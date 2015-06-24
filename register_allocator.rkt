#lang racket
(require racket/set)
(require "utilities.rkt")
(require "int_exp.rkt")
(require "interp.rkt")
(require "priority_queue.rkt")

(provide reg-int-exp-passes compile-reg-S0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Graph ADT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (make-graph vertices)
  (make-hash (map (lambda (v) (cons v (set))) vertices)))

(define (add-edge graph u v)
  (hash-set! graph u (set-add (hash-ref graph u (set)) v))
  (hash-set! graph v (set-add (hash-ref graph v (set)) u)))

(define (adjacent graph u)
  (hash-ref graph u))


(define compile-reg-S0
  (class compile-S0
    (super-new)

    (define caller-save (set 'rdx 'rcx 'rsi 'rdi 'r8 'r9 'r12))

    (define general-registers (vector 'rbx 'rcx 'rdx 'rsi 'rdi
    				  'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))
    (define registers (set-union (list->set (vector->list general-registers))
				 (set 'rax 'rsp 'rbp)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Liveness Analysis
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;; record live-after for each instruction

    (define/public (free-vars a)
      (match a
	 [`(var ,x) (set x)]
	 [else (set)]))

    (define/public (read-vars instr)
      (match instr
         [`(mov ,s ,d) (send this free-vars s)]
	 [(or `(add ,s ,d) `(sub ,s ,d)) 
	  (set-union (send this free-vars s) (send this free-vars d))]
	 [`(neg ,d) (send this free-vars d)]
	 [`(call ,f) (set)]
	 ))
  
    (define/public (write-vars instr)
      (match instr
         [`(mov ,s ,d) (send this free-vars d)]
	 [(or `(add ,s ,d) `(sub ,s ,d)) (send this free-vars d)]
	 [`(neg ,d) (send this free-vars d)]
	 [`(call ,f) caller-save]
	 ))

    (define/public (liveness-ss live-after)
      (lambda (orig-ss)
	(let loop ([ss (reverse orig-ss)] [live-after live-after] 
		   [lives '()] [new-ss '()])
	      (cond [(null? ss)
		     (values new-ss lives)]
		    [else
		     (let-values ([(new-s live-after)
				   ((send this liveness-analysis live-after)
				    (car ss))])
		       (loop (cdr ss)
			     live-after
			     (cons live-after lives)
			     (cons new-s new-ss)))]))))

    (define/public (liveness-analysis live-after)
      (lambda (ast)
	(match ast
           [`(program ,xs ,ss)
	    (let-values ([(new-ss lives) ((send this liveness-ss (set)) ss)])
	      `(program (,xs ,lives) ,new-ss))]
	   [else
	    (values ast
		    (set-union (set-subtract live-after (write-vars ast))
			       (read-vars ast)))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Build Interference Graph
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (build-interference live-after G)
      (lambda (ast)
	(match ast
	   [`(mov ,s ,d)
	    ;; d interferes with everything in live-after
	    ;;   except s and d
	    (for ([v live-after])
		 (for ([d (write-vars `(mov ,s ,d))]
		       #:when (not (or (eq? v s) (eq? v d))))
		      (add-edge G d v)))]
	   [`(call ,f)
	    ;; add interference with caller-save registers
	    (for ([v live-after])
		 (for ([u caller-save]
		       #:when (not (eq? v u)))
		      (add-edge G u v)))
	    ;; do the usual (not sure this is needed)
	    (let ([inst `(call ,f)])
	      (for ([v live-after])
		   (for ([d (write-vars inst)]
			 #:when (not (eq? v d)))
			(add-edge G d v))))]
           [`(program (,xs ,lives) ,ss)
	    (let ([G (make-graph xs)])
	      (let ([ss-lv (reverse (map cons ss lives))])
		(for ([s-lv ss-lv]) 
		     (match s-lv
			[`(,inst . ,live-after)
			 ((send this build-interference live-after G) inst)]))
		`(program (,xs ,G) ,ss)))]
	   [else
	    (for ([v live-after])
		 (for ([d (write-vars ast)] #:when (not (eq? v d)))
		      (add-edge G d v)))])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Allocate Registers and Stack Locations (Graph Coloring) 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define largest-color 0)

    ;; Choose the first available color
    (define (choose-color v unavail-colors)
      (let loop ([c 0])
	(cond [(set-member? unavail-colors c)
	       (loop (add1 c))]
	      [else
	       (cond [(> c largest-color)
		      (set! largest-color c)])
	       c])))

    (define variable-size 8)
    (define first-offset 16)

    (define (identify-home c)
      (let ([n (vector-length general-registers)])
	(cond [(< c n)
	       `(register ,(vector-ref general-registers c))]
	      [else 
	       `(stack-loc ,(+ first-offset (* (- c n) variable-size)))])))

    (define/public (allocate-registers)
      (lambda (ast)
	(match ast
           [`(program (,xs ,G) ,ss)
	    (let* ([unavail-colors (make-hash)] ;; aka. pencil marks
		   [compare (lambda (u v) 
			      (>=
			       (set-count (hash-ref unavail-colors u))
			       (set-count (hash-ref unavail-colors v))))]
		   [Q (make-pqueue compare)]
		   [pq-node (make-hash)] ;; maps vars to priority queue nodes
		   [color (make-hash)])  ;; maps vars to colors (natural numbers)
	      (for ([x xs])
		   (hash-set! unavail-colors x 
			      (list->set
			       (filter
				(lambda (u) (set-member? registers u))
				(set->list (hash-ref G x)))))
		   (hash-set! pq-node x (pqueue-push! Q x)))
	      ;; Graph coloring
	      (debug "starting graph coloring" '())
	      (let loop ()
		(cond [(> (pqueue-count Q) 0)
		       (let ([v (pqueue-pop! Q)])
			 (debug "coloring" v)
			 (let ([c (choose-color v (hash-ref unavail-colors v))])
			   (debug "found color" c)
			   (hash-set! color v c)
			   (for ([u (adjacent G v)])
				(debug "adjacent" u)
				(cond [(not (set-member? registers u))
				       (debug "not a register" u)
				       (hash-set! unavail-colors u
						  (set-add
						   (hash-ref unavail-colors u)
						   c))
				       (pqueue-decrease-key! 
					Q
					(hash-ref pq-node u))])
				)
			   (loop)))]))
	      (debug "finished graph coloring" '())
	      ;; Create mapping from variables to their homes
	      (let ([homes
		     (make-hash
		      (map (lambda (x) (cons x (identify-home
						(hash-ref color x))))
			   xs))]
		    [stack-size (cond [(< largest-color 
					  (vector-length general-registers))
				       first-offset]
				      [else
				       (- largest-color
					  (vector-length general-registers))])])
		(debug "assigning homes" '())
		`(program ,stack-size
			  ,(map (send this assign-locations homes) ss))))])))
      
    )) ;; compile-reg-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reg-int-exp-passes
  (let ([compiler (new compile-reg-S0)])
    (list `("uniquify" ,(lambda (ast) ((send compiler uniquify '())
				       `(program () ,ast)))
	    ,((fix interp-S0) '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,((fix interp-C0) '()))
	  `("instruction selection" ,(send compiler instruction-selection)
	    ,((fix interp-x86) '()))
	  `("liveness analysis" ,(send compiler liveness-analysis (void))
	    ,((fix interp-x86) '()))
	  `("build interference" ,(send compiler
					build-interference (void) (void))
	    ,((fix interp-x86) '()))
	  `("allocate registers" ,(send compiler allocate-registers)
	    ,((fix interp-x86) '()))
	  `("insert spill code" ,(send compiler insert-spill-code)
	    ,((fix interp-x86) '()))
	  `("print x86" ,(send compiler print-x86) #f)
	  )))

