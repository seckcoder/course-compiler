#lang racket
(require racket/set)
(require "utilities.rkt")
(require "int_exp.rkt")
(require "interp.rkt")
(require "priority_queue.rkt")

(provide reg-int-exp-passes)

(define caller-save (set 'rdx 'rcx 'rsi 'rdi 'r8 'r9 'r12))

(define general-registers (vector 'rbx 'rcx 'rdx 'rsi 'rdi
				  'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))
(define registers (set-union (list->set (vector->list general-registers))
			     (set 'rax 'rsp 'rbp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Liveness Analysis
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; record live-after for each instruction

(define free-vars
  (lambda (a)
    (match a
       [`(var ,x) (set x)]
       [else (set)])))

(define read-vars
  (lambda (instr)
    (match instr
       [`(mov ,s ,d) (free-vars s)]
       [(or `(add ,s ,d) `(sub ,s ,d)) 
	(set-union (free-vars s) (free-vars d))]
       [`(neg ,d) (free-vars d)]
       [`(call ,f) (set)]
       )))

(define write-vars
  (lambda (instr)
    (match instr
       [`(mov ,s ,d) (free-vars d)]
       [(or `(add ,s ,d) `(sub ,s ,d)) (free-vars d)]
       [`(neg ,d) (free-vars d)]
       [`(call ,f) caller-save]
       )))

(define (liveness-analysis ast)
  (match ast
     [`(program ,xs ,orig-ss)
      (let loop ([ss (reverse orig-ss)] [live-after (set)] [lives '()])
	(cond [(null? ss)
	       `(program (,xs ,lives) ,orig-ss)]
	      [else
	       (let* ([s (car ss)]
		      [live-before (set-union (set-subtract live-after
							    (write-vars s))
					      (read-vars s))])
		 (debug "after" s) (debug "live" live-after)
		 (loop (cdr ss)
		       live-before
		       (cons live-after lives)))]))]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Build Interference Graph
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (build-interference ast)
  (match ast
    [`(program (,xs ,lives) ,ss)
     (let ([graph (make-graph xs)])
       (let loop ([ss-lv (reverse (map cons ss lives))] [ss '()])
	 (cond [(null? ss-lv)
		`(program (,xs ,graph) ,ss)]
	       [else
		(match (car ss-lv)
		   [`((mov ,s ,d) . ,live-after)
		    ;; d interferes with everything in live-after
		    ;;   except s and d
		    (for ([v live-after])
			 (for ([d (write-vars `(mov ,s ,d))]
			       #:when (not (or (eq? v s) (eq? v d))))
			      (add-edge graph d v)))
		    (loop (cdr ss-lv) 
			  (cons `(mov ,s ,d) ss))]
		   [`(,inst . ,live-after)
		    (for ([v live-after])
			 (for ([d (write-vars inst)]
			       #:when (not (eq? v d)))
			      (add-edge graph d v)))
		    (loop (cdr ss-lv)
			  (cons inst ss))]
		   [`((call ,f) . ,live-after)
		    ;; add interference with caller-save registers
		    (for ([v live-after])
			 (for ([u caller-save]
			       #:when (not (eq? v u)))
			      (add-edge graph u v)))
		    ;; do the usual
		    (let ([inst `(call ,f)])
		      (for ([v live-after])
			   (for ([d (write-vars inst)]
				 #:when (not (eq? v d)))
				(add-edge graph d v)))
		      (loop (cdr ss-lv)
			    (cons inst ss)))]
		   )])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Allocate Registers and Stack Locations (Graph Coloring) 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
		       
(define (allocate-registers ast)
  (match ast
     [`(program (,xs ,G) ,ss)
      (let* ([unavail-colors (make-hash)] ;; aka. pencil marks
	     [compare (lambda (u v) 
			(>=
			 (set-count (hash-ref unavail-colors u))
			 (set-count (hash-ref unavail-colors v))))]
	     [Q (make-pqueue compare)]
	     [pq-node (make-hash)] ;; maps variables to priority queue nodes
	     [color (make-hash)])  ;; maps variables to colors (natural numbers)
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
					    (set-add (hash-ref unavail-colors u)
						     c))
				 (pqueue-decrease-key! Q (hash-ref pq-node u))])
			  )
		     (loop)))]))
	(debug "finished graph coloring" '())
	;; Create mapping from variables to their homes
	(let ([homes
	       (make-hash
		(map (lambda (x) (cons x (identify-home (hash-ref color x))))
		     xs))]
	      [stack-size (cond [(< largest-color 
				    (vector-length general-registers))
				 first-offset]
				[else
				 (- largest-color
				    (vector-length general-registers))])])
	(debug "assigning homes" '())
	  `(program ,stack-size
		    ,(map ((fix assign-locations) homes) ss))))]))
	  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reg-int-exp-passes
  (list `("uniquify" ,(lambda (ast) (((fix uniquify) '())
				     `(program () ,ast)))
	  ,((fix interp-S0) '()))
	`("flatten" ,((fix flatten) #f)
	  ,((fix interp-C0) '()))
	`("instruction selection" ,(fix instruction-selection)
	  ,((fix interp-x86) '()))
	`("liveness analysis" ,liveness-analysis
	  ,((fix interp-x86) '()))
	`("build interference" ,build-interference
	  ,((fix interp-x86) '()))
	`("allocate registers" ,allocate-registers
	  ,((fix interp-x86) '()))
	`("insert spill code" ,(fix insert-spill-code)
	  ,((fix interp-x86) '()))
	`("print x86" ,(fix print-x86) #f)
	))

