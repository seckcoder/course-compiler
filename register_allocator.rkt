#lang racket
(require racket/set)
(require "utilities.rkt")
(require "int_exp.rkt")
(require "interp.rkt")
(require "priority_queue.rkt")

(provide reg-int-exp-passes compile-reg-S0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Graph ADT

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
				 (set 'rax 'rsp 'rbp '__flag)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*
    ;; *annotated program with live-after information for each stmt

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
	 [else (error "read-vars unmatched" instr)]
	 ))
  
    (define/public (write-vars instr)
      (match instr
         [`(mov ,s ,d) (send this free-vars d)]
	 [(or `(add ,s ,d) `(sub ,s ,d)) (send this free-vars d)]
	 [`(neg ,d) (send this free-vars d)]
	 [`(call ,f) caller-save]
	 [else (error "write-vars unmatched" instr)]
	 ))

    (define/public (liveness-ss orig-live-after)
      (lambda (orig-ss)
	(let loop ([ss (reverse orig-ss)] [live-after orig-live-after] 
		   [lives '()] [new-ss '()])
	  (cond [(null? ss) (values new-ss lives)]
		[else
		 (define-values (new-s new-live-after)
		   ((send this uncover-live live-after) (car ss)))
		 (loop (cdr ss) new-live-after (cons new-live-after lives)
		       (cons new-s new-ss))]))))

    (define/public (uncover-live live-after)
      (lambda (ast)
	(match ast
           [`(program ,xs ,ss)
	    (define-values (new-ss lives) ((send this liveness-ss (set)) ss))
	    `(program (,xs ,lives) ,new-ss)]
	   [else
	    (values ast (set-union (set-subtract live-after (write-vars ast))
				   (read-vars ast)))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph

    (define/public (build-interference live-after G)
      (lambda (ast)
	(match ast
	   [`(mov ,s ,d)
	    (for ([v live-after])
		 (for ([d (write-vars `(mov ,s ,d))]
		       #:when (not (or (eq? v s) (eq? v d))))
		      (add-edge G d v)))
	    ast]
	   [`(call ,f)
	    (for ([v live-after])
		 (for ([u caller-save]
		       #:when (not (eq? v u)))
		      (add-edge G u v)))
	    ast]
           [`(program (,xs ,lives) ,ss)
	    (define G (make-graph xs))
	    (define new-ss '())
	    (for ([inst ss] [live-after lives])
		 (define new-inst ((send this build-interference 
					 live-after G) inst))
		 (set! new-ss (cons new-inst new-ss)))
	    `(program (,xs ,G) ,(reverse new-ss))]
	   [else
	    (for ([v live-after])
		 (for ([d (write-vars ast)] #:when (not (eq? v d)))
		      (add-edge G d v)))
	    ast])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86
    ;; Replaces variables with registers and stack locations
    ;; using graph coloring based on Soduko heuristics.
    ;; This pass encompasses assign-locations.

    (define largest-color 0)

    ;; Choose the first available color
    (define (choose-color v unavail-colors)
      (let loop ([c 0])
	(cond [(set-member? unavail-colors c) (loop (add1 c))]
	      [else
	       (cond [(> c largest-color) (set! largest-color c)])
	       c])))

    (define variable-size 8)
    (define first-offset 16)

    (define (identify-home c)
      (define n (vector-length general-registers))
      (cond [(< c n)
	     `(register ,(vector-ref general-registers c))]
	    [else 
	     `(stack-loc ,(+ first-offset (* (- c n) variable-size)))]))

    (define/public (allocate-registers)
      (lambda (ast)
	(match ast
           [`(program (,xs ,G) ,ss)
	    (define unavail-colors (make-hash)) ;; pencil marks
	    (define (compare u v) 
	      (>= (set-count (hash-ref unavail-colors u))
		  (set-count (hash-ref unavail-colors v))))
	    (define Q (make-pqueue compare))
	    (define pq-node (make-hash)) ;; maps vars to priority queue nodes
	    (define color (make-hash)) ;; maps vars to colors (natural nums)
	    (for ([x xs])
		 ;; mark neighboring registers as unavailable
		 (hash-set! unavail-colors x 
			    (list->set
			     (filter (lambda (u) (set-member? registers u))
				     (set->list (hash-ref G x)))))
		 ;; add variables to priority queue
		 (hash-set! pq-node x (pqueue-push! Q x)))
	    ;; Graph coloring
	    (while (> (pqueue-count Q) 0)
	       (define v (pqueue-pop! Q))
	       (define c (choose-color v (hash-ref unavail-colors v)))
	       (hash-set! color v c)
	       (for ([u (adjacent G v)])
		    (when (not (set-member? registers u))
		       (hash-set! unavail-colors u
				  (set-add (hash-ref unavail-colors u) c))
		       (pqueue-decrease-key! Q (hash-ref pq-node u)))))
	      ;; Create mapping from variables to their homes
	    (define homes
	      (make-hash (for/list ([x xs])
			    (cons x (identify-home (hash-ref color x))))))
	    (define stack-size
	      (cond [(< largest-color (vector-length general-registers))
		     first-offset]
		    [else (- largest-color (vector-length general-registers))]))
	    `(program ,stack-size ,(map (send this assign-locations homes) ss))]
	   )))

    )) ;; compile-reg-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define reg-int-exp-passes
  (let ([compiler (new compile-reg-S0)]
	[interp (new interp-S0)])
    (list `("programify" ,(lambda (ast) `(program () ,ast))
	    ,(send interp interp-scheme '()))
	  `("uniquify" ,(send compiler uniquify '())
	    ,(send interp interp-scheme '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,(send interp interp-C '()))
	  `("instruction selection" ,(send compiler select-instructions)
	    ,(send interp interp-x86 '()))
	  `("liveness analysis" ,(send compiler uncover-live (void))
	    ,(send interp interp-x86 '()))
	  `("build interference" ,(send compiler
					build-interference (void) (void))
	    ,(send interp interp-x86 '()))
	  `("allocate registers" ,(send compiler allocate-registers)
	    ,(send interp interp-x86 '()))
	  `("insert spill code" ,(send compiler insert-spill-code)
	    ,(send interp interp-x86 '()))
	  `("print x86" ,(send compiler print-x86) #f)
	  )))

