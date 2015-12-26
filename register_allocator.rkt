#lang racket
(require racket/set)
(require "utilities.rkt")
(require "int_exp.rkt")
(require "interp.rkt")
(require "priority_queue.rkt")

(provide reg-int-exp-passes compile-reg-S0)

(define compile-reg-S0
  (class compile-S0
    (super-new)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*
    ;; *annotated program with live-after information for each stmt

    (define/public (free-vars a)
      (match a
	 [`(var ,x) (set x)]
	 [`(reg ,r) (set r)] ;; experimental -Jeremy
	 [`(stack-loc ,i) (set)]
	 [`(int ,n) (set)]
	 [else (error "free-vars, unhandled" a)]))

    (define/public (read-vars instr)
      (match instr
         [`(movq ,s ,d) (send this free-vars s)]
	 [(or `(addq ,s ,d) `(subq ,s ,d) `(imulq ,s ,d)) 
	  (set-union (send this free-vars s) (send this free-vars d))]
	 [`(negq ,d) (send this free-vars d)]
	 [`(call ,f) (set)]
	 [else (error "read-vars unmatched" instr)]
	 ))
  
    (define/public (write-vars instr)
      (match instr
         [`(movq ,s ,d) (send this free-vars d)]
	 [(or `(addq ,s ,d) `(subq ,s ,d) `(imulq ,s ,d)) 
	  (send this free-vars d)]
	 [`(negq ,d) (send this free-vars d)]
	 [`(call ,f) caller-save]
	 [else (error "write-vars unmatched" instr)]
	 ))

    (define/public (liveness-ss orig-live-after)
      (lambda (orig-ss)
	(let loop ([ss (reverse orig-ss)] [live-after orig-live-after] 
		   [lives (list orig-live-after)] [new-ss '()])
	  (cond [(null? ss) (values new-ss (cdr lives))]
		[else
		 (define-values (new-s new-live-after)
		   ((send this uncover-live live-after) (car ss)))
		 (loop (cdr ss) new-live-after (cons new-live-after lives)
		       (cons new-s new-ss))]))))

    (define/public (uncover-live live-after)
      (lambda (ast)
	(match ast
           [`(program ,xs ,ss ...)
	    (define-values (new-ss lives) ((send this liveness-ss (set)) ss))
	    (assert "lives ss size" (= (length lives) (length new-ss)))
	    `(program (,xs ,lives) ,@new-ss)]
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
	   [`(movq ,s ,d)
	    (for ([v live-after])
		 (for ([d (write-vars `(movq ,s ,d))]
		       #:when (not (or (equal? v s) (equal? v d))))
		      (add-edge G d v)))
	    ast]
	   [`(call ,f)
	    (for ([v live-after])
		 (for ([u caller-save]
		       #:when (not (equal? v u)))
		      (add-edge G u v)))
	    ast]
           [`(program (,xs ,lives) ,ss ...)
	    (define G (make-graph xs))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((send this build-interference live-after G) inst)))
	    `(program (,xs ,G) ,@new-ss)]
	   [else
	    (for ([v live-after])
		 (for ([d (write-vars ast)] #:when (not (equal? v d)))
		      (add-edge G d v)))
	    ast])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86
    ;; Replaces variables with registers and stack locations
    ;; using graph coloring based on Soduko heuristics.
    ;; This pass encompasses assign-locations.

    (define largest-color 0)

    ;; Choose the first available color
    ;; To do: move biasing -Jeremy
    (define (choose-color v unavail-colors)
      (let loop ([c 0])
	(cond [(set-member? unavail-colors c) 
	       (loop (add1 c))]
	      [else c])))

    (define variable-size 8)
    (define first-offset 8)

    (define (identify-home c)
      (define n (vector-length registers-for-alloc))
      (cond [(< c n)
	     `(reg ,(vector-ref registers-for-alloc c))]
	    [else 
	     `(stack-loc ,(+ first-offset (* (- c n) variable-size)))]))

    (define/public (allocate-homes G xs ss)
      (debug "allocate-homes" xs)
      (set! largest-color 0)
      (define unavail-colors (make-hash)) ;; pencil marks
      (define (compare u v) 
	(>= (set-count (hash-ref unavail-colors u))
	    (set-count (hash-ref unavail-colors v))))
      (define Q (make-pqueue compare))
      (define pq-node (make-hash)) ;; maps vars to priority queue nodes
      (define color (make-hash)) ;; maps vars to colors (natural nums)
      (for ([x xs])
	   ;; mark neighboring register colors as unavailable
	   (define adj-reg
	      (filter (lambda (u) (set-member? registers u))
		      (set->list (hash-ref G x))))
	   (define adj-colors
	     (list->set (map (lambda (r) (register->color r)) adj-reg)))
	   (hash-set! unavail-colors x adj-colors)
	   ;; add variables to priority queue
	   (hash-set! pq-node x (pqueue-push! Q x)))
      ;; Graph coloring
      (while (> (pqueue-count Q) 0)
	     (define v (pqueue-pop! Q))
	     (define c (choose-color v (hash-ref unavail-colors v)))
	     (cond [(> c largest-color) (set! largest-color c)])
	     (hash-set! color v c)
	     (debug "coloring" (cons v c))
	     (for ([u (adjacent G v)])
		  (when (not (set-member? registers u))
			(hash-set! unavail-colors u
				   (set-add (hash-ref unavail-colors u) c))
			(pqueue-decrease-key! Q (hash-ref pq-node u)))))
      ;; Create mapping from variables to their homes
      (define homes
	(make-hash (for/list ([x xs])
			     (cons x (identify-home (hash-ref color x))))))
      (define num-spills 
	(max 0 (- (add1 largest-color) (vector-length registers-for-alloc))))
      (define stack-size
	(+ (send this first-offset)
	   (align (* num-spills (send this variable-size)) 16)))
      ;;(printf "stack size: ~a" stack-size)(newline)
      ;;(printf "aligned stack size: ~a" (align stack-size 16))(newline)
      (values homes (align stack-size 16)))

    (define/public (allocate-registers)
      (lambda (ast)
	(match ast
           [`(program (,locals ,G) ,ss ...)
	    (define-values (homes stk-size) 
	      (send this allocate-homes G locals ss))
	    `(program ,stk-size 
		      ,@(map (send this assign-locations homes) ss))]
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

