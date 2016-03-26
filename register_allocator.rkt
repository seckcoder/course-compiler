#lang racket
(require racket/set)
(require "utilities.rkt")
(require "int_exp.rkt")
(require "interp.rkt")
(require "priority_queue.rkt")

(provide reg-int-exp-passes compile-reg-R0)

(define use-move-biasing #f)

(define compile-reg-R0
  (class compile-R0
    (super-new)

    (inherit assign-homes)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*
    ;; *annotated program with live-after information for each stmt

    (define/public (free-vars a)
      (match a
	 [`(var ,x) (set x)]
	 [`(reg ,r) (set r)]
	 [`(deref ,r ,i) (set r)]
	 [`(int ,n) (set)]
	 [else (error "free-vars, unhandled" a)]))

    (define/public (read-vars instr)
      (match instr
         [`(movq ,s ,d) (free-vars s)]
	 [(or `(addq ,s ,d) `(subq ,s ,d) `(imulq ,s ,d)) 
	  (set-union (free-vars s) (free-vars d))]
	 [`(negq ,d) (free-vars d)]
	 [`(callq ,f) (set)]
	 [else (error "read-vars unmatched" instr)]
	 ))
  
    (define/public (write-vars instr)
      (match instr
         [`(movq ,s ,d) (free-vars d)]
	 [(or `(addq ,s ,d) `(subq ,s ,d) `(imulq ,s ,d)) 
	  (free-vars d)]
	 [`(negq ,d) (free-vars d)]
	 [`(callq ,f) caller-save]
	 [else (error "write-vars unmatched" instr)]
	 ))

    (define/public (liveness-ss orig-live-after)
      (lambda (orig-ss)
	(let loop ([ss (reverse orig-ss)] [live-after orig-live-after] 
		   [lives (list orig-live-after)] [new-ss '()])
	  (cond [(null? ss) (values new-ss lives)]
		[else
		 (define-values (new-s new-live-after)
		   ((uncover-live live-after) (car ss)))
		 (loop (cdr ss) new-live-after (cons new-live-after lives)
		       (cons new-s new-ss))]))))

    (define/public (uncover-live live-after)
      (lambda (ast)
	(match ast
          [`(program ,xs (type ,ty) ,ss ...)
	    (define-values (new-ss lives) ((liveness-ss (set)) ss))
	    (assert "lives ss size" (= (length (cdr lives)) (length new-ss)))
	    `(program (,xs ,(cdr lives)) (type ,ty) ,@new-ss)]
          [`(program ,xs ,ss ...)
	    (define-values (new-ss lives) ((liveness-ss (set)) ss))
	    (assert "lives ss size" (= (length (cdr lives)) (length new-ss)))
	    `(program (,xs ,(cdr lives)) ,@new-ss)]
	   [else
	    (values ast (set-union (set-subtract live-after 
						 (write-vars ast))
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
		 (for ([d (free-vars d)]
		       #:when (not (or (equal? `(var ,v) s) (equal? v d))))
		      (add-edge G d v)))
	    ast]
	   [`(callq ,f)
	    (for ([v live-after])
		 (for ([u caller-save]
		       #:when (not (equal? v u)))
		      (add-edge G u v)))
	    ast]
           [`(program (,xs ,lives) (type ,ty) ,ss ...)
	    (define G (make-graph xs))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((build-interference live-after G) inst)))
	    (print-dot G "./interfere.dot")
	    `(program (,xs ,G) (type ,ty) ,@new-ss)]
           [`(program (,xs ,lives) ,ss ...)
	    (define G (make-graph xs))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((build-interference live-after G) inst)))
	    (print-dot G "./interfere.dot")
	    `(program (,xs ,G) ,@new-ss)]
	   [else
	    (for ([v live-after])
		 (for ([d (write-vars ast)] #:when (not (equal? v d)))
		      (add-edge G d v)))
	    ast])))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-move-graph : pseudo-x86* -> pseudo-x86*
    ;; *annotate program with move graph

    (define/public (build-move-graph G)
      (lambda (ast)
	(match ast
	   [`(movq (var ,s) (var ,d))
            (if use-move-biasing
                (add-edge G s d)
                '())
	    ast]
           [`(program (,xs ,IG) (type ,ty) ,ss ...)
            (define MG (make-graph xs))
            (define new-ss
              (if use-move-biasing
                  (let ([nss 
                         (for/list ([inst ss])
                           ((build-move-graph MG) inst))])
                    (print-dot MG "./move.dot")
                    nss)
                  ss))
            `(program (,xs ,IG ,MG) (type ,ty) ,@new-ss)]
           [`(program (,xs ,IG) ,ss ...)
            (define MG (make-graph xs))
            (define new-ss
              (if use-move-biasing
                  (let ([nss 
                         (for/list ([inst ss])
                           ((build-move-graph MG) inst))])
                    (print-dot MG "./move.dot")
                    nss)
                  ss))
            `(program (,xs ,IG ,MG) ,@new-ss)]

	   [else ast])))
	    

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86
    ;; Replaces variables with registers and stack locations
    ;; using graph coloring based on Suduko heuristics.
    ;; This pass encompasses assign-homes.

    (define largest-color 0)

    ;; Choose the first available color
    ;; To do: move biasing -Jeremy
    (define (choose-color v unavail-colors move-related)
      (define n (vector-length registers-for-alloc))
      (define biased-selection
        (for/first ([c move-related]
                    #:when (not (set-member? unavail-colors c)))
          c))
      (if (or (eq? biased-selection #f) (>= biased-selection n))
          (let ([unbiased-selection     
                 (let loop ([c 0])
                   (cond [(set-member? unavail-colors c) 
                          (loop (add1 c))]
                         [else c]))])
            (if (or (eq? biased-selection #f) (< unbiased-selection n)) unbiased-selection
                biased-selection))
          biased-selection))

    (inherit variable-size first-offset)

    (define (identify-home c)
      (define n (vector-length registers-for-alloc))
      (cond
        [(< c n)
         `(reg ,(vector-ref registers-for-alloc c))]
        [else 
         `(deref rbp ,(- (+ (first-offset) (* (- c n) (variable-size)))))]))

    (define/public (allocate-homes IG MG xs ss)
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
		      (set->list (adjacent IG x))))
	   (define adj-colors
	     (list->set (map (lambda (r) (register->color r)) adj-reg)))
	   (hash-set! unavail-colors x adj-colors)
	   ;; add variables to priority queue
	   (hash-set! pq-node x (pqueue-push! Q x)))
      ;; Graph coloring
      (while (> (pqueue-count Q) 0)
	     (define v (pqueue-pop! Q))
             (define move-related 
               (list->set (filter (lambda (x) (>= x 0)) 
                                  (map (lambda (k) (hash-ref color k -1)) 
                                       (set->list (adjacent MG v))))))
	     (define c (choose-color v (hash-ref unavail-colors v) move-related))
	     (cond [(> c largest-color) (set! largest-color c)])
	     (hash-set! color v c)
	     (debug "coloring" (cons v c))
	     (for ([u (adjacent IG v)])
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
      (define spill-space (* num-spills (variable-size)))
      (values homes spill-space)
      )
    (define/public (allocate-registers)
      (lambda (ast)
	(match ast
           [`(program (,locals ,IG ,MG) (type ,ty) ,ss ...)
	    (define-values (homes stk-size) 
	      (allocate-homes IG MG locals ss))
	    `(program ,stk-size (type ,ty)
		      ,@(map (assign-homes homes) ss))]
           [`(program (,locals ,IG ,MG) ,ss ...)
	    (define-values (homes stk-size) 
	      (allocate-homes IG MG locals ss))
	    `(program ,stk-size 
		      ,@(map (assign-homes homes) ss))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(program ,spill-space ,ss ...)
	    (define callee-reg (set->list callee-save))
	    (define save-callee-reg
	      (for/list ([r callee-reg])
			(format "\tpushq\t%~a\n" r)))
	    (define restore-callee-reg
	      (for/list ([r (reverse callee-reg)])
			(format "\tpopq\t%~a\n" r)))
	    (define callee-space (* (length (set->list callee-save))
				    (variable-size)))
	    (define stack-adj (- (align (+ callee-space spill-space) 16)
				  callee-space))
	    (string-append
	     (format "\t.globl ~a\n" (label-name "main"))
	     (format "~a:\n" (label-name "main"))
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (string-append* save-callee-reg)
	     (format "\tsubq\t$~a, %rsp\n" stack-adj)
	     "\n"
	     (string-append* (map (print-x86) ss))
	     "\n"
             (format "\tmovq\t%rax, %rdi\n")
             (format "\tcallq\t~a\n" (label-name "print_int"))
	     (format "\tmovq\t$0, %rax\n")
	     (format "\taddq\t$~a, %rsp\n" stack-adj)
	     (string-append* restore-callee-reg)
	     (format "\tpopq\t%rbp\n")
	     (format "\tretq\n"))]
	   [else
	    ((super print-x86) e)]
	   )))

    )) ;; compile-reg-R0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define reg-int-exp-passes
  (let ([compiler (new compile-reg-R0)]
	[interp (new interp-R0)])
    `(#|
      ("programify" ,(lambda (ast) `(program () ,ast))
      ,(send interp interp-scheme '()))
      |#
      ("uniquify" ,(send compiler uniquify '()) ,(send interp
                                                       interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler
                                   build-interference (void) (void))
       ,(send interp interp-x86 '()))
      ("build move graph" ,(send compiler
                                 build-move-graph (void))
       ,(send interp interp-x86 '()))
      ("allocate registers" ,(send compiler allocate-registers)
       ,(send interp interp-x86 '()))
      ("insert spill code" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ("print x86" ,(send compiler print-x86) #f)
      )))

