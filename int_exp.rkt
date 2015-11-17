#lang racket
(require racket/set racket/stream)
(require "utilities.rkt")
(require "interp.rkt")

(provide int-exp-passes compile-S0)

(define compile-S0
  (class object%
    (super-new)

    (define/public (primitives)
      (set '+ '- '* 'read))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S0 -> S0
    (define/public (uniquify env)
      (lambda (e)
	(match e
	   [(? symbol?) (cdr (assq e env))]
	   [(? integer?) e]
	   [`(let ([,x ,e]) ,body)
	    (define new-x (gensym x))
	    (define new-e ((send this uniquify env) e))
	    `(let ([,new-x ,new-e])
	       ,((send this uniquify (cons (cons x new-x) env)) body))]
	   [`(program ,extra ,body)
	    `(program ,extra ,((send this uniquify env) body))]
	   [`(,op ,es ...) #:when (set-member? (send this primitives) op)
	    `(,op ,@(map (send this uniquify env) es))]
	   [else (error "uniquify couldn't match" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : Bool -> S0 -> C0-expr x (C0-stmt list)
    (define/public (collect-locals)
      (lambda (ast)
	(match ast
	   [`(assign ,x ,e) (list x)]
	   [`(return ,e) '()]
	   [else
	    (error "unmatched in collect-locals S0" ast)]
	   )))

    (define/public (flatten need-atomic)
      (lambda (e)
        (match e
           [(? symbol?) (values e '())]
	   [(? integer?) (values e '())]
	   [`(let ([,x ,e]) ,body)
	    (define-values (new-e e-ss) ((send this flatten #f) e))
	    (define-values (new-body body-ss) ((send this flatten #f) body))
	    (values new-body (append e-ss `((assign ,x ,new-e)) body-ss))]
	   [`(,op ,es ...) #:when (set-member? (send this primitives) op)
	    (define-values (new-es sss) (map2 (send this flatten #t) es))
	    (define ss (append* sss))
	    (define prim-apply `(,op ,@new-es))
	    (cond [need-atomic
		   (define tmp (gensym 'tmp))
		   (values tmp (append ss `((assign ,tmp ,prim-apply))))]
		  [else (values prim-apply ss)])]
	   [`(program ,extra ,e)
	    (define-values (new-e ss) ((send this flatten #f) e))
	    (define xs (append* (map (send this collect-locals) ss)))
	    `(program ,(remove-duplicates xs) ,@(append ss `((return ,new-e))))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : C0 -> psuedo-x86

    (define/public (binary-op->inst op)
      (match op
         ['+ 'add] ['- 'sub] ['* 'imul]
	 [else (error "in binary-op->inst unmatched" op)]
	 ))

    (define/public (unary-op->inst op)
      (match op
	 ['- 'neg] [else (error "in unary-op->inst unmatched" op)]
	 ))

    (define/public (commutative? op)
      (match op
         ['+ #t] ['* #t] 
         [else #f]))

    (define/public (select-instructions)
      (lambda (e)
	(match e
           [(? symbol?) `(var ,e)]
	   [(? integer?) `(int ,e)]
	   [`(register ,r) `(register ,r)]
	   [`(return ,e)
	    ((send this select-instructions) `(assign (register rax) ,e))]
	   [`(assign ,lhs (read))
	    (define new-lhs ((send this select-instructions) lhs))
	    `((call _read_int) (mov (register rax) ,new-lhs))]
	   [`(assign ,lhs ,x) #:when (symbol? x)
	    (define new-lhs ((send this select-instructions) lhs))
	    (cond [(equal? `(var ,x) new-lhs) '()]
		  [else `((mov (var ,x) ,new-lhs))])]
	   [`(assign ,lhs ,n) #:when (integer? n)
	    (define new-lhs ((send this select-instructions) lhs))
	    `((mov (int ,n) ,new-lhs))]
	   [`(assign ,lhs (,op ,e1 ,e2))
	    (define new-lhs ((send this select-instructions) lhs))
	    (define new-e1 ((send this select-instructions) e1))
	    (define new-e2 ((send this select-instructions) e2))
	    (define inst (binary-op->inst op))
	    (cond [(equal? new-e1 new-lhs)
		   `((,inst ,new-e2 ,new-lhs))]
		  [(equal? new-e2 new-lhs)
		   `((,inst ,new-e1 ,new-lhs))]
		  ;; The following can shorten the live range of e2. -JGS
		  [(and (send this commutative? op) 
			(integer? e1) (symbol? e2))
		   `((mov ,new-e2 ,new-lhs) (,inst ,new-e1 ,new-lhs))]
		  [else `((mov ,new-e1 ,new-lhs) (,inst ,new-e2 ,new-lhs))])]
	   [`(assign ,lhs (,op ,e1))	
	    (define new-lhs ((send this select-instructions) lhs))
	    (define new-e1 ((send this select-instructions) e1))
	    (define inst (unary-op->inst op))
	    (cond [(equal? new-e1 new-lhs)
		   `((,inst ,new-lhs))]
		  [else `((mov ,new-e1 ,new-lhs) (,inst ,new-lhs))])]
	   [`(program ,xs ,ss ...)
	    `(program ,xs ,@(append* (map (send this select-instructions) ss)))]
	   [else (error "instruction selection, unmatched " e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-locations : homes -> pseudo-x86 -> pseudo-x86
    ;;
    ;; Replace variables with stack locations. Later versions of this pass
    ;; will assign some variables to registers. 

    (define/public (variable-size) 8)
    (define/public (first-offset) 8)

    (define/public (instructions)
      (set 'add 'sub 'imul 'neg 'mov))

    (define/public (assign-locations homes)
      (lambda (e)
	(match e
	   [`(var ,x) (hash-ref homes x)]
	   [`(int ,n) `(int ,n)]
	   [`(register ,r) `(register ,r)]
	   [`(call ,f) `(call ,f)]
	   [`(program ,xs ,ss ...)
	    ;; create mapping of variables to stack locations
	    (define (make-stack-loc n)
	      `(stack-loc ,(+ (send this first-offset)
			      (* (send this variable-size) n))))
	    (define new-homes
	      (make-hash (map cons xs
			      (map make-stack-loc
				   (stream->list (in-range 0 (length xs)))))))
	    (define stack-space (align 
				 (* (length xs)
				    (send this variable-size))
				 16))
	    `(program ,stack-space
		      ,@(map (send this assign-locations new-homes) ss))]
	   [`(,instr-name ,as ...) 
	    #:when (set-member? (send this instructions) instr-name)
	    `(,instr-name ,@(map (send this assign-locations homes) as))]
	   [else (error "in assign-locations S0, unmatched" e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; insert-spill-code : psuedo-x86 -> x86
    ;; Uses register rax to patch things up

    (define/public (on-stack? a)
      (match a
         [`(stack-loc ,n) #t]
	 [else #f]))

    (define/public (insert-spill-code)
      (lambda (e)
	(match e
           [`(mov ,s ,d)
	    (cond [(equal? s d) '()] ;; trivial move, delete it
		  [(and (on-stack? s) (on-stack? d))
		   `((mov ,s (register rax))
		     (mov (register rax) ,d))]
		  [else `((mov ,s ,d))])]
	   [`(call ,f) `((call ,f))]
	   [`(program ,stack-space ,ss ...)
	    `(program ,stack-space 
		      ,@(append* (map (send this insert-spill-code) ss)))]
	   ;; for imulq, destination must be a register -Jeremy
	   [`(imul ,s (register ,d))
	    `((imul ,s (register ,d)))]
	   [`(imul ,s ,d)
	    `((mov ,d (register rax))
	      (imul ,s (register rax))
	      (mov (register rax) ,d))]
	   [`(,instr-name ,s ,d)
	    #:when (set-member? (send this instructions) instr-name)
	    (cond [(and (on-stack? s) (on-stack? d))	
		   (debug 'spill-code "spilling")
		   `((mov ,s (register rax)) (,instr-name (register rax) ,d))]
		  [else `((,instr-name ,s ,d))])]
	   [`(,instr-name ,d)
	    #:when (set-member? (send this instructions) instr-name)
	    `((,instr-name ,d))]
	   )))
  
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/public (print-x86)
      (lambda (e)
	(match e
           [`(stack-loc ,n) 
	    (format "~a(%rbp)" (- n))]
	   [`(int ,n) (format "$~a" n)]
	   [`(register ,r) (format "%~a" r)]
	   [`(call ,f) (format "\tcallq\t~a\n" f)]
	   [`(program ,stack-space ,ss ...)
	    (string-append
	     (format "\t.globl _main\n")
	     (format "_main:\n")
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (format "\tsubq\t$~a, %rsp\n" stack-space)
	     "\n"
	     (string-append* (map (send this print-x86) ss))
	     "\n"
	     (format "\taddq\t$~a, %rsp\n" stack-space)
	     (format "\tpopq\t%rbp\n")
	     (format "\tretq\n")
	     )]
	   [`(,instr-name ,s ,d)
	    #:when (set-member? (send this instructions) instr-name)
	    (format "\t~aq\t~a, ~a\n" instr-name
		    ((send this print-x86) s) 
		    ((send this print-x86) d))]
	   [`(,instr-name ,d)
	    #:when (set-member? (send this instructions) instr-name)
	    (format "\t~aq\t~a\n" instr-name ((send this print-x86) d))]
	   [else (error "print-x86, unmatched" e)]
	   )))

    )) ;; class compile-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define int-exp-passes
  (let ([compiler (new compile-S0)]
	[interp (new interp-S0)])
    (list `("programify" ,(lambda (ast) `(program () ,ast))
	    ,(send interp interp-scheme '()))
	  `("uniquify" ,(send compiler uniquify '())
	    ,(send interp interp-scheme '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,(send interp interp-C '()))
	  `("instruction selection" ,(send compiler select-instructions)
	    ,(send interp interp-x86 '()))
	  `("assign locations" ,(send compiler assign-locations (void))
	    ,(send interp interp-x86 '()))
	  `("insert spill code" ,(send compiler insert-spill-code)
	    ,(send interp interp-x86 '()))
	  `("print x86" ,(send compiler print-x86) #f)
	  )))

