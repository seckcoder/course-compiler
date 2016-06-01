#lang racket
(require racket/set racket/stream)
(require "utilities.rkt")
(require "interp.rkt")

(provide int-exp-passes compile-R0)

(define compile-R0
  (class object%
    (super-new)

    (define/public (primitives)
      (set '+ '- 'read))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S0 -> S0
    (define/public (uniquify env)
      (lambda (e)
	(define recur (uniquify env))
	(match e
          [(? symbol?) (cdr (assq e env))]
          [(? integer?) e]
          [`(let ([,x ,(app recur new-e)]) ,body)
           (define new-x (gensym (racket-id->c-id x)))
           `(let ([,new-x ,new-e])
	       ,((uniquify (cons (cons x new-x) env)) body))]
          [`(program ,(app recur new-body))
           `(program ,new-body)]
          [`(,op ,es ...) #:when (set-member? (primitives) op)
           `(,op ,@(map recur es))]
          [else (error "uniquify couldn't match" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : Bool -> S0 -> C0-expr x (C0-stmt list) x var list

    (define/public (flatten need-atomic)
      (lambda (e)
        (verbose "flatten" e)
        (match e
           [(? symbol?) (values e '() '())]
	   [(? integer?) (values e '() '())]
	   [`(let ([,x ,rhs]) ,body)
	    (define-values (new-rhs rhs-ss xs1) ((flatten #f) rhs))
	    (define-values (new-body body-ss xs2) ((flatten need-atomic) body))
	    (values new-body 
		    (append rhs-ss `((assign ,x ,new-rhs)) body-ss)
		    (cons x (append xs1 xs2)))]
	   [`(,op ,(app (flatten #t) new-es sss xss) ...) 
	    #:when (set-member? (primitives) op)
	    (define ss (append* sss))
	    (define xs (append* xss))
	    (define prim-apply `(,op ,@new-es))
	    (cond [need-atomic
		   (define tmp (gensym 'tmp))
		   (values tmp (append ss `((assign ,tmp ,prim-apply))) 
			   (cons tmp xs))]
		  [else (values prim-apply ss xs)])]
	   [`(program ,e)
	    (define-values (new-e ss xs) ((flatten #t) e))
	    `(program ,xs ,@(append ss `((return ,new-e))))]
           [else
	    (error "flatten could not match" e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : C0 -> psuedo-x86

    (define/public (binary-op->inst op)
      (match op
         ['+ 'addq]
	 ['- 'subq]
	 [else (error "in binary-op->inst unmatched" op)]
	 ))

    (define/public (unary-op->inst op)
      (match op
	 ['- 'negq] [else (error "in unary-op->inst unmatched" op)]
	 ))

    (define/public (commutative? op)
      (match op
         ['+ #t]
         [else #f]))

    (define/public (select-instructions)
      (lambda (e)
	(match e
           [(? symbol?) `(var ,e)]
	   [(? integer?) `(int ,e)]
	   [`(reg ,r) `(reg ,r)]
	   [`(return ,e)
	    ((select-instructions) `(assign (reg rax) ,e))]
	   [`(assign ,lhs (read))
	    (define new-lhs ((select-instructions) lhs))
	    `((callq read_int) (movq (reg rax) ,new-lhs))]
	   [`(assign ,lhs ,x) #:when (symbol? x)
	    (define new-lhs ((select-instructions) lhs))
	    (cond [(equal? `(var ,x) new-lhs) '()]
		  [else `((movq (var ,x) ,new-lhs))])]
	   [`(assign ,lhs ,n) #:when (integer? n)
	    (define new-lhs ((select-instructions) lhs))
	    `((movq (int ,n) ,new-lhs))]
	   [`(assign ,lhs (,op ,e1 ,e2))
	    (define new-lhs ((select-instructions) lhs))
	    (define new-e1 ((select-instructions) e1))
	    (define new-e2 ((select-instructions) e2))
	    (define inst (binary-op->inst op))
	    (cond [(equal? new-e1 new-lhs)
		   `((,inst ,new-e2 ,new-lhs))]
		  [(equal? new-e2 new-lhs)
		   `((,inst ,new-e1 ,new-lhs))]
		  ;; The following can shorten the live range of e2. -JGS
		  [(and (commutative? op) 
			(integer? e1) (symbol? e2))
		   `((movq ,new-e2 ,new-lhs) (,inst ,new-e1 ,new-lhs))]
		  [else `((movq ,new-e1 ,new-lhs) (,inst ,new-e2 ,new-lhs))])]
	   [`(assign ,lhs (,op ,e1))	
	    (define new-lhs ((select-instructions) lhs))
	    (define new-e1 ((select-instructions) e1))
	    (define inst (unary-op->inst op))
	    (cond [(equal? new-e1 new-lhs)
		   `((,inst ,new-lhs))]
		  [else `((movq ,new-e1 ,new-lhs) (,inst ,new-lhs))])]
	   [`(program ,locals ,ss ...)
	    (let ([new-ss (map (select-instructions) ss)])
	      `(program ,locals ,@(append* new-ss)))]
	   [else (error "R0/instruction selection, unmatched " e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86
    ;;
    ;; Replace variables with stack locations. Later versions of this pass
    ;; will assign some variables to registers. 

    (define/public (variable-size) 8)
    (define/public (first-offset) 8)

    (define/public (instructions)
      (set 'addq 'subq 'negq 'movq))

    (define/public (assign-homes homes)
      (lambda (e)
	(match e
	   [`(var ,x) (hash-ref homes x)]
	   [`(int ,n) `(int ,n)]
	   [`(reg ,r) `(reg ,r)]
	   [`(deref ,r ,n) `(deref ,r ,n)]
	   [`(callq ,f) `(callq ,f)]
	   [`(program (,xs ...) ,ss ...)
	    ;; create mapping of variables to stack locations
	    (define (make-stack-loc n)
	      `(deref rbp ,(- (+ (first-offset)
				 (* (variable-size) n)))))
	    (define new-homes
	      (make-hash (map cons xs
			      (map make-stack-loc
				   (stream->list (in-range 0 (length xs)))))))
	    (define stack-space (align 
				 (* (length xs)
				    (variable-size))
				 16))
	    `(program ,stack-space
		      ,@(map (assign-homes new-homes) ss))]
	   [`(,instr-name ,as ...) 
	    #:when (set-member? (instructions) instr-name)
	    `(,instr-name ,@(map (assign-homes homes) as))]
	   [else (error "in assign-homes S0, unmatched" e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; patch-instructions : psuedo-x86 -> x86
    ;; Uses register rax to patch things up

    (define/public (in-memory? a)
      (match a
        [`(deref ,reg ,n) #t]
        [else #f]))

    (define/public (patch-instructions)
      (lambda (e)
	(match e
          ;; Large integers cannot be moved directly to memory
          ;; I am not sure what sizes can be moved directly to
          ;; memory. This is a conservative estimate. -andre 
          [`(movq (int ,n) ,(? in-memory? d)) #:when (> n (expt 2 16))
           `((movq (int ,n) (reg rax))
             (movq (reg rax) ,d))]
           [`(movq ,s ,d)
	    (cond [(equal? s d) '()] ;; trivial move, delete it
		  [(and (in-memory? s) (in-memory? d))
		   `((movq ,s (reg rax))
		     (movq (reg rax) ,d))]
                  [else `((movq ,s ,d))])]
	   [`(callq ,f) `((callq ,f))]
	   [`(program ,stack-space ,ss ...)
	    `(program ,stack-space 
		      ,@(append* (map (patch-instructions) ss)))]
	   [`(,instr-name ,s ,d)
	    #:when (set-member? (instructions) instr-name)
	    (cond [(and (in-memory? s) (in-memory? d))	
		   (debug 'patch-instructions "spilling")
		   `((movq ,s (reg rax)) (,instr-name (reg rax) ,d))]
		  [else `((,instr-name ,s ,d))])]
	   [`(,instr-name ,d)
	    #:when (set-member? (instructions) instr-name)
	    `((,instr-name ,d))]
	   )))
  
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/public (print-x86)
      (lambda (e)
	(match e
	   [`(deref ,reg ,i)
	    (format "~a(%~a)" i reg)]
	   [`(int ,n) (format "$~a" n)]
	   [`(reg ,r) (format "%~a" r)]
	   [`(callq ,f)
	    (format "\tcallq\t~a\n" (label-name (symbol->string f)))]
	   [`(program ,stack-space ,ss ...)
	    (string-append
	     (format "\t.globl ~a\n" (label-name "main"))
	     (format "~a:\n" (label-name "main"))
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (format "\tsubq\t$~a, %rsp\n" stack-space)
	     "\n"
	     (string-append* (map (print-x86) ss))
	     "\n"
             (format "\tmovq\t%rax, %rdi\n")
             (format "\tcallq\t~a\n" (label-name "print_int"))
	     (format "\tmovq\t$0, %rax\n")
	     (format "\taddq\t$~a, %rsp\n" stack-space)
	     (format "\tpopq\t%rbp\n")
	     (format "\tretq\n")
	     )]
	   [`(,instr-name ,s ,d)
	    #:when (set-member? (instructions) instr-name)
	    (format "\t~a\t~a, ~a\n" instr-name
		    ((print-x86) s) 
		    ((print-x86) d))]
	   [`(,instr-name ,d)
	    #:when (set-member? (instructions) instr-name)
	    (format "\t~a\t~a\n" instr-name ((print-x86) d))]
	   [else (error "print-x86, unmatched" e)]
	   )))
    )) ;; class compile-R0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define int-exp-passes
  (let ([compiler (new compile-R0)]
	[interp (new interp-R0)])
    (list 
	  `("uniquify" ,(send compiler uniquify '())
	    ,interp-scheme)
	  `("flatten" ,(send compiler flatten #f)
	    ,interp-C)
	  `("instruction selection" ,(send compiler select-instructions)
	    ,interp-x86)
	  `("assign homes" ,(send compiler assign-homes (void))
	    ,interp-x86)
	  `("insert spill code" ,(send compiler patch-instructions)
	    ,interp-x86)
	  `("print x86" ,(send compiler print-x86) #f)
	  )))
