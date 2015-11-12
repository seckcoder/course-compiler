#lang racket
(require "vectors.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-S3 functions-passes)

(define compile-S3
  (class compile-S2
    (super-new)

    (define/public (non-apply-ast)
      (set-union (send this primitives)
		 (set 'if 'let 'define 'program)))

    (define (fun-def-name d)
      (match d
	 [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	  f]
	 [else (error "ill-formed function definition")]))
      
    (define (fun-def-type d)
      (match d
	 [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	  `(,@ps -> ,rt)]
	 [else (error "ill-formed function definition")]))
      


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S3 -> S3 (for programs)
    ;; type-check : env -> S3 -> type (for expressions)
    (define/override (type-check env)
      (lambda (e)
	(match e
	   [`(,f ,es ...) #:when (not (set-member? (send this non-apply-ast) f))
	    (define t-args (map (send this type-check env) es))
	    (define f-t ((send this type-check env) f))
	    (match f-t
	       [`(,ps ... -> ,rt)
		(unless (equal? t-args ps)
		  (error "parameter and argument type mismatch for function" f))
		rt]
	       [else (error "expected a function, not" f-t)])]
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    ((send this type-check (append (map cons xs ps) env)) body)]
	   [`(program ,ds ... ,body)
	    (define new-env (for/list ([d ds]) 
				      (cons (fun-def-name d) (fun-def-type d))))
	    (for ([d ds])
	       ((send this type-check new-env) d))
	    ((send this type-check new-env) body)
	    `(program ,@ds ,body)]
	   [else ((super type-check env) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S3 -> S3

    (define/override (uniquify env)
      (lambda (e)
	(match e
	   [`(,f ,es ...) #:when (not (set-member? (send this non-apply-ast) f))
	    (define new-es (map (send this uniquify env) es))
	    (define new-f ((send this uniquify env) f))
	    `(,new-f ,@new-es)]
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (define new-xs (map gensym xs))
	    (define new-env (append (map cons xs new-xs) env))
	    `(define (,(cdr (assq f env)) 
		      ,@(map (lambda (x t) `[,x : ,t]) new-xs ps)) : ,rt 
		      ,((send this uniquify new-env) body))]
	   [`(program ,ds ... ,body)
	    (define new-env
	      (for/list ([d ds])
	         (match d
                    [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
		     (define new-f (gensym f))
		     `(,f . ,new-f)]
		    [else (error "type-check, ill-formed function def")])))
	    `(program ,@(map (send this uniquify new-env) ds)
		      ,((send this uniquify new-env) body))]
	   [else ((super uniquify env) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal functions and application

    (define/public (reveal-functions funs)
      (lambda (e)
	(let ([recur (send this reveal-functions funs)])
        (define ret
	  (match e
	     [(? number?) e]
	     [(? symbol?)
	      (cond [(memq e funs) `(function-ref ,e)]
		    [else e])]
	     [`(let ([,x ,e]) ,body)
	      `(let ([,x ,(recur e)]) ,(recur body))]
	     [#t #t]
	     [#f #f]
	     [`(if ,cnd ,thn ,els)
	      `(if ,(recur cnd) ,(recur thn) ,(recur els))]
	     [`(define (,f ,params ...) : ,rt ,body)
	      `(define (,f ,@params) : ,rt ,(recur body))]
	     [`(program ,ds ... ,body)
	      (define funs (for/list ([d ds]) (fun-def-name d)))
	      `(program ,@(map (send this reveal-functions funs) ds)
			,((send this reveal-functions funs) body))]
	     [`(,op ,es ...) #:when (set-member? (send this primitives) op)
	      `(,op ,@(map recur es))]
	     [`(,f ,es ...)
	      `(app ,(recur f) ,@(map recur es))]
	     ))
	ret)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S3 -> C3-expr x (C3-stmt list)

    (define (flatten-body body)
      (define-values (new-body ss) ((send this flatten #f) body))
      (define locals (append* (map (send this collect-locals) ss)))
      (values (remove-duplicates locals) 
	      (append ss `((return ,new-body)))))

    (define/override (flatten need-atomic)
      (lambda (ast)
	(match ast
	   [`(program ,ds ... ,body)
	    (define-values (locals new-body) (flatten-body body))
	    (define new-ds (map (send this flatten #f) ds))
	    `(program ,locals ,new-ds ,@new-body)]
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (define-values (locals new-body) (flatten-body body))
	    `(define (,f ,@(map (lambda (x t) `[,x : ,t]) xs ps)) : ,rt ,locals
			 ,@new-body)]
	   [`(function-ref ,f)
	    (define tmp (gensym 'tmp))
	    (values tmp (list `(assign ,tmp (function-ref ,f))))]
	   [`(app ,f ,es ...) 
	    (define-values (new-f f-ss) ((send this flatten #t) f))
	    (define-values (new-es sss) (map2 (send this flatten #t) es))
	    (define ss (append f-ss (append* sss)))
	    (define fun-apply `(app ,new-f ,@new-es))
	    (cond [need-atomic
		   (define tmp (gensym 'tmp))
		   (values tmp (append ss `((assign ,tmp ,fun-apply))))]
		  [else (values fun-apply ss)])]
	   [else ((super flatten need-atomic) ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S3 -> S3

    (define max-stack 0)

    (define/override (select-instructions)
      (lambda (e)
	(match e
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
	    (set! max-stack 0)
	    (define n (vector-length arg-registers))
	    ;; move from registers and stack locations to parameters
	    (define-values (first-params last-params) 
	      (cond[(> (length xs) n) (split-at xs n)]
		   [else (values xs '())]))
	    (define mov-regs
	      (for/list ([param first-params] [r arg-registers])
	         `(mov (register ,r) (var ,param))))
	    (define mov-stack
	      (for/list ([param last-params] 
			 [i (in-range 0 (length last-params))])
	         `(mov (stack-loc ,(- (+ 16 (* i 8)))) (var ,param))))
	    (define new-ss (append mov-stack mov-regs
              (append* (map (send this select-instructions) ss))))
	    ;; parameters become locals
	    `(define (,f) ,(length xs) (,(append xs locals) ,max-stack)
	       ,@new-ss)]
	   [`(assign ,lhs (function-ref ,f))
	    (define new-lhs ((send this select-instructions) lhs))
	    `((lea (function-ref ,f) ,new-lhs))]
	   [`(assign ,lhs (app ,f ,es ...))
	    (define new-lhs ((send this select-instructions) lhs))
	    (define new-f ((send this select-instructions) f))
	    (define new-es (map (send this select-instructions) es))
	    (define n (vector-length arg-registers))
	    (define-values (first-args last-args) 
	      (cond[(> (length new-es) n) (split-at new-es n)]
		   [else (values new-es '())]))
	    (define mov-regs
	      (for/list ([arg first-args] [r arg-registers])
	         `(mov ,arg (register ,r))))
	    (define mov-stack
	      (for/list ([arg last-args] [i (in-range 0 (length last-args))])
	         `(mov ,arg (stack-arg ,(* i 8)))))
	    (set! max-stack (max max-stack (length last-args)))
	    (append mov-stack mov-regs
	     `((indirect-call ,new-f) (mov (register rax) ,new-lhs)))]
	   [`(program ,locals ,ds ,ss ...)
	    (define new-ds (map (send this select-instructions) ds))
	    (set! max-stack 0)
	    (define sss (map (send this select-instructions) ss))
	    `(program (,locals ,max-stack) ,new-ds ,@(append* sss))]
	   [else ((super select-instructions) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*

    (define/override (read-vars instr)
      (match instr
         [`(lea ,s ,d) (send this free-vars s)]
	 [`(indirect-call ,f) (send this free-vars f)]
     	 [else (super read-vars instr)]))

    (define/override (write-vars instr)
      (match instr
	 [`(indirect-call ,f) caller-save]
	 [`(lea ,s ,d)  (send this free-vars d)]
     	 [else (super write-vars instr)]))

    (define/override (uncover-live live-after)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack) ,ss ...)
	    (define-values (new-ss lives) ((send this liveness-ss (set)) ss))
	    `(define (,f) ,n (,locals ,max-stack ,lives) ,@new-ss)]
           [`(program (,locals ,max-stack) ,ds ,ss ...)
	    (define-values (new-ss lives) ((send this liveness-ss (set)) ss))
	    (define new-ds (map (send this uncover-live (set)) ds))
	    `(program (,locals ,max-stack ,lives) ,new-ds ,@new-ss)]
	   [else ((super uncover-live live-after) ast)]
	   )))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph

    (define/override (build-interference live-after G)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack ,lives) ,ss ...)
	    (define new-G (make-graph locals))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
			((send this build-interference live-after new-G) inst)))
	    `(define (,f) ,n (,locals ,max-stack ,new-G) ,@new-ss)]
           [`(program (,locals ,max-stack ,lives) ,ds ,ss ...)
	    (define new-G (make-graph locals))
	    (define new-ds (for/list ([d ds])
			      ((send this build-interference (void) (void)) d)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
			((send this build-interference live-after new-G) inst)))
	    `(program (,locals ,max-stack ,new-G) ,new-ds ,@new-ss)]
	   [else ((super build-interference live-after G) ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-locations : homes -> pseudo-x86 -> pseudo-x86

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'lea)))

    (define/override (assign-locations homes)
      (lambda (e)
	(match e
	   [`(stack-loc ,i) `(stack-loc ,i)]
	   [`(stack-arg ,i) `(stack-arg ,i)]
	   [`(indirect-call ,f)
	    `(indirect-call ,((send this assign-locations homes) f))]
	   [`(function-ref ,f) `(function-ref ,f) ]
	   [else ((super assign-locations homes) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86

    (define/override (allocate-registers)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,xs ,max-stack ,G) ,ss ...)
	    (define-values (homes stk-size) (send this allocate-homes G xs ss))
	    (define new-ss (map (send this assign-locations homes) ss))
	    `(define (,f) ,n ,(+ stk-size (* 8 max-stack)) ,@new-ss)]
           [`(program (,locals ,max-stack ,G) ,ds ,ss ...)
	    (define new-ds (map (send this allocate-registers) ds)) 
	    (define-values (homes stk-size) 
	      (send this allocate-homes G locals ss))
	    (define new-ss (map (send this assign-locations homes) ss))
	    `(program ,(align (+ stk-size (* 8 max-stack)) 16)
		      ,new-ds ,@new-ss)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; insert-spill-code : psuedo-x86 -> x86

    (define/override (on-stack? a)
      (match a
	 [`(function-ref ,f) #t]
	 [else (super on-stack? a)]))

    (define/override (insert-spill-code)
      (lambda (e)
	(match e
	   [`(define (,f) ,n ,stack-space ,ss ...)
	    (define sss (for/list ([s ss]) ((send this insert-spill-code) s)))
	    `(define (,f) ,n ,stack-space ,@(append* sss))]
	   [`(indirect-call ,f)
	    `((indirect-call ,f))]
	   [`(program ,stack-space ,ds ,ss ...)
	    (define new-ds (for/list ([d ds])
				     ((send this insert-spill-code) d)))
	    (define sss (for/list ([s ss]) ((send this insert-spill-code) s)))
	    `(program ,stack-space ,new-ds ,@(append* sss))]
	   [`(lea ,s ,d)
	    (cond [(on-stack? d)
		   `((lea ,s (register rax))
		     (mov (register rax) ,d))]
		  [else
		   `((lea ,s ,d))])]
	   [else ((super insert-spill-code) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(function-ref ,f)
	    (format "~a(%rip)" f)]
	   [`(indirect-call ,f)
	    (format "\tcallq\t*~a\n" ((send this print-x86) f))]
	   [`(stack-arg ,i)
	    (format "~a(%rsp)" i)]
	   [`(define (,f) ,n ,stack-space ,ss ...)
	    (define callee-reg (set->list callee-save))
	    (define save-callee-reg
	      (for/list ([r callee-reg])
			(format "\tpushq\t%~a\n" r)))
	    (define restore-callee-reg
	      (for/list ([r (reverse callee-reg)])
			(format "\tpopq\t%~a\n" r)))
	    (string-append
	     (format "\t.globl ~a\n" f)
	     (format "~a:\n" f)
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (string-append* save-callee-reg)
	     (format "\tsubq\t$~a, %rsp\n" stack-space)
	     "\n"
	     (string-append* (map (send this print-x86) ss))
	     "\n"
	     (format "\taddq\t$~a, %rsp\n" stack-space)
	     (string-append* restore-callee-reg)
	     (format "\tpopq\t%rbp\n")
	     (format "\tretq\n")
	     )]
	   [`(program ,stack-space ,ds ,ss ...)
	    (string-append
	     (string-append* (for/list ([d ds]) ((send this print-x86) d)))
	     "\n"
	     ((super print-x86) `(program ,stack-space ,@ss)))]
	   [else ((super print-x86) e)]
	   )))

    ));; compile-S3
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define functions-passes
  (let ([compiler (new compile-S3)]
	[interp (new interp-S3)])
    (list `("programify"
	    ,(lambda (ast) 
	       (match ast
		  [`(program ,ds ... ,body)
		   `(program ,@ds ,body)]
		  [else ;; for backwards compatibility with S0 thru S2
		   `(program ,ast)]))
	    ,(send interp interp-scheme '()))
	  `("type-check" ,(send compiler type-check '())
	    ,(send interp interp-scheme '()))
	  `("uniquify" ,(send compiler uniquify '())
	    ,(send interp interp-scheme '()))
	  `("reveal-functions" ,(send compiler reveal-functions '())
	    ,(send interp interp-scheme '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,(send interp interp-C '()))
	  `("instruction selection" ,(send compiler select-instructions)
	    ,(send interp interp-x86 '()))
	  `("liveness analysis" ,(send compiler uncover-live (void))
	    ,(send interp interp-x86 '()))
	  `("build interference" ,(send compiler build-interference
					(void) (void))
	    ,(send interp interp-x86 '()))
	  `("allocate registers" ,(send compiler allocate-registers)
	    ,(send interp interp-x86 '()))
	  `("insert spill code" ,(send compiler insert-spill-code)
	    ,(send interp interp-x86 '()))
	  `("print x86" ,(send compiler print-x86) #f)
	  )))
