#lang racket
(require "vectors.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-S3 functions-passes)

(define compile-S3
  (class compile-S2
    (super-new)
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S3 -> S3
    (define/override (type-check env)
      (lambda (e)
	(match e
	   [`(,f ,es ...) #:when (and (symbol? f) (assq f env))
	    (define t-args (map (send this type-check env) es))
	    (define f-t (cdr (assq f env)))
	    (match f-t
	       [`(,ps ... -> ,rt)
		(unless (equal? t-args ps)
		  (error "parameter and argument type mismatch for function" f))
		rt]
	       [else (error "expected a function, not" f-t)])]
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    ((send this type-check (append (map cons xs ps) env)) body)]
	   [`(program ,ds ... ,body)
	    (define new-env
	      (for/list ([d ds])
	         (match d
                    [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
		     `(,f . (,@ps -> ,rt))]
		    [else (error "type-check, ill-formed function def")])))
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
	   [`(,f ,es ...) #:when (and (symbol? f) (assq f env))
	    (define new-es (map (send this uniquify env) es))
	    (define new-f (cdr (assq f env)))
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
	   [`(,f ,es ...) 
	    #:when (and (symbol? f) 
			(not (set-member? (send this primitives) f)))
	    (define-values (new-es sss) (map2 (send this flatten #t) es))
	    (define ss (append* sss))
	    (define fun-apply `(,f ,@new-es))
	    (cond [need-atomic
		   (define tmp (gensym 'tmp))
		   (values tmp (append ss `((assign ,tmp ,fun-apply))))]
		  [else (values fun-apply ss)])]
	   [else ((super flatten need-atomic) ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S3 -> S3

    (define/override (select-instructions)
      (lambda (e)
	(match e
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
	    ;; move from registers and stack locations to parameters
	    (define-values (first-params last-params) 
	      (cond[(> (length xs) 6) (split-at xs 6)]
		   [else (values xs '())]))
	    (define mov-regs
	      (for/list ([param first-params] [r arg-registers])
	         `(mov (register ,r) (var ,param))))
	    (define mov-stack
	      (for/list ([param last-params] 
			 [i (in-range 0 (length last-params))])
	         `(mov (stack-loc ,(- (+ 16 i))) (var ,param))))
	    (define new-ss (append mov-stack mov-regs
              (append* (map (send this select-instructions) ss))))
	    `(define (,f) ,(length xs) ,locals ,@new-ss)]
	   [`(assign ,lhs (,f ,es ...))
	    #:when (and (symbol? f) 
			(not (set-member? (send this primitives) f)))
	    (define new-lhs ((send this select-instructions) lhs))
	    (define new-es (map (send this select-instructions) es))
	    (define-values (first-args last-args) 
	      (cond[(> (length new-es) 6) (split-at new-es 6)]
		   [else (values new-es '())]))
	    (define mov-regs
	      (for/list ([arg first-args] [r arg-registers])
	         `(mov ,arg (register ,r))))
	    (define mov-stack
	      (for/list ([arg last-args] [i (in-range 0 (length last-args))])
	         `(mov ,arg (stack-arg ,(* i 8)))))
	    (append mov-stack mov-regs
	     `((call ,f) (mov (register rax) ,new-lhs)))]
	   [`(program ,locals ,ds ,ss ...)
	    `(program ,locals
		      ,(map (send this select-instructions) ds)
		      ,@(append* (map (send this select-instructions) ss)))]
	   [else ((super select-instructions) e)]
	   )))
    ));; compile-S3
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define functions-passes
  (let ([compiler (new compile-S3)]
	[interp (new interp-S3)])
    (list `("programify" ,(lambda (ast) ast)
	    ,(send interp interp-scheme '()))
	  `("type-check" ,(send compiler type-check '())
	    ,(send interp interp-scheme '()))
	  `("uniquify" ,(send compiler uniquify '())
	    ,(send interp interp-scheme '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,(send interp interp-C '()))
	  `("instruction selection" ,(send compiler select-instructions)
	    ,(send interp interp-x86 '()))
	  ;; `("liveness analysis" ,(send compiler uncover-live (void))
	  ;;   ,(send interp interp-x86 '()))
	  ;; `("build interference" ,(send compiler build-interference
	  ;;  				(void) (void))
	  ;;   ,(send interp interp-x86 '()))
	  ;; `("allocate registers" ,(send compiler allocate-registers)
	  ;;   ,(send interp interp-x86 '()))
	  ;; `("insert spill code" ,(send compiler insert-spill-code)
	  ;;   ,(send interp interp-x86 '()))
	  ;; `("print x86" ,(send compiler print-x86) #f)
	  )))
