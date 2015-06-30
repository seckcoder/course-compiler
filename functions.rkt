#lang racket
(require "vectors.rkt")
(require "interp.rkt")
(provide compile-S3 functions-passes)

(define compile-S3
  (class compile-S2
    (super-new)
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S3 -> S3
    (define/override (type-check env)
      (lambda (e)
	(match e
	   [`(,f ,es ...) #:when (assq f env)
	    (define t-args (map (send this type-check env) es))
	    (define f-t (cdr (assq f env)))
	    (match f-t
	       [`(,ps ... -> ,rt)
		(unless (equal? t-args ps)
		  (error "parameter and argument type mismatch for function" f))
		rt]
	       [else (error "expected a function, not" f-t)])]
	   [`(program ,ds ... ,body)
	    
	    ]
	   [else ((super type-check env) e)]
	   )))

    ));; compile-S3
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define vectors-passes
  (let ([compiler (new compile-S2)]
	[interp (new interp-S2)])
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
