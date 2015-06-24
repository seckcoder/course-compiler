#lang racket
(require "register_allocator.rkt")
(require "interp.rkt")
(provide compile-S1 conditionals-passes)

(define compile-S1
  (class compile-reg-S0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) (set 'eq? 'and 'or 'not)))

    (define/override (binary-op->inst op)
      (match op
	 ['eq? 'cmp]
	 ['and 'and]
	 ['or 'or]
	 [else (super binary-op->inst op)]
	 ))

    (define/override (unary-op->inst op)
      (match op
	 ['not 'not]
	 [else (super unary-op->inst op)]
	 ))

    (define/override (uniquify env)
      (lambda (e)
	(match e
	   [#t #t]
	   [#f #f]
	   [`(if ,cnd ,thn ,els)
	    (let ([cnd ((send this uniquify env) cnd)]
		  [thn ((send this uniquify env) thn)]
		  [els ((send this uniquify env) els)])
	      `(if ,cnd ,thn ,els))]
	   [else ((super uniquify env) e)]
	   )))
  
    (define/override (flatten need-atomic)
      (lambda (e)
	(match e
	   [#t (values #t '())]
	   [#f (values #f '())]
	   [`(if ,cnd ,thn ,els)
	    (let-values ([(new-cnd cnd-ss) ((send this flatten #t) cnd)]
			 [(new-thn thn-ss) ((send this flatten #t) thn)]
			 [(new-els els-ss) ((send this flatten #t) els)])
	      (let* ([tmp (gensym 'if)]
		     [thn-ret `(assign ,tmp ,new-thn)]
		     [els-ret `(assign ,tmp ,new-els)])
		(values tmp
			(append cnd-ss
				`(if ,new-cnd
				     ,(append thn-ss (list thn-ret))
				     ,(append els-ss (list els-ret)))))))]
	   [else ((super flatten need-atomic) e)]
	   )))

    (define/override (instruction-selection)
      (lambda (e)
	(match e
	   [#t `(int 1)]
	   [#f `(int 0)]
	   [`(assign ,lhs ,b)
	    #:when (boolean? b)
	    
	    
	    
	    ]
	   ;; Keep the if statement to simplify register allocation
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((send this instruction-selection) cnd)]
		  [thn-ss (append* (map (send this instruction-selection) 
					thn-ss))]
		  [els-ss (append* (map (send this instruction-selection)
					els-ss))])
	      `(if ,cnd ,thn-ss ,els-ss))]
	   [else
	    ((super instruction-selection) e)]
	   )))

    (define/override (liveness-analysis live-after)
      (lambda (ast)
	(match ast
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let-values ([(thn-ss thn-lives)
			  ((send this liveness-ss live-after) thn-ss)]
			 [(els-ss els-lives)
			  ((send this liveness-ss live-after) els-ss)])
	      (let ([live-after-thn (cond [(null? thn-lives) live-after]
					  [else (car thn-lives)])]
		    [live-after-els (cond [(null? els-lives) live-after]
					  [else (car els-lives)])])
		(values
		 `(if ,cnd ,thn-ss ,thn-lives ,els-ss ,els-lives)
		 (set-union live-after-thn live-after-els
			    (send this free-vars cnd)))))]
	   [else
	    ((super liveness-analysis live-after) ast)]
	   )))

      (define/override (build-interference live-after G)
	(lambda (ast)
	  (match ast
	     [`(if ,cnd ,thn-ss ,thn-lives ,els-ss ,els-lives)
	      (for ([inst (append thn-ss els-ss)]
		    [live-after (append thn-lives els-lives)]) 
		   ((send this build-interference 
			  live-after G) inst))
	      `(if ,cnd ,thn-ss ,els-ss)]
	     [else
	      ((super build-interference live-after G) ast)]
	     )))
      
      
    )) ;; compile-S1

(define conditionals-passes
  (let ([compiler (new compile-S1)]
	[interp (new interp-S1)])
    (list `("uniquify" ,(lambda (ast) ((send compiler uniquify '())
				       `(program () ,ast)))
	    ,(send interp interp-scheme '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,(send interp interp-C '()))
	  `("instruction selection" ,(send compiler instruction-selection)
	    ,(send interp interp-x86 '()))
	  `("liveness analysis" ,(send compiler liveness-analysis (void))
	    ,(send interp interp-x86 '()))
	  `("build interference" ,(send compiler
					build-interference (void) (void))
	    ,(send interp interp-x86 '()))
	  #;`("allocate registers" ,(send compiler allocate-registers)
	    ,(send interp interp-x86 '()))
	  #;`("insert spill code" ,(send compiler insert-spill-code)
	    ,(send interp interp-x86 '()))
	  #;`("print x86" ,(send compiler print-x86) #f)
	  )))
