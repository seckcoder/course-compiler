#lang racket
(require "register_allocator.rkt")
(require "interp.rkt")
(require "utilities.rkt")
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
  
    (define/override (collect-locals)
      (lambda (ast)
	(debug "collect-locals in S1" ast)
	(match ast
	   [`(if ,cnd ,thn ,els)
	    (append (append* (map (send this collect-locals) thn))
		    (append* (map (send this collect-locals) els)))]
	   [else
	    ((super collect-locals) ast)]
	   )))

    (define/override (flatten need-atomic)
      (lambda (e)
	(debug "flattening in S1" e)
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
				(list `(if ,new-cnd
					   ,(append thn-ss (list thn-ret))
					   ,(append els-ss (list els-ret))))))))]
	   [else ((super flatten need-atomic) e)]
	   )))

    (define/override (instruction-selection)
      (lambda (e)
	(match e
	   [#t `(int 1)]
	   [#f `(int 0)]
	   [`(assign ,lhs ,b)
	    #:when (boolean? b)
	    (let ([lhs ((send this instruction-selection) lhs)]
		  [b ((send this instruction-selection) b)])
	      (list `(mov ,b ,lhs)))]

	   ;; Keep the if statement to simplify register allocation
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((send this instruction-selection) cnd)]
		  [thn-ss (append* (map (send this instruction-selection) 
					thn-ss))]
		  [els-ss (append* (map (send this instruction-selection)
					els-ss))])
	      (list `(if ,cnd ,thn-ss ,els-ss)))]
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
	      (debug "build interference for" ast)
	      (for ([inst (append thn-ss els-ss)]
		    [live-after (append thn-lives els-lives)]) 
		   ((send this build-interference 
			  live-after G) inst))
	      `(if ,cnd ,thn-ss ,els-ss)]
	     [else
	      ((super build-interference live-after G) ast)]
	     )))
      
    (define/override (assign-locations homes)
      (lambda (e)
	(match e
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((send this assign-locations homes) cnd)]
		  [thn-ss (map (send this assign-locations homes) thn-ss)]
		  [els-ss (map (send this assign-locations homes) els-ss)])
	      `(if ,cnd ,thn-ss ,els-ss))]
	   [else
	    ((super assign-locations homes) e)]
	   )))
      
    (define/override (insert-spill-code)
      (lambda (e)
	(match e
           [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([else-label (gensym 'else)]
		  [end-label (gensym 'if-end)])
	      (append
	       `((cmpl (int 0) ,cnd))
	       `((je ,else-label))
	       thn-ss
	       `((jmp ,end-label))
	       `((label ,else-label))
	       els-ss
	       `((label ,end-label))
	       ))]
	   [else
	    ((super insert-spill-code) e)])))

    (define/override (print-x86)
      (lambda (e)
	(match e
           [`(cmpl ,s1 ,s2) 
	    (format "\tcmpl\t~a,~a\n"
		    ((send this print-x86) s1)
		    ((send this print-x86) s2))]
	   [`(je ,label)
	    (format "\tje ~a\n" label)]
	   [`(jmp ,label)
	    (format "\tjmp ~a\n" label)]
	   [`(label ,l)
	    (format "~a:\n" l)]
	   [else
	    ((super print-x86) e)]
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
	  `("build interference" ,(send compiler build-interference
					(void) (void))
	    ,(send interp interp-x86 '()))
	  `("allocate registers" ,(send compiler allocate-registers)
	    ,(send interp interp-x86 '()))
	  `("insert spill code" ,(send compiler insert-spill-code)
	    ,(send interp interp-x86 '()))
	  `("print x86" ,(send compiler print-x86) #f)
	  )))
