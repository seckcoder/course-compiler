#lang racket

(require "register_allocator.rkt")

(define compile-S1
  (class compile-reg-S0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) (set 'eq? 'and 'or 'not)))

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
	    (let-values ([(new-cnd cnd-ss) ((recur #t) cnd)]
			 [(new-thn thn-ss) ((recur #t) thn)]
			 [(new-els els-ss) ((recur #t) els)])
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
			    (free-vars cnd)))))]
	   [else
	    ((super liveness-analysis live-after) ast)]
	   )))
    
    

    )) ;; compile-S1
