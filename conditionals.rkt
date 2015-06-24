#lang racket
(require (rename-in "int_exp.rkt" (old-uniquify uniquify))
	 (rename-in "int_exp.rkt" (old-flatten flatten)))

(define primitives (set '+ '- '* 'eq? 'and 'or 'not))

(define (uniquify recur)
  (lambda (env)
    (lambda (e)
      (match e
	 [#t #t]
	 [#f #f]
	 [`(if ,cnd ,thn ,els)
	  (let ([cnd ((recur env) cnd)]
		[thn ((recur env) thn)]
		[els ((recur env) els)])
	    `(if ,cnd ,thn ,els))]
	 [else (((old-uniquify recur) env) e)]
	 ))))

(define (flatten recur)
  (lambda (need-atomic)
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
	 [else (((old-flatten recur) need-atomic) e)]
	 ))))
