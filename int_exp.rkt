#lang racket

(define (sexp->ast sexp)
  (match sexp
     [(? symbol?) `(var ,sexp)]
     [(? integer?) `(int ,sexp)]
     [`(+ ,e1 ,e2) `(prim ,+ ,(sexp->ast e1) ,(sexp->ast e2))]
     [`(- ,e) `(prim ,- ,(sexp->ast e))]
     [`(let: ([,xs : ,Ts ,es] ...) ,body)
      (let ([bs (map (lambda (x T e) `[,x : ,T ,(sexp->ast e)]) xs Ts es)])
	`(let: ,bs ,(sexp->ast body)))]
     [else (error "sexp->ast, unhandled case in match for " sexp)]))

(define p0 0)
;(sexp->ast p0)
(define p1 '(+ 10 (- 5)))
;(sexp->ast p1)
(define p2 '(let: ([x : Integer 41] [y : Integer 1]) (+ x y)))
;(sexp->ast p2)

(define flatten-mt (make-hash))

(define (flatten e)
  (match e
	 [`(,tag ,args ...)
	  (apply (hash-ref flatten-mt tag) args)]
	 [else
	  (error "no match in flatten" e)
	  ]))

(hash-set! flatten-mt 'var
	   (lambda (x) (values `(var ,x) '())))
(hash-set! flatten-mt 'int
	   (lambda (n) (values `(int ,n) '())))
(hash-set! flatten-mt 'prim
	   (lambda (op . es) 
	     (let ([es-bs (foldl
			   (lambda (e es-bs)
			     (let-values ([(ep bs) (flatten e)])
			       (cons (cons ep (car es-bs))
				     (cons bs (cdr es-bs)))))
			   (cons '() '())
			   es)])
	       (let ([tmp (gensym 'tmp)] [es (car es-bs)] [bs (cdr es-bs)])
		 (values `(var ,tmp)
			 (append bs
				 (list `(,tmp : Integer
					      (prim ,op ,es ...))))
			 )))))
(hash-set! flatten-mt 'let
	   (lambda (bs body)
	     (let-values ([(new-body body-bs) (flatten body)])
	       (let ([new-bs
		      (foldl
		       (lambda (b res-bs)
			 (match b
				[`(,x : ,T ,e)
				 (let-values ([(ep bs) (flatten e)])
				   (append bs 
					   (list `(,x : ,T ,ep))
					   res-bs))]))
		       body-bs
		       bs)])
		 `(let: ,new-bs ,new-body)))))

;(flatten (sexp->ast p1))

(define (interp ast env)
  (match ast
	 [`(var ,x) (cdr (assq x env))]
	 [`(int ,n) n]
	 [`(prim ,op ,args ...)
	  (apply op (map (lambda (e) (interp e env)) args))]
	 [`(let: ,bs ,body)
	  (let ([new-env
		 (foldl
		  (lambda (b env)
		    (match b
			   [`(,x : ,T ,e)
			    (cons (cons x (interp e env))
				  env)]))
		  env
		  bs)])
	    (interp body new-env)
	    )]
	 [else
	  (error interp "no match in interp for " ast)]))

(interp (sexp->ast p0) '())
(interp (sexp->ast p1) '())
(interp (sexp->ast p2) '())
