#lang racket

(provide interp-S0 interp-C0 interp-x86)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter for S0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (interp-S0 env ast)
  (match ast
     [`(var ,x)
      (cond [(assq x env) => (lambda (p) (cdr p))]
		   [else (error "in interp-S0, undefined variable " x)])]
     [`(int ,n) n]
     [`(prim ,name ,op ,args ...)
      (apply op (map (lambda (e) (interp-S0 env e)) args))]
     [`(let ([,x ,e]) ,body)
      (let ([v (interp-S0 env e)])
	(interp-S0 (cons (cons x v) env) body))]
     [`(program ,e) (interp-S0 '() e)]
     [else
      (error interp-S0 "no match in interp-S0 for " ast)]
     ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; C0
;;
;; atomic   a  ::= n | x
;; expr     e  ::= a | (prim op a ...)
;; stmt     s  ::= (assign (var x) e) | (return a)
;; program  p  ::= (program (x ...) (s ...))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define result (gensym 'result))

(define (interp-C0 env ast)
  (match ast
     [`(var ,x)
      (cond [(assq x env) => cdr]
	    [else (error "in interp-C0, undefined variable " x)])]
     [`(int ,n) n]
     [`(prim ,name ,op ,args ...)
      (apply op (map (lambda (e) (interp-C0 env e)) args))]
     [`(assign (var ,x) ,e)
      (let ([v (interp-C0 env e)])
	(cons (cons x v) env))]
     [`(return ,e)
      (let ([v (interp-C0 env e)])
	(cons (cons result v) env))]
     [`(program ,xs ,ss) 
      (let loop ([env '()] [ss ss])
	(cond [(null? ss)
	       (cond [(assq result env) => cdr]
		     [else (error "missing return statement")])]
	      [else
	       (loop (interp-C0 env (car ss)) (cdr ss))]))]
     [else
      (error interp-C0 "no match in interp-C0 for " ast)]
     ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; psuedo-x86 and x86
;; s,d ::= (var x) | (int n) | (register r) | (stack-loc n)
;; i   ::= (mov s d) | (add s d) | (sub s d) | (neg d) | (call f)
;; psuedo-x86 ::= (program (x ...) (i ...))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-name ast)
  (match ast
     [(or `(var ,x) `(register ,x) `(stack-loc ,x))
      x]
     [else
      (error "doesn't have a name: " ast)]))

(define (interp-x86 env ast)
  (match ast
     [(or `(var ,x) `(register ,x) `(stack-loc ,x))
      (cond [(assq x env) => cdr]
	    [else (error "in interp-x86, undefined variable " x)])]
     [`(int ,n) n]
     [`(call _read_int) (cons (cons 'rax (read)) env)]
     [`(add ,s ,d)
      (let ([s (interp-x86 env s)] 
	    [d (interp-x86 env d)]
	    [x (get-name d)])
	(cons (cons x (+ d s)) env))]
     [`(sub ,s ,d)
      (let ([s (interp-x86 env s)] 
	    [d (interp-x86 env d)]
	    [x (get-name d)])
	(cons (cons x (- d s)) env))]
     [`(neg ,d)
      (let ([d (interp-x86 env d)]
	    [x (get-name d)])
	(cons (cons x (- d)) env))]
     [(or `(mov ,e (var ,x)) `(mov ,e (stack-loc ,x))
	  `(mov ,e (register ,x)))
      (let ([v (interp-x86 env e)])
	(cons (cons x v) env))]
     [`(program ,xs ,ss) 
      (let loop ([env '()] [ss ss])
	(cond [(null? ss)
	       (cond [(assq 'rax env) => cdr]
		     [else (error "rax not initialized")])]
	      [else
	       (loop (interp-x86 env (car ss)) (cdr ss))]))]
     [else
      (error interp-x86 "no match in interp-x86 for " ast)]
     ))

