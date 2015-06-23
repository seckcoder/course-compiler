#lang racket
(require "utilities.rkt")
(provide interp-S0 interp-C0 interp-x86)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter for S0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (interp-op op)
  (match op
     ['+ +]
     ['- -]
     ['* *]
     ['read read]
     [else (error "in interp-op, unmatched" op)]))

(define (interp-S0 recur)
  (lambda (env)
    (lambda (ast)
      (match ast
         [(? symbol?)
	  (cond [(assq ast env) => (lambda (p) (cdr p))]
		[else (error "in interp-S0, undefined variable " ast)])]
	 [(? integer?) ast]
	 [`(let ([,x ,e]) ,body)
	  (let ([v ((recur env) e)])
	    ((recur (cons (cons x v) env)) body))]
	 [`(program ,extra ,e) ((recur '()) e)]
	 [`(,op ,args ...)
	  (apply (interp-op op) (map (recur env) args))]
	 [else
	  (error (format "no match in interp-S0 for ~a" ast))]
	 ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; C0
;;
;; atomic   a  ::= n | x
;; expr     e  ::= a | (prim op a ...)
;; stmt     s  ::= (assign (var x) e) | (return a)
;; program  p  ::= (program (x ...) (s ...))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define result (gensym 'result))

(define (interp-C0 recur)
  (lambda (env)
    (lambda (ast)
      (match ast
	 [(? symbol?)
	  (cond [(assq ast env) => cdr]
		[else (error "in interp-C0, undefined variable " ast)])]
	 [(? integer?) ast]
	 [`(assign ,x ,e)
	  (let ([v ((recur env) e)])
	    (cons (cons x v) env))]
	 [`(return ,e)
	  (debug "interpreting return" e)
	  (let ([v ((recur env) e)])
	    (debug "return" v)
	    (cons (cons result v) env))]
	 [`(program ,xs ,ss) 
	  (let loop ([env '()] [ss ss])
	    (cond [(null? ss)
		   (cond [(assq result env) => cdr]
			 [else (error "missing return statement")])]
		  [else
		   (loop ((recur env) (car ss)) (cdr ss))]))]
	 [`(,op ,args ...)
	  (apply (interp-op op) (map (recur env) args))]
	 [else
	  (error "no match in interp-C0 for " ast)]
	 ))))

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

(define (interp-x86 recur)
  (lambda (env)
    (lambda (ast)
      (match ast
         [(or `(var ,x) `(register ,x) `(stack-loc ,x))
	  (cond [(assq x env) => cdr]
		[else (error "in interp-x86, undefined variable " x)])]
	 [`(int ,n) n]
	 [`(call _read_int) (cons (cons 'rax (read)) env)]
	 [`(add ,s ,d)
	  (let ([s ((recur env) s)] 
		[d ((recur env) d)]
		[x (get-name d)])
	    (cons (cons x (+ d s)) env))]
	 [`(sub ,s ,d)
	  (let ([s ((recur env) s)] 
		[d ((recur env) d)]
		[x (get-name d)])
	    (cons (cons x (- d s)) env))]
	 [`(neg ,d)
	  (let ([d ((recur env) d)]
		[x (get-name d)])
	    (cons (cons x (- d)) env))]
	 [(or `(mov ,e (var ,x)) `(mov ,e (stack-loc ,x))
	      `(mov ,e (register ,x)))
	  (let ([v ((recur env) e)])
	    (cons (cons x v) env))]
	 [`(program ,xs ,ss) 
	  (let loop ([env '()] [ss ss])
	    (cond [(null? ss)
		   (cond [(assq 'rax env) => cdr]
			 [else (error "in interp-x86, rax not initialized for return")])]
		  [else
		   (loop ((recur env) (car ss)) (cdr ss))]))]
	 [else
	  (error interp-x86 "no match in interp-x86 for " ast)]
	 ))))

