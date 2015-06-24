#lang racket
(require "utilities.rkt")
(provide interp-S0 interp-S1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter for S0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define interp-S0
  (class object%
    (super-new)

    (define/public (interp-op op)
      (match op
         ['+ +]
	 ['- -]
	 ['* *]
	 ['read read]
	 [else (error "in interp-op S0, unmatched" op)]))

    (define/public (interp-scheme env)
      (lambda (ast)
	(match ast
           [(? symbol?)
	    (cond [(assq ast env) => (lambda (p) (cdr p))]
		  [else (error "interp-scheme S0, undefined variable " ast)])]
	   [(? integer?) ast]
	   [`(let ([,x ,e]) ,body)
	    (let ([v ((send this interp-scheme env) e)])
	      ((send this interp-scheme (cons (cons x v) env)) body))]
	   [`(program ,extra ,e) ((send this interp-scheme '()) e)]
	   [`(,op ,args ...)
	    (apply (interp-op op) (map (send this interp-scheme env) args))]
	   [else
	    (error (format "no match in interp-scheme S0 for ~a" ast))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; C0
    ;;
    ;; atomic   a  ::= n | x
    ;; expr     e  ::= a | (op a ...)
    ;; stmt     s  ::= (assign x e) | (return a)
    ;; program  p  ::= (program (x ...) (s ...))
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define result (gensym 'result))

    (define/public (seq-C env)
      (lambda (ss)
	(let loop ([env env] [ss ss])
	  (cond [(null? ss)
		 env]
		[else
		 (loop ((send this interp-C env) (car ss)) 
		       (cdr ss))]))))
	
    (define/public (interp-C env)
      (lambda (ast)
	(match ast
           [(? symbol?)
	    (cond [(assq ast env) => cdr]
		  [else (error "in interp-C0, undefined variable " ast)])]
	   [(? integer?) ast]
	   [`(assign ,x ,e)
	    (let ([v ((send this interp-C env) e)])
	      (cons (cons x v) env))]
	   [`(return ,e)
	    (debug "interpreting return" e)
	    (let ([v ((send this interp-C env) e)])
	      (debug "return" v)
	      (cons (cons result v) env))]
	   [`(program ,xs ,ss)
	    (let ([env ((send this seq-C '()) ss)])
	      (cond [(assq result env) => cdr]
		    [else (error "missing return statement")]))]
	   [`(,op ,args ...)
	    (apply (interp-op op) (map (send this interp-C env) args))]
	   [else
	    (error "no match in interp-C0 for " ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; psuedo-x86 and x86
    ;; s,d ::= (var x) | (int n) | (register r) | (stack-loc n)
    ;; i   ::= (mov s d) | (add s d) | (sub s d) | (neg d) | (call f)
    ;; psuedo-x86 ::= (program (x ...) (i ...))
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define (get-name ast)
      (match ast
         [(or `(var ,x) `(register ,x) `(stack-loc ,x))
	  x]
	 [else
	  (error "doesn't have a name: " ast)]))

    (define/public (interp-x86 env)
      (lambda (ast)
	(match ast
	   [(or `(var ,x) `(register ,x) `(stack-loc ,x))
	    (cond [(assq x env) => cdr]
		  [else (error "in interp-x86, undefined variable " x)])]
	   [`(int ,n) n]
	   [`(call _read_int) (cons (cons 'rax (read)) env)]
	   [`(add ,s ,d)
	    (let ([s ((send this interp-x86 env) s)] 
		  [d ((send this interp-x86 env) d)]
		  [x (get-name d)])
	      (cons (cons x (+ d s)) env))]
	   [`(sub ,s ,d)
	    (let ([s ((send this interp-x86 env) s)] 
		  [d ((send this interp-x86 env) d)]
		  [x (get-name d)])
	      (cons (cons x (- d s)) env))]
	   [`(neg ,d)
	    (let ([d ((send this interp-x86 env) d)]
		  [x (get-name d)])
	      (cons (cons x (- d)) env))]
	   [(or `(mov ,e (var ,x)) `(mov ,e (stack-loc ,x))
		`(mov ,e (register ,x)))
	    (let ([v ((send this interp-x86 env) e)])
	      (cons (cons x v) env))]
	   [`(program ,xs ,ss) 
	    (let loop ([env '()] [ss ss])
	      (cond [(null? ss)
		     (cond [(assq 'rax env) => cdr]
			   [else (error "in interp-x86, return rax absent")])]
		    [else
		     (loop ((send this interp-x86 env) (car ss)) (cdr ss))]))]
	   [else
	    (error "no match in interp-x86 S0 for " ast)]
	   )))

    )) ;; class interp-S0


(define interp-S1
  (class interp-S0
    (super-new)

    (define/override (interp-op op)
      (match op
         ['eq? eq?]
	 ['and (lambda (a b) (and a b))]
	 ['or (lambda (a b) (or a b))]
	 ['not not]
	 [else (super interp-op op)]))

    (define/override (interp-scheme env)
      (lambda (ast)
	(match ast
           [#t #t]
           [#f #f]
	   [`(if ,cnd ,thn ,els)
	    (if ((send this interp-scheme env) cnd)
		((send this interp-scheme env) thn)
		((send this interp-scheme env) els))]
	   [else
	    ((super interp-scheme env) ast)]
	   )))

    (define/override (interp-C env)
      (lambda (ast)
	(match ast
           [#t #t]
           [#f #f]
	   [`(if ,cnd ,thn ,els)
	    (if ((send this interp-C env) cnd)
		((send this seq-C env) thn)
		((send this seq-C env) els))]
	   [else
	    ((super interp-C env) ast)]
	   )))

    #;(define/override (interp-x86 env)
      (lambda (ast)
	(match ast
	   [ ]
	   )))
	    
    ));; class interp-S1
    

