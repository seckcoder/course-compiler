#lang racket
(require "utilities.rkt")
(provide interp-S0 interp-S1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S0
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

    (define/public (get-name ast)
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
	   ['()
	    env]
	   [`((call _read_int) . ,ss) 
	    ((send this interp-x86 (cons (cons 'rax (read)) env)) ss)]
	   [`((add ,s ,d) . ,ss)
	    (let ([s ((send this interp-x86 env) s)] 
		  [d ((send this interp-x86 env) d)]
		  [x (get-name d)])
	      ((send this interp-x86 (cons (cons x (+ d s)) env)) ss))]
	   [`((sub ,s ,d) . ,ss)
	    (let ([s ((send this interp-x86 env) s)] 
		  [d ((send this interp-x86 env) d)]
		  [x (get-name d)])
	      ((send this interp-x86 (cons (cons x (- d s)) env)) ss))]
	   [`((neg ,d) . ,ss)
	    (let ([d ((send this interp-x86 env) d)]
		  [x (get-name d)])
	      ((send this interp-x86 (cons (cons x (- d)) env)) ss))]
	   [(or `((mov ,e (var ,x)) . ,ss) 
		`((mov ,e (stack-loc ,x)) . ,ss)
		`((mov ,e (register ,x)) . ,ss))
	    (let ([v ((send this interp-x86 env) e)])
	      ((send this interp-x86 (cons (cons x v) env)) ss))]
	   [`(program ,xs ,ss) 
	    (let ([env ((send this interp-x86 '()) ss)])
	      (cond [(assq 'rax env) => cdr]
		    [else (error "in interp-x86, return rax absent")]))]
	   [else
	    (error "no match in interp-x86 S0 for " ast)]
	   )))

    )) ;; class interp-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

    (define (goto-label label ss)
      (cond [(null? ss)
	     (error "goto-label, couldn't find label" label)]
	    [else
	     (match (car ss)
		[`(label ,l) #:when (eq? l label)
		 (cdr ss)]
		[else
		 (goto-label label (cdr ss))])]))

    (define program (make-parameter '()))

    (define byte2full-reg
      (lambda (r)
	(match r
	   ['al 'rax]
	   ['bl 'rbx]
	   ['cl 'rcx]
	   ['dl 'rdx]
	   )))

    (define/override (get-name ast)
      (match ast
	 [`(byte-register ,r)
	  (super get-name `(register ,(byte2full-reg r)))]
	 [else (super get-name ast)]))

    (define/override (interp-x86 env)
      (lambda (ast)
	(match ast
	   [`(byte-register ,r)
	    ((send this interp-x86 env) `(register ,(byte2full-reg r)))]
	   [`((sete ,d) . ,ss)
	    (let ([v ((send this interp-x86 env) '(register __flag))]
		  [d ((send this interp-x86 env) d)]
		  [x (send this get-name d)])
	      ((send this interp-x86 (cons (cons x v) env)) ss))]
           [#t 1]
           [#f 0]
	   ;; if's are present before insert-spill-code
	   [(or `((if ,cnd ,thn ,els) . ,ss)
		`((if ,cnd ,thn ,_ ,els ,_) . ,ss))
	    (if (not (eq? 0 ((send this interp-x86 env) cnd)))
		((send this interp-x86 env) (append thn ss))
		((send this interp-x86 env) (append els ss)))]
	   [`((label ,l) . ,ss)
	    ((send this interp-x86 env) ss)]
	   [`((cmp ,s1 ,s2) . ,ss)
	    (let ([v1 ((send this interp-x86 env) s1)] 
		  [v2 ((send this interp-x86 env) s2)])
	      ((send this interp-x86 (cons (cons '__flag (equal? v1 v2)) env))
	       ss))]
	   [`((jmp ,label) . ,ss)
	    ((send this interp-x86 env) (goto-label label (program)))]
	   [`((je ,label) . ,ss)
	    (let ([flag (cond [(assq '__flag env) => (lambda (p) (cdr p))]
			      [else (error "flag not set before je")])])
	      (cond [flag 
		     ((send this interp-x86 env) (goto-label label (program)))]
		    [else ((send this interp-x86 env) ss)]))]
	   [`(program ,xs ,ss) 
	    (parameterize ([program ss])
	     ((super interp-x86 '()) ast))]
	   [else
	    ((super interp-x86 env) ast)]
	   )))
	    
    ));; class interp-S1
    

