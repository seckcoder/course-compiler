#lang racket
(require "utilities.rkt")
(provide interp-S0 interp-S1 interp-S2 interp-S3)

;; This (dynamically scoped) parameter is used for goto
(define program (make-parameter '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S0

(define interp-S0
  (class object%
    (super-new)

    (field (result (gensym 'result)))

    (define/public (primitives)
      (set '+ '- '* 'read))

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
	   [`(,op ,args ...) #:when (set-member? (send this primitives) op)
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
    ;; program  p  ::= (program (x ...) s ...)

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
	   [`(program ,xs ,ss ...)
	    (define env ((send this seq-C '()) ss))
	    (cond [(assq result env) => cdr]
		  [else (error "missing return statement")])]
	   [`(,op ,args ...) #:when (set-member? (send this primitives) op)
	    (apply (interp-op op) (map (send this interp-C env) args))]
	   [else
	    (error "no match in interp-C0 for " ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; psuedo-x86 and x86
    ;; s,d ::= (var x) | (int n) | (register r) | (stack-loc n)
    ;; i   ::= (mov s d) | (add s d) | (sub s d) | (neg d) | (call f)
    ;; psuedo-x86 ::= (program (x ...) i ...)

    (define/public (get-name ast)
      (match ast
         [(or `(var ,x) `(register ,x) `(stack-loc ,x))
	  x]
	 [else
	  (error "doesn't have a name: " ast)]))

    (define/public (interp-x86-op op)
      (match op
	 ['add +]
	 ['sub -]
	 ['neg -]
	 ['mul *]
	 [else (error "interp-x86-op, unmatched" op)]))

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
	   [`((call _malloc) . ,ss)
	    (define num-bytes ((send this interp-x86 env) '(register rdi)))
	    (define vec (make-vector (/ num-bytes 8)))
	    (define new-env (cons (cons 'rax vec) env))
	    ((send this interp-x86 new-env) ss)]
	   [`((mov ,s ,d) . ,ss)
	    (define x (send this get-name d))
	    (define v ((send this interp-x86 env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`(program ,xs ,ss ...) 
	    (let ([env ((send this interp-x86 '()) ss)])
	      (cond [(assq 'rax env) => cdr]
		    [else (error "in interp-x86, return rax absent")]))]
	   [`((,binary-op ,s ,d) . ,ss)
	    (let ([s ((send this interp-x86 env) s)] 
		  [d ((send this interp-x86 env) d)]
		  [x (get-name d)]
		  [f (send this interp-x86-op binary-op)])
	      ((send this interp-x86 (cons (cons x (f d s)) env)) ss))]
	   [`((,unary-op ,d) . ,ss)
	    (let ([d ((send this interp-x86 env) d)]
		  [x (get-name d)]
		  [f (send this interp-x86-op unary-op)])
	      ((send this interp-x86 (cons (cons x (f d)) env)) ss))]
	   [else (error "no match in interp-x86 S0 for " ast)]
	   )))

    )) ;; class interp-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S1

(define interp-S1
  (class interp-S0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'eq? 'and 'or 'not)))

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
	   [else ((super interp-scheme env) ast)]
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
	   [else ((super interp-C env) ast)]
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

    (define (i2b i)
      (cond [(eq? i 0) #f]
	    [else #t]))

    (define (b2i b)
      (cond [b 1]
	    [else 0]))

    (define/override (interp-x86-op op)
      (match op
	 ['not not]
	 ['and (lambda (a b) (b2i (and (i2b a) (i2b b))))]
	 ['or (lambda (a b) (b2i (or (i2b a) (i2b b))))]
	 [else (super interp-x86-op op)]))

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
	      ((send this interp-x86 (cons (cons '__flag 
						 (b2i (eq? v1 v2))) 
					   env))
	       ss))]
	   [`((jmp ,label) . ,ss)
	    ((send this interp-x86 env) (goto-label label (program)))]
	   [`((je ,label) . ,ss)
	    (let ([flag (cond [(assq '__flag env) => (lambda (p) (cdr p))]
			      [else (error "flag not set before je")])])
	      (cond [(i2b flag)
		     ((send this interp-x86 env) (goto-label label (program)))]
		    [else ((send this interp-x86 env) ss)]))]
	   [`(program ,xs ,ss ...)
	    (parameterize ([program ss])
	     ((super interp-x86 '()) ast))]
	   [else ((super interp-x86 env) ast)]
	   )))
	    
    ));; class interp-S1
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S2

(define interp-S2
  (class interp-S1
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'vector 'vector-ref 'vector-set!)))

    (define/override (interp-op op)
      (match op
         ['vector vector]
	 ['vector-ref vector-ref]
	 ['vector-set! vector-set!]
	 [else (super interp-op op)]))

    (define/override (interp-x86 env)
      (lambda (ast)
	(match ast
	   [`(offset ,s ,i)
	    (define vec ((send this interp-x86 env) s))
	    (vector-ref vec i)]
	   [`((mov ,s (offset ,d ,i)) . ,ss)
	    (define v ((send this interp-x86 env) s))
	    (define vec ((send this interp-x86 env) d))
	    (debug "vector-set!" (list vec i v))
	    (vector-set! vec i v)
	    ((send this interp-x86 env) ss)]
	   [else ((super interp-x86 env) ast)]
	   )))

    ));; interp-S2

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S3


(define interp-S3
  (class interp-S2
    (super-new)
    (inherit-field result)

    (define/override (interp-scheme env)
      (lambda (ast)
	(match ast
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (cons f `(lambda ,xs ,body))]
	   [`(,f ,args ...) #:when (assq f env)
	    (define new-args (map (send this interp-scheme env) args))
	    (match (cdr (assq f env))
	       [`(lambda (,xs ...) ,body)
		((send this interp-scheme (map cons xs new-args)) body)]
	       [else (error "interp-scheme, expected a funnction, not" 
			    (cdr (assq f env)))])]
	   [`(program ,ds ... ,body)
	    (define new-env (map (send this interp-scheme '()) ds))
	    ((send this interp-scheme new-env) body)]
	   [else ((super interp-scheme env) ast)]
	   )))

    (define/override (interp-C env)
      (lambda (ast)
	(match ast
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
	    (cons f `(lambda ,xs ,@ss))]
	   [`(,f ,args ...) #:when (assq f env)
	    (define new-args (map (send this interp-C env) args))
	    (match (cdr (assq f env))
	       [`(lambda (,xs ...) ,ss ...)
		(define result-env
		  ((send this seq-C (map cons xs new-args)) ss))
		(cond [(assq result result-env) => cdr]
		  [else (error "missing return statement")])]
	       [else (error "interp-C, expected a funnction, not" 
			    (cdr (assq f env)))])]
	   [`(program ,locals ,ds ,ss ...)
	    (define new-env (map (send this interp-C '()) ds))
	    (define result-env ((send this seq-C new-env) ss))
	    (cond [(assq result result-env) => cdr]
		  [else (error "missing return statement")])]
	   [else ((super interp-C env) ast)]
	   )))

    (define (stack-arg-name n)
      (string->symbol (string-append "rsp_" (number->string n))))

    (define/public (builtin-funs) 
      (set '_malloc '_read_int))

    (define/override (get-name ast)
      (match ast
         [`(stack-arg ,n) (stack-arg-name n)]
	 [else (super get-name ast)]
	 ))

    (define/override (interp-x86 env)
      (lambda (ast)
	(match ast
	   [`(stack-arg ,n)
	    (define x (stack-arg-name n))
	    (cond [(assq x env) => cdr]
		  [else (error "in interp-x86, undefined variable " x)])]
	   [`(define (,f) ,n ,extra ,ss ...)
	    (cons f `(lambda ,n ,@ss))]
	   [`((call ,f) . ,ss) 
	    #:when (not (set-member? (send this builtin-funs) f))
	    (match (cdr (assq f env))
	       [`(lambda ,n ,body-ss ...)
		;; copy some register and stack locations over to new-env
		(define passing-regs (for/list ([r arg-registers])
					       (assq r env)))
		(define passing-stack
		  (for/list ([i (in-range 
				 0 (max 0 (- n (vector-length
						arg-registers))))])
			    (define name (stack-arg-name (* i 8)))
			    (define val
			      (cond [(assq name env) => cdr]
				    [else (error "undefined" name)])) 
			    (define index (- (+ 16 (* i 8))))
			    (cons index val)))
		(debug "passing stack" passing-stack)
		(define new-env (append passing-regs passing-stack))
		(define result-env
		  (parameterize ([program body-ss])
		     ((send this interp-x86 new-env) body-ss)))
		(define res (cond [(assq 'rax result-env) => cdr]
				  [else (error "missing rax for return")]))
		((send this interp-x86 (cons (cons 'rax res) env)) ss)]
	       [else (error "interp-x86, expected a funnction, not" 
			    (cdr (assq f env)))])
	    ]
	   [`(program ,extra ,ds ,ss ...)
	    (parameterize ([program ss])
	       (define env (map (send this interp-x86 '()) ds))
	       (define result-env ((send this interp-x86 env) ss))
	       (cond [(assq 'rax result-env) => cdr]
		     [else (error "missing rax for return")]))]
	   [else ((super interp-x86 env) ast)]
	   )))


    ));; interp-S3
