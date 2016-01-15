#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(provide interp-scheme interp-C interp-x86 interp-S0 interp-S1 interp-S2 interp-S3 interp-S4 )

(define interp-scheme
  (lambda (p)
    ((send (new interp-S4) interp-scheme '()) p)))

(define interp-C
  (lambda (p)
    ((send (new interp-S4) interp-C '()) p)))

(define interp-x86
  (lambda (p)
    ((send (new interp-S4) interp-x86 '()) p)))

;; This (dynamically scoped) parameter is used for goto
(define program (make-parameter '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S0: integer arithmetic and 'let'

(define interp-S0
  (class object%
    (super-new)

    (field (result (gensym 'result)))

    (define/public (primitives)
      (set '+ '- 'read))

    (define/public (interp-op op)
      (match op
         ['+ fx+]
	 ['- (lambda (n) (fx- 0 n))]
	 ['read read-fixnum]
	 [else (error "in interp-op S0, unmatched" op)]))

    (define/public (interp-scheme env)
      (lambda (ast)
	(match ast
           [(? symbol?)
	    (lookup ast env)]
	   [(? integer?) ast]
	   [`(let ([,x ,e]) ,body)
	    (let ([v ((send this interp-scheme env) e)])
	      ((send this interp-scheme (cons (cons x v) env)) body))]
	   [`(program ,e) ((send this interp-scheme '()) e)]
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
        (debug "interp-C0" ast)
	(match ast
           [(? symbol?)
	    (lookup ast env)]
	   [(? integer?) ast]
	   [`(assign ,x ,e)
	    (let ([v ((send this interp-C env) e)])
	      (cons (cons x v) env))]
	   [`(return ,e)
	    (let ([v ((send this interp-C env) e)])
	      (cons (cons result v) env))]
	   [`(program ,xs ,ss ...)
	    (define env ((send this seq-C '()) ss))
	    (lookup result env)]
	   [`(,op ,args ...) #:when (set-member? (send this primitives) op)
	    (apply (interp-op op) (map (send this interp-C env) args))]
	   [else
	    (error "no match in interp-C0 for " ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; psuedo-x86 and x86
    ;; s,d ::= (var x) | (int n) | (reg r) | (stack n)
    ;; i   ::= (movq s d) | (addq s d) | (subq s d) | (imulq s d) 
    ;;       | (negq d) | (callq f)
    ;; psuedo-x86 ::= (program (x ...) i ...)

    (define/public (get-name ast)
      (match ast
         [(or `(var ,x) `(reg ,x) `(stack ,x))
	  x]
	 [else
	  (error "doesn't have a name: " ast)]))

    (define/public (interp-x86-op op)
      (match op
	 ['addq +]
	 ['subq -]
	 ['negq -]
	 [else (error "interp-x86-op, unmatched" op)]))

    (define/public (interp-x86-exp env)
      (lambda (ast)
	(match ast
	   [(or `(var ,x) `(reg ,x) `(stack ,x))
            (lookup x env)]
	   [`(int ,n) n]
	   [else
	    (error "interp-x86-exp, unhandled" ast)])))

    (define/public (interp-x86 env)
      (lambda (ast)
	(match ast
	   ['()
	    env]
	   [`((callq read_int) . ,ss) 
	    ((send this interp-x86 (cons (cons 'rax (read)) env)) ss)]
	   [`((callq malloc) . ,ss)
	    (define num-bytes ((send this interp-x86-exp env) '(reg rdi)))
	    (define vec (make-vector (/ num-bytes 8)))
	    (define new-env (cons (cons 'rax vec) env))
	    ((send this interp-x86 new-env) ss)]
           [`((callq alloc) . ,ss)
	    (define num-bytes ((send this interp-x86-exp env) '(reg rdi)))
	    (define vec (make-vector (/ num-bytes 8)))
	    (define new-env (cons (cons 'rax vec) env))
	    ((send this interp-x86 new-env) ss)]
           [`((callq initialize) . ,ss)
            ;; Could do some work here if we decide to lower the
            ;; representation of vectors for this interpreter. 
            ((send this interp-x86 env) ss)]
	   [`((movq ,s ,d) . ,ss)
	    (define x (send this get-name d))
	    (define v ((send this interp-x86-exp env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`(program ,xs ,ss ...) 
	    (let ([env ((send this interp-x86 '()) ss)])
	      (lookup 'rax env))]
	   [`((,binary-op ,s ,d) . ,ss)
	    (let ([s ((send this interp-x86-exp env) s)] 
		  [d ((send this interp-x86-exp env) d)]
		  [x (send this get-name d)]
		  [f (send this interp-x86-op binary-op)])
	      ((send this interp-x86 (cons (cons x (f d s)) env)) ss))]
	   [`((,unary-op ,d) . ,ss)
	    (let ([d ((send this interp-x86-exp env) d)]
		  [x (send this get-name d)]
		  [f (send this interp-x86-op unary-op)])
	      ((send this interp-x86 (cons (cons x (f d)) env)) ss))]
	   [else (error "no match in interp-x86 S0 for " ast)]
	   )))

    )) ;; class interp-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S1: Booleans and conditionals

(define interp-S1
  (class interp-S0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'eq? 'and 'or 'not)))

    (define/override (interp-op op)
      (match op
         ['eq? (lambda (v1 v2)
                 (cond [(and (fixnum? v1) (fixnum? v2)) (eq? v1 v2)]
                       [(and (boolean? v1) (boolean? v2)) (eq? v1 v2)]))]
         ['not (lambda (v) (match v [#t #f] [#f #t]))]
	 ['and (lambda (v1 v2)
		 (cond [(and (boolean? v1) (boolean? v2))
			(and v1 v2)]))]
	 [else (super interp-op op)]))

    (define/override (interp-scheme env)
      (lambda (ast)
	(match ast
           [#t #t]
           [#f #f]
	   [`(and ,e1 ,e2)
	    (match ((send this interp-scheme env) e1)
	      [#t (match ((send this interp-scheme env) e2)
		    [#t #t] [#f #f])]
              [#f #f])]
	   [`(if ,cnd ,thn ,els)
	    (if ((send this interp-scheme env) cnd)
		((send this interp-scheme env) thn)
		((send this interp-scheme env) els))]
           [else ((super interp-scheme env) ast)]
	   )))

    (define/override (interp-C env)
      (lambda (ast)
	(debug "interp-C1" ast)
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
	 [`(byte-reg ,r)
	  (super get-name `(reg ,(byte2full-reg r)))]
	 [else (super get-name ast)]))

    (define (i2b i)
      (cond [(eq? i 0) #f]
	    [else #t]))

    (define (b2i b)
      (cond [b 1]
	    [else 0]))

    (define/override (interp-x86-op op)
      (match op
	 ['notq not]
	 ['andq (lambda (a b) (b2i (and (i2b a) (i2b b))))]
	 [else (super interp-x86-op op)]))

    (define/override (interp-x86-exp env)
      (lambda (ast)
	(match ast
	   [`(byte-reg ,r)
	    ((send this interp-x86-exp env) `(reg ,(byte2full-reg r)))]
           [#t 1]
           [#f 0]
	   [else ((super interp-x86-exp env) ast)]
	   )))

    (define/override (interp-x86 env)
      (lambda (ast)
	(match ast
	   [`((sete ,d) . ,ss)
	    (let ([v ((send this interp-x86-exp env) '(reg __flag))]
		  [x (send this get-name d)])
	      ((send this interp-x86 (cons (cons x v) env)) ss))]
	   ;; if's are present before patch-instructions
	   [(or `((if ,cnd ,thn ,els) . ,ss)
		`((if ,cnd ,thn ,_ ,els ,_) . ,ss))
	    (if (not (eq? 0 ((send this interp-x86-exp env) cnd)))
		((send this interp-x86 env) (append thn ss))
		((send this interp-x86 env) (append els ss)))]
	   [`((label ,l) . ,ss)
	    ((send this interp-x86 env) ss)]
	   [`((cmpq ,s1 ,s2) . ,ss)
	    (let ([v1 ((send this interp-x86-exp env) s1)] 
		  [v2 ((send this interp-x86-exp env) s2)])
	      ((send this interp-x86 (cons (cons '__flag 
						 (b2i (eq? v1 v2))) 
					   env))
	       ss))]
	   [`((movzbq ,s ,d) . ,ss)
	    (define x (send this get-name d))
	    (define v ((send this interp-x86-exp env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`((jmp ,label) . ,ss)
	    ((send this interp-x86 env) (goto-label label (program)))]
	   [`((je ,label) . ,ss)
	    (let ([flag (lookup '__flag env)])
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
;; Interpreters for S2: Vectors

(define interp-S2
  (class interp-S1
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'vector 'vector-ref 'vector-set!)))

    (define/override (interp-op op)
      (match op
         ['eq? (lambda (v1 v2)
                 (cond [(or (and (fixnum? v1) (fixnum? v2)) 
			    (and (boolean? v1) (boolean? v2))
			    (and (vector? v1) (vector? v2)))
			(eq? v1 v2)]))]
         ['vector vector]
	 ['vector-ref vector-ref]
	 ['vector-set! vector-set!]
	 [else (super interp-op op)]))

    (define/override (interp-x86-exp env)
      (lambda (ast)
	(match ast
	   [`(offset ,s ,i)
	    (define vec ((send this interp-x86-exp env) s))
	    (vector-ref vec (/ i 8))]
	   [else ((super interp-x86-exp env) ast)]
	   )))

    (define/override (interp-x86 env)
      (lambda (ast)
	(match ast
	   [`((movq ,s (offset ,d ,i)) . ,ss)
	    (define v ((send this interp-x86-exp env) s))
	    (define vec ((send this interp-x86-exp env) d))
	    (vector-set! vec (/ i 8) v)
	    ((send this interp-x86 env) ss)]
	   [else ((super interp-x86 env) ast)]
	   )))

    ));; interp-S2

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S3: functions


(define interp-S3
  (class interp-S2
    (super-new)
    (inherit-field result)

    (define/public (non-apply-ast)
      (set-union (send this primitives)
		 (set 'if 'let 'define 'program)))

    (define/override (interp-scheme env)
      (lambda (ast)
	(match ast
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (cons f `(lambda ,xs ,body))]
	   [`(function-ref ,f)
	    (lookup f env)]
	   [`(app ,f ,args ...)
	    (define new-args (map (send this interp-scheme env) args))
	    (let ([f-val ((send this interp-scheme env) f)])
	      (match f-val
	         [`(lambda (,xs ...) ,body)
		  (define new-env (append (map cons xs new-args) env))
		  ((send this interp-scheme new-env) body)]
		 [else (error "interp-scheme, expected function, not" f-val)]))]
	   [`(program ,ds ... ,body)
	    (let ([top-level (map  (send this interp-scheme '()) ds)])
	      ((send this interp-scheme top-level) body))]
	    #;(let loop ([ds ds] [new-env '()])
	      (cond [(null? ds)
		     ((send this interp-scheme new-env) body)]
		    [else
		     (loop (cdr ds)
			   (cons ((send this interp-scheme new-env) (car ds))
				 new-env))]))
	   [`(,f ,args ...) #:when (not (set-member?
					 (send this non-apply-ast) f))
	    ((send this interp-scheme env) `(app ,f ,@args))]
	   [else ((super interp-scheme env) ast)]
	   )))

    (define/override (interp-C env)
      (lambda (ast)
	(debug "interp-C2" ast)
	(match ast
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
	    (cons f `(lambda ,xs ,@ss))]
	   [`(function-ref ,f)
	    (lookup f env)]
	   [`(app ,f ,args ...)
	    (define new-args (map (send this interp-C env) args))
	    (define f-val ((send this interp-C env) f))
	    (match f-val
	       [`(lambda (,xs ...) ,ss ...)
		(define new-env (append (map cons xs new-args) env))
		(define result-env ((send this seq-C new-env) ss))
		(lookup result result-env)]
	       [else (error "interp-C, expected a funnction, not" f-val)])]
	   [`(program ,locals (defines ,ds) ,ss ...)
	    (define new-env (map (send this interp-C '()) ds))
	    (define result-env ((send this seq-C new-env) ss))
	    (lookup result result-env)]
	   [else ((super interp-C env) ast)]
	   )))

    (define (stack-arg-name n)
      (string->symbol (string-append "rsp_" (number->string n))))

    (define/public (builtin-funs) 
      (set 'alloc 'malloc 'initialize 'read_int))

    (define/override (get-name ast)
      (match ast
         [`(stack-arg ,n) (stack-arg-name n)]
	 [else (super get-name ast)]
	 ))

    (define (call-function f-val ss env)
      (match f-val
	 [`(lambda ,n ,body-ss ...)
	  ;; copy some register and stack locations over to new-env
	  (define passing-regs
	    (filter (lambda (p) p) (for/list ([r arg-registers])
					     (assq r env))))
	  (define passing-stack
	    (for/list ([i (in-range 
			   0 (max 0 (- n (vector-length
					  arg-registers))))])
		      (define name (stack-arg-name (* i 8)))
		      (define val (lookup name env))
		      (define index (- (+ 16 (* i 8))))
		      (cons index val)))
	  (define new-env (append passing-regs passing-stack env))
	  (define result-env
	    (parameterize ([program body-ss])
			  ((send this interp-x86 new-env) body-ss)))
	  (define res (lookup 'rax result-env))
	  ((send this interp-x86 (cons (cons 'rax res) env)) ss)]
	 [else (error "interp-x86, expected a function, not" f-val)]))
      
    (define/override (interp-x86-exp env)
      (lambda (ast)
	(match ast
	   [`(stack-arg ,n)
	    (define x (stack-arg-name n))
	    (lookup x env)]
	   [`(function-ref ,f)
	    (lookup f env)]
	   [else ((super interp-x86-exp env) ast)]
	   )))

    (define/override (interp-x86 env)
      (lambda (ast)
	(if (pair? ast)
	    (debug "interp-x86" (car ast))
	    '())
	(match ast
	   [`(define (,f) ,n ,extra ,ss ...)
	    (cons f `(lambda ,n ,@ss))]
	   ;; Treat lea like mov -Jeremy
	   [`((leaq ,s ,d) . ,ss)
	    (define x (send this get-name d))
	    (define v ((send this interp-x86-exp env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`((indirect-callq ,f) . ,ss)
	    (define f-val ((send this interp-x86-exp env) f))
	    (call-function f-val ss env)]
	   [`((callq ,f) . ,ss) #:when (not (set-member? (send this builtin-funs) f))
	    (call-function (lookup f env) ss env)]
	   [`(program ,extra (defines ,ds) ,ss ...)
	    (parameterize ([program ss])
	       (define env (map (send this interp-x86 '()) ds))
	       (define result-env ((send this interp-x86 env) ss))
	       (lookup 'rax result-env))]
	   [else ((super interp-x86 env) ast)]
	   )))


    ));; interp-S3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S4: lambda

(define interp-S4
  (class interp-S3
    (super-new)
    (inherit-field result)

    (define/override (interp-scheme env)
      (lambda (ast)
	(match ast
	   [`(lambda: ([,xs : ,Ts] ...) : ,rT ,body)
	    `(lambda ,xs ,body ,env)]
	   [`(app ,f ,args ...)
	    (define new-args (map (send this interp-scheme env) args))
	    (let ([f-val ((send this interp-scheme env) f)])
	      (match f-val
	         [`(lambda (,xs ...) ,body ,lam-env)
		  (define new-env (append (map cons xs new-args) lam-env))
		  ((send this interp-scheme new-env) body)]
		 [else (error "interp-scheme, expected function, not" f-val)]))]
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (mcons f `(lambda ,xs ,body))]
	   [`(program ,ds ... ,body)
	    (let ([top-level (map (send this interp-scheme '()) ds)])
	      ;; Use set-cdr! on define lambda's for mutual recursion
	      (for/list ([b top-level])
			(set-mcdr! b (match (mcdr b)
				       [`(lambda ,xs ,body)
					`(lambda ,xs ,body ,top-level)])))
	      ((send this interp-scheme top-level) body))]
	   [else ((super interp-scheme env) ast)]
	   )))

    )) ;; interp-S4


 
