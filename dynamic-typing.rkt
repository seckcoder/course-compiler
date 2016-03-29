#lang racket
(require racket/set)
(require "utilities.rkt")
(require "interp.rkt")
(require "dynamic-interp.rkt")
(require "lambda.rkt")

(provide compile-R6 R6-passes R6-typechecker R7-passes)

(define compile-R6
  (class compile-R4
    (super-new)

    (define type-predicates (set 'boolean? 'integer? 'vector? 'procedure?))

    (define/override (primitives)
      (set-union (super primitives) 
		 type-predicates
		 (set 'inject 'project)
		 ))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check

    (define/override (type-check env)
      (lambda (e)
        (match e
          [`(vector-ref ,(app (type-check env) e t) ,i)
           (match t
             [`(Vector ,ts ...)
              (unless (and (exact-nonnegative-integer? i)
                           (i . < . (length ts)))
                (error 'type-check "invalid index ~a" i))
              (let ([t (list-ref ts i)])
                (values `(has-type (vector-ref ,e (has-type ,i Integer)) ,t) t))]
             [`(Vectorof ,t)
              (unless (exact-nonnegative-integer? i)
                (error 'type-check "invalid index ~a" i))
              (values `(has-type (vector-ref ,e (has-type ,i Integer)) ,t) t)]
             [else (error "expected a vector in vector-ref, not" t)])]
          [`(vector-set! ,e-vec ,i ,e-arg) 
           (define-values (e-vec^ t-vec) ((type-check env) e-vec))
           (define-values (e-arg^ t-arg) ((type-check env) e-arg))
           (match t-vec
             [`(Vector ,ts ...)
              (unless (and (exact-nonnegative-integer? i)
                           (i . < . (length ts)))
                (error 'type-check "invalid index ~a" i))
              (unless (equal? (list-ref ts i) t-arg)
                (error 'type-check "type mismatch in vector-set! ~a ~a" 
                       (list-ref ts i) t-arg))
              (values `(has-type (vector-set! ,e-vec^
                                              (has-type ,i Integer)
                                              ,e-arg^) Void) 'Void)]
             [`(Vectorof ,t)
              (unless (exact-nonnegative-integer? i)
                (error 'type-check "invalid index ~a" i))
              (unless (equal? t t-arg)
                (error 'type-check "type mismatch in vector-set! ~a ~a" 
                       t t-arg))
              (values `(has-type (vector-set! ,e-vec^
                                              (has-type ,i Integer)
                                              ,e-arg^) Void) 'Void)]
             [else (error 'type-check
                          "expected a vector in vector-set!, not ~a"
                          t-vec)])]
          [`(inject ,e ,ty)
	   (define-values (new-e e-ty) ((type-check env) e))
	   (cond
	    [(equal? e-ty ty)
	     (values `(has-type (inject ,new-e ,ty) Any) 'Any)]
	    [else
	     (error "injected expression does not have expected type" e ty)])]
	  [`(project ,e ,ty)
	   (define-values (new-e e-ty) ((type-check env) e))
	   (cond
	    [(equal? e-ty 'Any)
	     (values `(has-type (project ,new-e ,ty) ,ty) ty)]
	    [else
	     (error "project expression does not have type Any" e)])]
	  [`(,pred ,e) #:when (set-member? type-predicates pred)
	   (define-values (new-e e-ty) ((type-check env) e))
	   (cond
	    [(equal? e-ty 'Any)
	     (values `(has-type (,pred ,new-e) Boolean) 'Boolean)]
	    [else
	     (error "type predicate expected argument of type Any, not" e-ty)])]
	  [else
	   ((super type-check env) e)]
	  )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify
    (define/override (uniquify env)
      (lambda (e)
	(match e
          [`(inject ,e ,ty)
	   `(inject ,((uniquify env) e) ,ty)]
	  [`(project ,e ,ty)
	   `(project ,((uniquify env) e) ,ty)]
	  [else ((super uniquify env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal-functions
    
    (define/override (reveal-functions funs)
      (lambda (e)
	(define recur (send this reveal-functions funs))
	(match e
          [`(inject ,e ,t)
	   `(inject ,(recur e) ,t)]
	  [`(project ,e ,t)
	   `(project ,(recur e) ,t)]
          [else ((super reveal-functions funs) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; convert-to-closures

    (define/override (free-variables e)
      (define (recur e) (send this free-variables e))
      (match e
        [(or `(inject ,e ,ty) `(project ,e ,ty))
	 (recur e)]
	[else (super free-variables e)]
	))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten

    (define/override (flatten need-atomic)
      (lambda (e)
        (verbose "flatten" e)
	(match e
          [`(has-type (inject ,e ,ty) ,ty2)
	   (define-values (new-e e-ss) ((send this flatten #t) e))
	   (cond [need-atomic
		  (define tmp (gensym 'tmp))
		  (values `(has-type ,tmp ,ty2)
			  (append e-ss `((assign ,tmp (has-type (inject ,new-e ,ty) ,ty2)))))]
		 [else
		  (values `(has-type (inject ,new-e ,ty) ,ty2) e-ss)])]
	  [`(has-type (project ,e ,ty) ,ty2)
	   (define-values (new-e e-ss) ((send this flatten #t) e))
	   (cond [need-atomic
		  (define tmp (gensym 'tmp))
		  (values `(has-type ,tmp ,ty2)
			  (append e-ss `((assign ,tmp (has-type (project ,new-e ,ty) ,ty2)))))]
		 [else
		  (values `(has-type (project ,new-e ,ty) ,ty2) e-ss)])]
	  [else
	   ((super flatten need-atomic) e)]
	  )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots

    (define/override (uncover-call-live-roots-exp e)
      (vomit "any/uncover-call-live-roots-exp" e)
      (match e 
        [`(inject ,e ,ty) (uncover-call-live-roots-exp e)]
        [`(project ,e ,ty) (uncover-call-live-roots-exp e)]
        [else (super uncover-call-live-roots-exp e)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions

    (define (any-tag ty)
      (match ty
	 ['Integer 0]
	 ['Void 0]
	 ['Boolean 1]
	 [`(Vector ,ts ...) 2]
	 [`(Vectorof ,t) 2]
	 [`(,ts ... -> ,rt) 3]
	 [else (error "in any-tag, unrecognized type" ty)]
	 ))

    (define pred->tag
      (lambda (pred)
	(match pred
	   ['integer? 0]
	   ['boolean? 1]
	   ['vector? 2]
	   ['procedure? 3]
	   [else (error "in pred->tag, unrecognized predicate" pred)]
	   )))

    (define any-mask 3)
    (define pointer-mask 2)

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'salq 'sarq)))

    (define/override (select-instructions)
      (lambda (e)
	(define recur (send this select-instructions))
	(match e
          [`(assign ,lhs (inject ,e ,ty))
           (define new-lhs (recur lhs))
	   (define new-e (recur e))
	   (cond [(or (equal? ty 'Integer) (equal? ty 'Boolean))
		  `((movq ,new-e ,new-lhs)
		    (salq (int 2) ,new-lhs)
		    (orq (int ,(any-tag ty)) ,new-lhs))]
		 [else
		  `((movq ,new-e ,new-lhs)
		    (orq (int ,(any-tag ty)) ,new-lhs))])]
          [`(assign ,lhs (project ,e ,ty))
           (define new-lhs (recur lhs))
	   (define new-e (recur e))
	   `((movq ,new-e ,new-lhs)
	     (andq (int ,any-mask) ,new-lhs)
	     (if (eq? ,new-lhs (int ,(any-tag ty)))
		 ((andq (int ,pointer-mask) ,new-lhs)
		  (if (eq? ,new-lhs (int ,pointer-mask))
		      ;; vectors and procedures.
		      ;; To do: check length of vector, arity of procedure. -Jeremy
		      ((movq (int ,any-mask) ,new-lhs)
		       (notq ,new-lhs)
		       (andq  ,new-e ,new-lhs))
		      ;; booleans and integers
		      ((movq ,new-e ,new-lhs)
		       (sarq (int 2) ,new-lhs))
		      ))
		 ((callq ,(string->symbol (label-name 'exit))))))]
	  [`(assign ,lhs (,pred ,e)) #:when (set-member? type-predicates pred)
           (define new-lhs (recur lhs))
	   (define new-e (recur e))
	   `((movq ,new-e ,new-lhs)
	     (andq (int ,any-mask) ,new-lhs)
	     (cmpq (int ,(pred->tag pred)) ,new-lhs)
	     (set e (byte-reg al))
	     (movzbq (byte-reg al) ,new-lhs))]
	  [else ((super select-instructions) e)]
	  )))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live

    (define/override (read-vars instr)
      (match instr
        [(or `(sarq ,s ,d) `(salq ,s ,d))
         (set-union (send this free-vars s) (send this free-vars d))]
        [else (super read-vars instr)]
	))

    (define/override (write-vars instr)
      (match instr
        [(or `(sarq ,s ,d) `(salq ,s ,d)) 
         (send this free-vars d)]
        [else (super write-vars instr)]))
	

    ))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; R7 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define compile-R7
  (class compile-R6
    (super-new)
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; cast-insert


    (define/public (cast-insert)
      (lambda (e)
        (match e
          [(? integer?) `(inject ,e Integer)]
          [(? symbol?) e]
          [`(read) `(inject (read) Integer)]
          [`(function-ref ,e ,n) `(inject (function-ref ,e) (,@(map (lambda (x) 'Any) (range n)) -> Any))]
          [`(+ ,e1 ,e2) `(inject (+ (project ,((cast-insert) e1) Integer) (project ,((cast-insert) e2) Integer)) Integer)]
          [`(- ,e) `(inject (- (project ,((cast-insert) e) Integer)) Integer)]
          [`(let ([,x ,e1]) ,e2) `(let ([,x ,((cast-insert) e1)]) ,((cast-insert) e2))]
          [#t `(inject #t Boolean)]
          [#f `(inject #f Boolean)]
          [`(and ,e1 ,e2) (let ([gen (gensym)])
                            `(let ([,gen ,((cast-insert) e1)])
                               (if (eq? ,gen (inject #f Boolean))
                                   ,gen
                                   ,((cast-insert) e2))))]
          [`(not ,e) `(inject (not (project ,((cast-insert) e) Boolean)) Boolean)]
          [`(eq? ,e1 ,e2) `(inject (eq? ,((cast-insert) e1),((cast-insert) e2)) Boolean)]
          [`(if ,eq ,et ,ef) `(if (eq? ,((cast-insert) eq) (inject #f Boolean)) ,((cast-insert) ef) ,((cast-insert) et))]
          [`(vector ,es ...) `(inject (vector ,@(map (cast-insert) es)) (Vector ,@(map (lambda (x) 'Any) es)))]
          [`(vector-ref ,e1 ,n) `(vector-ref (project ,((cast-insert) e1) (Vectorof Any)) ,n)]
          [`(vector-set! ,e1 ,n ,e2) `(inject (vector-set! (project ,((cast-insert) e1) (Vectorof Any)) ,n ,((cast-insert) e2)) Void)]
          [`(void) `(inject (void) Void)] ; ???
          [`(lambda (,xs ...) ,e) `(inject (lambda: (,@(map (lambda (x) `[,x : Any]) xs)) : Any ,((cast-insert) e)) (,@(map (lambda (x) 'Any) xs) -> Any))]
          [`(app ,e ,es ...) `(app (project ,((cast-insert) e) (,@(map (lambda (x) 'Any) es) -> Any)) ,@(map (cast-insert) es))]
          [`(define (,f ,xs ...) ,e) `(define (,f ,@(map (lambda (x) `[,x : Any]) xs)) : Any ,((cast-insert) e))]
          [`(program ,ds ... ,e) `(program ,@(map (cast-insert) ds) ,((cast-insert) e))])))
          
          

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check

   (define/override (type-check env)
      (lambda (e)
        (match e
          [`(function-ref ,e)
           (let ([t (lookup e env)])
             (values `(has-type (function-ref ,e) ,t) t))]
          [`(app ,e ,es ...)
           (define-values (e* ty*)
             (for/lists (e* ty*) ([e (in-list es)])
               ((type-check env) e)))
           (define-values (e^ ty)
             ((type-check env) e))
           (match ty
             [`(,ty^* ... -> ,rt)
              (unless (equal? ty* ty^*)
                (error "parameter and argument type mismatch for function" e))
              (vomit "app" e^ e* rt)
              (values `(has-type (app ,e^ ,@e*) ,rt) rt)]
             [else (error "expected a function, not" ty)])]
	  [else
	   ((super type-check env) e)]
	  )))


    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify
    (define/override (uniquify env)
      (lambda (e)
	(match e
          [`(define (,f ,xs ...) ,body)
           (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
           (define new-env (append (map cons xs new-xs) env))
           `(define (,(cdr (assq f env)) 
                     ,@new-xs) 
                     ,((uniquify new-env) body))]
          [`(program ,ds ... ,body)  #:when (or (null? ds) (not (eq? (caar ds) 'type)))
           (define new-env
             (for/list ([d ds])
               (match d
                 [`(define (,f ,xs ...) ,body)
                  (define new-f (gensym (racket-id->c-id f)))
                  `(,f . ,new-f)]
                 [else (error "type-check, ill-formed function def")])))
           `(program ,@(map (uniquify new-env) ds)
                     ,((uniquify new-env) body))]
          [`(lambda (,xs ...) ,body)
	   (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
	   (define new-env (append (map cons xs new-xs) env))
           `(lambda ,new-xs
              ,((uniquify new-env) body))]
	  [else ((super uniquify env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal-functions
    (define/override (fun-def-name d)
      (match d
        [`(define (,f ,xs ...) ,body)
         f]
        [else (super fun-def-name d)])) 
    
    (define/public (fun-def-arity d)
      (match d
        [`(define (,f ,xs ...) ,body)
         (length xs)]
        [else (error 'Syntax-Error "ill-formed function definition in ~a" d)]))

    (define/override (reveal-functions funs)
      (lambda (e)
	(define recur (send this reveal-functions funs))
	(match e
          [(? symbol?) #:when (or (null? funs) (pair? (car funs))) ; This is an arity-environment, meaning R7
           (cond
            [(lookup e funs #f) `(function-ref ,e ,(lookup e funs))]
            [else e])]
          ['(void) '(void)]
          [`(program ,ds ... ,body) #:when (or (null? ds) (not (eq? (caar ds) 'type)))
           (define funs 
             (for/list ([d ds]) 
               (cons (fun-def-name d) (fun-def-arity d))))
           `(program ,@(map (reveal-functions funs) ds)
                     ,((reveal-functions funs) body))]
          [`(define (,f ,params ...) ,body)
           `(define (,f ,@params) ,(recur body))]
          [`(lambda ,params ,body)
           `(lambda ,params ,(recur body))]
          [else ((super reveal-functions funs) e)])))


    ))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define R6-typechecker
  (let ([compiler (new compile-R6)])
    (send compiler type-check '())))
(define R6-passes
  (let ([compiler (new compile-R6)]
        [interp (new interp-R6)])
    `(
      ;("type-check" ,(send compiler type-check '())
      ; ,(send interp interp-scheme '()))
      ("uniquify" ,(send compiler uniquify '())
       ,(send interp interp-scheme '()))
      ("reveal-functions" ,(send compiler reveal-functions '())
       ,(send interp interp-scheme '()))
      ("convert-to-closures" ,(send compiler convert-to-closures)
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-C '()))
      ("uncover call live roots"
       ,(send compiler uncover-call-live-roots)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler build-interference
                                   (void) (void))
       ,(send interp interp-x86 '()))
      ("build move graph" ,(send compiler
                                 build-move-graph (void))
       ,(send interp interp-x86 '()))
      ("allocate registers" ,(send compiler allocate-registers)
       ,(send interp interp-x86 '()))
      ("lower conditionals" ,(send compiler lower-conditionals)
       ,(send interp interp-x86 '()))
      ("patch instructions" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ("print x86" ,(send compiler print-x86) #f)
      )))

(define R7-passes
  (let ([compiler (new compile-R7)]
        [interp (new interp-R6)])
    `(
      ("uniquify" ,(send compiler uniquify '())
       ,(interp-r7 '()))
      ("reveal-functions" ,(send compiler reveal-functions '())
       ,(interp-r7 '()))
      ("translate" ,(send compiler cast-insert)
       ,(send interp interp-scheme '()))
      ("inserthastype" ,(send compiler type-check '())
       ,(send interp interp-scheme '()))
      ("convert-to-closures" ,(send compiler convert-to-closures)
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-C '()))
      ("uncover call live roots"
       ,(send compiler uncover-call-live-roots)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler build-interference
                                   (void) (void))
       ,(send interp interp-x86 '()))
      ("build move graph" ,(send compiler
                                 build-move-graph (void))
       ,(send interp interp-x86 '()))
      ("allocate registers" ,(send compiler allocate-registers)
       ,(send interp interp-x86 '()))
      ("lower conditionals" ,(send compiler lower-conditionals)
       ,(send interp interp-x86 '()))
      ("patch instructions" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ("print x86" ,(send compiler print-x86) #f)
      )))
