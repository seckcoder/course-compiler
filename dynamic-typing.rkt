#lang racket
(require racket/set)
(require "utilities.rkt")
(require "interp.rkt")
(require "lambda.rkt")

(provide compile-R6 R6-passes R6-typechecker)

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
	 ['Boolean 1]
	 [`(Vector ,ts ...) 2]
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

    (define/override (select-instructions [rootstack #t])
      (lambda (e)
	(define recur (send this select-instructions rootstack))
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
		      ;; To do: check length and arity. -Jeremy
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
	     (cmpq ,(pred->tag pred) ,new-lhs)
	     (sete (byte-reg al))
	     (movzbq (byte-reg al) ,new-lhs))]
	  [else ((super select-instructions rootstack) e)]
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
