#lang racket
(require racket/set)
(require "utilities.rkt")
(require "lambda.rkt")

(provide compile-R6 compile-R7 R6-passes R6-typechecker R7-passes R7-typechecker)

(define compile-R6
  (class compile-R4
    (super-new)

    (define type-predicates (set 'boolean? 'integer? 'vector? 'procedure?))

    (define/override (primitives)
      (set-union (super primitives) 
		 type-predicates
		 (set 'inject 'project)
		 ))

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
	  [`(,pred ,e) #:when (set-member pred type-predicates)
	   (define-values (new-e e-ty) ((type-check env) e))
	   (cond
	    [(equal? e-ty 'Any)
	     (values `(has-type (,pred ,new-e) Boolean) 'Boolean)]
	    [else
	     (error "type predicate expected argument of type Any, not" e-ty)])]
	  [else
	   ((super type-check env) e)]
	  )))

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

    (define/override (select-instructions)
      (lambda (e)
	(match e
          [`(assign ,lhs (inject ,e ,ty))
           (define new-lhs ((send this select-instructions) lhs))
	   (define new-e ((send this select-instructions) e))
	   (cond [(or (equal? ty 'Integer) (equal? ty 'Boolean))
		  `((movq ,new-e ,new-lhs)
		    (salq (int 2) ,new-lhs)
		    (orq (int ,(any-tag ty)) new-lhs))]
		 [else
		  `((movq ,new-e ,new-lhs)
		    (orq (int ,(any-tag ty)) new-lhs))])]
          [`(assign ,lhs (project ,e ,ty))
           (define new-lhs ((send this select-instructions) lhs))
	   (define new-e ((send this select-instructions) e))
	   `((movq ,new-e ,new-lhs)
	     (andq (int ,any-mask) ,new-lhs)
	     (if (eq? ,new-lhs (int ,(any-tag ty)))
		 ((andq (int ,pointer-mask) ,new-lhs)
		  (if (eq? ,new-lhs (int ,pointer-mask))
		      ;; vectors and procedures. This needs work to handle length and arity. -Jeremy
		      ((movq (int ,any-mask) ,new-lhs)
		       (notq ,new-lhs)
		       (andq  ,new-e ,new-lhs))
		      ;; booleans and integers
		      ((movq ,new-e ,new-lhs)
		       (sarq (int 2) ,new-lhs))
		      ))
		 ((callq ,(label-name "exit")))))]
	  [`(assign ,lhs (,pred ,e)) #:when (set-member pred type-predicates)
           (define new-lhs ((send this select-instructions) lhs))
	   (define new-e ((send this select-instructions) e))
	   `((movq ,new-e ,new-lhs)
	     (andq (int ,any-mask) ,new-lhs)
	     (cmpq ,(pred->tag pred) ,new-lhs)
	     (sete (byte-reg al))
	     (movzbq (byte-reg al) ,new-lhs))]
	  [else ((super select-instructions) e)]
	  )))
    
    ))
