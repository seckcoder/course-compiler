#lang racket
(require "functions.rkt")
(require "interp.rkt")
(provide compile-S4 lambda-passes)

(define compile-S4
  (class compile-S3
    (super-new)

    ;; from `functions.rkt`
    ;; - where is `primitives` defined?
    ;; - do I even need to include this?
    (define/public (non-apply-ast)
      (set-union (send this primitives)
        	 (set 'if 'let 'define 'program)))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S4 -> S4

    ;; How do I test just this? Is there a way?
    (define/override (type-check env)
      (lambda (e)
        (match e
          [`(,e ,e* ...) #:when (not (set-member? (send this non-apply-ast) e))
           (define ran-type* (map (send this type-check env) e*))
           (define rat-type ((send this type-check env) e))
           (match rat-type
             [`(,fml* ... -> ,rT)
              (unless (equal? ran-type* fml*)
                (error "function ~a expected ~a, given ~a" e ran-type* fml*))
              rT]
             [else (error "expected a function, not" e)])]
          [`(lambda: ([,x : ,T] ...) : ,rT ,body)
           ((send this type-check (append (map cons x T) env)) body)]
          ;; other ASTs handled by super-class (hopefully)
          [else ((super type-check env) e)]
          )))

    ;; - What do I have to uniquify for first-class functions?
    ;; - would it be beneficial to just list first-class functions into `define`s now?
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lift-lambda : env -> S4 -> S3
    (define/public (lift-lambda env)
      (lambda (e)
        (match e
          [`(,f ,arg* ...) #:when (not (set-member? (send this non-apply-ast) e))
           (define new-f )]
          [`(lambda ([,x : ,T] ...) : ,rT ,body) ...]
          [`(program ,d* ... ,body)]
          )))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define lambda-passes
  (let ([compiler (new compile-S4)]
        [interp (new interp-S4)])
    (list 5)))
