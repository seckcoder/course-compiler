#lang racket
(require "functions.rkt")
(require "interp.rkt")
(provide compile-S4 lambda-passes)

(define compile-S4
  (class compile-S3
    (super-new)
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S4 -> S4
    (define/override (type-check env)
      (lambda (e)
        (define (recur e) (send this type-check env))
        (match e
          [`(,e ,e* ...) #:when (not (set-member? (send this non-apply-ast) e))
           (define ran-type* (map recur e*))
           (define rat-type (recur e))
           (match rat-type
             [`(,fml* ... -> ,rT)
              (unless (equal? ran-type* fml*)
                (error "function ~a expected ~a, given ~a" e ran-type* fml*))
              rT]
             [else (error "expected a function, not" e)])]
          [`(lambda: ([,x : ,T] ...) : ,rT ,body)
           ((send this type-check (append (map cons x T) env)) body)]
          [else ((super type-check env) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lift-lambda : env -> S4 -> S3
    (define/public (lift-lambda env)
      (lambda (e)
        (define (recur e) (send this lift-lambda env))
        (match e
          [`((lambda ,fml* : ,rT ,body) ,arg*)
           (define abs-name (gensym))
           (define-values (new-b b-dep) (recur body))
           (values `(,abs-name ,@arg*) b-dep)]
          [`(lambda ,fml* : ,rT ,body)
           (define abs-name (gensym))
           (define-values (new-b b-dep) (recur body))
           (values `(define (,abs-name ,@fml*) : ,rT ,new-b) b-dep)]
          [`(define (,f ,fml ...) : ,rT ,body)
           (define-values (new-b b-dep) (recur body))
           (values `(define (,f ,@fml) : ,rT ,new-b) b-dep)]
          [`(program ,d ... ,body)
           (define-values (new-d d-dep) (map recur d))
           (define-values (new-b b-dep) (recur body))
           (define final-ds (append d-dep b-dep new-d))
           `(program ,final-ds new-b)]
          )))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define lambda-passes
  (let ([compiler (new compile-S4)]
        [interp (new interp-S4)])
    (list 'idk?)))
