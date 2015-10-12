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
        (match e
          [`(lambda: ([,x : ,T] ...) ,e) ...]
          [`(,e ,e* ...) ...]
          [else ((super type-check env) e)]
          )))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define lambda-passes
  (let ([compiler (new compile-S4)]
        [interp (new interp-S4)])
    (list 5)))
