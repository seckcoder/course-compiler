#lang racket

(require racket/contract)
(provide
 (contract-out
  [rootstack-size (parameter/c exact-nonnegative-integer?)]
  [heap-size      (parameter/c exact-nonnegative-integer?)]))


;; Parameter that determines what the initial rootstack size of the program is.
(define rootstack-size
  (make-parameter (expt 2 13)))

;; Parameter that determines what the initial heap size of the program is.
(define heap-size 
  (make-parameter (expt 2 4)))
