#lang racket

(require racket/contract)
(provide
 (contract-out
  [rootstack-length (parameter/c exact-nonnegative-integer?)]
  [heap-length      (parameter/c exact-nonnegative-integer?)]))

(define rootstack-length
  (make-parameter 10000))

(define heap-length
  (make-parameter 10000))
