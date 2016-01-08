#lang racket
(require "utilities.rkt")
(require "int_exp.rkt")
(require "register_allocator.rkt")
(require "conditionals.rkt")
(require "vectors.rkt")
(require "functions.rkt")
(require "lambda.rkt")

(define (range start end)
  (let loop ([i start] [res '()])
    (cond [(eq? i end) (reverse res)]
   	  [else (loop (add1 i) (cons i res))])))

(define (test-compiler name passes test-family test-nums)

  (display "------------------------------------------------------")(newline)
  (display "testing compiler ")(display name)(newline)
  (interp-tests name passes test-family test-nums)
  (compiler-tests name passes test-family test-nums)
  (newline)(display "tests passed")(newline)
  )

(define s0_range (range 1 24))
(define s1_range (range 1 22))
(define s2_range (range 1 7))
(define s3_range (range 1 10))
(define s4_range (range 0 5))

;(test-compiler "conditionals" conditionals-passes "s1" (range 21 22))

(if #t (begin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "int_exp" int-exp-passes "s0" s0_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "reg_int_exp" reg-int-exp-passes "s0" s0_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "conditionals" conditionals-passes "s0" s0_range)
(test-compiler "conditionals" conditionals-passes "s1" s1_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "vectors" vectors-passes "s0" s0_range)
(test-compiler "vectors" vectors-passes "s1" s1_range)
(test-compiler "vectors" vectors-passes "s2" s2_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "functions" functions-passes "s0" s0_range)
(test-compiler "functions" functions-passes "s1" s1_range)
(test-compiler "functions" functions-passes "s2" s2_range)
(test-compiler "functions" functions-passes "s3" s3_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "lambda" lambda-passes "s0" s0_range)
(test-compiler "lambda" lambda-passes "s1" s1_range)
(test-compiler "lambda" lambda-passes "s2" s2_range)
(test-compiler "lambda" lambda-passes "s3" s3_range)
(test-compiler "lambda" lambda-passes "s4" s4_range)

) '())



