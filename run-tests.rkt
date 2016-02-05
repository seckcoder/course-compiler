#lang racket
(require "utilities.rkt")
(require "int_exp.rkt")
(require "register_allocator.rkt")
(require "conditionals.rkt")
(require "vectors.rkt")
(require "functions.rkt")
(require "lambda.rkt")
(require "interp.rkt")

(define (range start end)
  (let loop ([i start] [res '()])
    (cond [(eq? i end) (reverse res)]
   	  [else (loop (add1 i) (cons i res))])))

(define (test-compiler name typechecker passes test-family test-nums)

  (display "------------------------------------------------------")(newline)
  (display "testing compiler ")(display name)(newline)
  (interp-tests name typechecker passes interp-scheme test-family test-nums)
  (compiler-tests name typechecker passes test-family test-nums)
  (newline)(display "tests passed")(newline)
  )

(define s0_range (range 1 26))
(define s1_range (range 1 31))
(define s2_range (range 1 7))
(define s3_range (range 1 11))
(define s4_range (range 0 5))

(if #t (begin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "int_exp" #f int-exp-passes "s0" s0_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "reg_int_exp" #f reg-int-exp-passes "s0" s0_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "conditionals" conditionals-typechecker conditionals-passes "s0" s0_range)
(test-compiler "conditionals" conditionals-typechecker conditionals-passes "s1" s1_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "vectors" vectors-typechecker vectors-passes "s0" s0_range)
(test-compiler "vectors" vectors-typechecker vectors-passes "s1" s1_range)
(test-compiler "vectors" vectors-typechecker vectors-passes "s2" s2_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "functions" functions-typechecker functions-passes "s0" s0_range)
(test-compiler "functions" functions-typechecker functions-passes "s1" s1_range)
(test-compiler "functions" functions-typechecker functions-passes "s2" s2_range)
(test-compiler "functions" functions-typechecker functions-passes "s3" s3_range)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test-compiler "lambda" lambda-typechecker lambda-passes "s0" s0_range)
(test-compiler "lambda" lambda-typechecker lambda-passes "s1" s1_range)
(test-compiler "lambda" lambda-typechecker lambda-passes "s2" s2_range)
(test-compiler "lambda" lambda-typechecker lambda-passes "s3" s3_range)
(test-compiler "lambda" lambda-typechecker lambda-passes "s4" s4_range)

) '())
 



 

