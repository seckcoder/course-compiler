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

(define ((run-single-test compiler-name test-name))
  ;; Get the compiler configuration
  (define (err-compiler)
    (error 'run-single-test "invalid compiler ~a" compiler-name))
  (match-define (list typechecker passes)
    (hash-ref compiler-table compiler-name err-compiler))

  ;; Check to make sure that the test has a file backing it
  (define test-source (build-path "tests" (string-append test-name ".rkt")))
  (unless (file-exists? test-source)
    (error 'run-single-test "invalid test ~a, no " test-name))

  (display "------------------------------------------------------")(newline)
  (printf "testing compiler ~a on ~a\n" compiler-name test-name)
  #;((check-passes compiler-name name typechecker passes interp-scheme) test-name)
  )

(define s0_range (range 1 26))
(define s1_range (range 1 30))
(define s2_range (range 1 8))
(define s3_range (range 1 11))
(define s4_range (range 0 5))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feature-table
  (make-immutable-hash
   `(("int" .
      ,(lambda ()
         (test-compiler "int_exp" #f int-exp-passes "s0" s0_range)))
     ("reg" .
      ,(lambda ()
         (test-compiler "reg_int_exp" #f reg-int-exp-passes "s0" s0_range)))
     ("if" .
      ,(lambda ()
         (let ([tc conditionals-typechecker]
               [ps conditionals-passes])
           (test-compiler "conditionals" tc ps "s0" s0_range)
           (test-compiler "conditionals" tc ps "s1" s1_range))))
     ("vector" .
      ,(lambda ()
         (let ([tc vectors-typechecker]
               [ps vectors-passes])
           ;;(test-compiler "vectors" tc ps "s0" s0_range)
           ;;(test-compiler "vectors" tc ps "s1" s1_range)
           (test-compiler "vectors" tc ps "s2" '(8)))))
     ("function" .
      ,(lambda ()
         (let ([tc functions-typechecker]
               [ps functions-passes])
           (test-compiler "functions" tc ps "s0" s0_range)
           (test-compiler "functions" tc ps "s1" s1_range)
           (test-compiler "functions" tc ps "s2" s2_range)
           (test-compiler "functions" tc ps "s3" s3_range))))
     ("lambda" .
      ,(lambda ()
         (let ([tc lambda-typechecker]
               [ps lambda-passes])
           (test-compiler "lambda" tc ps "s0" s0_range)
           (test-compiler "lambda" tc ps "s1" s1_range)
           (test-compiler "lambda" tc ps "s2" s2_range)
           (test-compiler "lambda" tc ps "s3" s3_range)
           (test-compiler "lambda" tc ps "s4" s4_range)))))))

(define compiler-table
  (hash))

(define feature-list
  `("int" "reg" "if" "vector" "function" "lambda"))


(define specific-tests (make-parameter #f))
(command-line
 #:once-each
 ;; Allows setting the number of columns that the pretty printer
 ;; uses to display s-expressions.
 [("-w" "--pprint-width") columns "set the width for pretty printing"
  (let ([columns (string->number columns)])
    (unless (exact-positive-integer? columns)
      (error 'run-tests "expected positive integer, but found ~v" columns)) 
    (pretty-print-columns columns))]
 #:multi
 [("-f" "--feature") name "feature name (int, reg, if, vector, function, lambda)"
  (define (oops) (error 'run-tests "unrecognized feature ~a" name))
  (specific-tests
   (cons (hash-ref feature-table name oops)
         (or (specific-tests) '())))]
 #;
 [("-t" "--test") compiler test ""
 (specific-test
 (cons (run-single-test compiler test)
       (or (specific-test) '())))]
;; If you pass -d or --debug to the file all the (debug label val ...)
;; statements will print the labels and values. This is done by
;; setting the debug-state parameter in utilities.rkt to be true.
["-d" "increment debugging level" (debug-level (add1 (debug-level)))]
#:args ()
(if (not (specific-tests))
    (for ([feature feature-list])
      ((hash-ref feature-table feature)))
    (for ([test (specific-tests)]) (test))))

 



 

