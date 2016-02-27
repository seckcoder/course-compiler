#lang racket
(require "utilities.rkt")
(require "int_exp.rkt")
(require "register_allocator.rkt")
(require "conditionals.rkt")
(require "vectors.rkt")
(require "functions.rkt")
(require "lambda.rkt")
(require "interp.rkt")
(require "runtime-config.rkt")

;; I have made the original run-tests more programmatic so that we
;; don't have to edit it in order to change which test are run or
;; change parameters to the compiler. To get the default behavior
;; simply type "racket run-tests.rkt" at the command line. To get a
;; description of what can be manipulated pass "-h" for the help
;; message.  I will add the abilility to run student tests shortly.

;; Table associating names of compilers with the information for
;; running and testing them.
(define compiler-list
  ;; Name           Typechecker               Compiler-Passes      Valid suites
  `(("int_exp"      #f                        ,int-exp-passes      (0))
    ("reg_int_exp"  #f                        ,reg-int-exp-passes  (0))
    ("conditionals" ,conditionals-typechecker ,conditionals-passes (0 1))
    ("vectors"      ,vectors-typechecker      ,vectors-passes      (0 1 2))
    ("functions"    ,functions-typechecker    ,functions-passes    (0 1 2 3))
    ("lambda"       ,lambda-typechecker       ,lambda-passes       (0 1 2 3 4))
    ))

(define compiler-table (make-immutable-hash compiler-list))

;; This list serves the same function as the range definitions that were used
;; prior to giving run-tests a command line interfaces.
(define suite-list
  `((0 . ,(range 1 26))
    (1 . ,(range 1 32))
    (2 . ,(range 1 18))
    ;; There is a problem with interp that needs sorted in problem 16
    (3 . ,(range 1 16))
    (4 . ,(range 0 5))))

(define (suite-range x)
  (let ([r? (assoc x suite-list)])
    (unless r?
      (error 'suite-range "invalid suite ~a" x))
    (cdr r?)))

;; test-compiler runs a compiler (list of passes) with a name and
;; typechecker on a list of tests in a particular test-suite.
(define (test-compiler name typechecker passes test-suite test-nums)
  (display "------------------------------------------------------")(newline)
  (display "testing compiler ")(display name)(newline)
  (interp-tests name typechecker passes interp-scheme test-suite test-nums)
  (compiler-tests name typechecker passes test-suite test-nums)
  (newline)(display "tests passed")(newline))

;; These parameters may be altered by passing at the command line if
;; they are not altered then the default is to test everything.
(define compilers-to-test
  (make-parameter #f))
(define suites-to-test
  (make-parameter #f))
(define tests-to-run
  (make-parameter #f))

;; add some object to the end of an optional list stored in a parameter.
;; This seems case specific or else I would put it in utilities. -andre
(define (snoc-to-opt-param param x)
  (unless (parameter? param)
    (error 'snoc-to-opt-param "expected a parameter: ~a" param))
  (param (let ([list? (param)])
           (if list?
               (let snoc ([ls list?] [x x])
                 (cond
                   [(pair? ls)
                    (cons (car ls)
                          (snoc (cdr ls) x))]
                   [else (list x)]))
               (list x)))))

;; The command-line macro is a standard racket function for controlling
;; 
(command-line
 #:multi
 ;; Add a compiler to the set of test to run
 [("-c" "--compiler") name "add a compiler to the test set"
  (unless (hash-ref compiler-table name #f)
    (error 'run-tests
           "compiler flag expects a compiler: ~a\nvalid compilers ~a"
           name (map car compiler-list)))
  (snoc-to-opt-param compilers-to-test name)]
 ;; Add a test suite to the test to run
 [("-s" "--suite") num "number of suite to run"
  (let ([suite-n (string->number num)])
    (unless (exact-nonnegative-integer? suite-n)
      (error 'run-tests "suites are nonnegative integers, got ~a" num))
    (snoc-to-opt-param suites-to-test suite-n))]
 ;; Select individual tests to run
 [("-t" "--test") num "specify specific test numbers to run"
  (let ([test-n (string->number num)])
    (unless (exact-nonnegative-integer? test-n)
      (error 'run-tests "tests are nonnegative integers, got ~a" num))
    (snoc-to-opt-param tests-to-run test-n))]
 ;; turn up the debbugging volume
 ["-d" "increment debugging level" (debug-level (add1 (debug-level)))]

 ;; These are the flags that are each allowed once
 #:once-each
 [("-r" "--rootstack-size") bytes
  "set the size of rootstack for programs compiled"
  (let ([bytes? (string->number bytes)])
    (unless (and (exact-positive-integer? bytes?)
                 (= (remainder bytes? 8) 0))
      (error 'run-tests
             "rootstack-size expected positive multiple of 8: ~v"
             bytes)) 
    (rootstack-size bytes?))]

 [("-m" "--heap-size") bytes
  "set the size of initial heap for programs compiled"
  (let ([bytes? (string->number bytes)])
    (unless (and (exact-positive-integer? bytes?)
                 (= (remainder bytes? 8) 0))
      (error 'run-tests
             "heap-size expected positive multiple of 8: ~v" bytes)) 
    (heap-size bytes?))]

 ;; Allows setting the number of columns that the pretty printer
 ;; uses to display s-expressions.
 [("-w" "--pprint-width") columns "set the width for pretty printing"
  (let ([columns (string->number columns)])
    (unless (exact-positive-integer? columns)
      (error 'run-tests "expected positive integer, but found ~v" columns)) 
    (pretty-print-columns columns))]


 #:args ()
 ;; default to testing all compilers 
 (unless (compilers-to-test)
   (compilers-to-test (map car compiler-list)))

 ;; default to testing all suites
 (unless (suites-to-test)
   (suites-to-test (map car suite-list)))

 ;; default to testing the first 100 tests in each suite
 (unless (tests-to-run)
   (tests-to-run (range 0 100)))

 ;; This is the loop that calls test compile for each suite
 (for ([compiler (compilers-to-test)])
   (let ([info? (hash-ref compiler-table compiler #f)])
     (unless info?
       (error 'run-tests "invalid compiler: ~a" compiler))
     (match-let ([(list tyck pass suites) info?])
       (for ([suite (suites-to-test)])
         (when (set-member? suites suite)
           (let* ([sname (format "s~a" suite)]
                  [test-set (set-intersect (suite-range suite) (tests-to-run))]
                  [tests (sort test-set <)])
             (test-compiler compiler tyck pass sname tests))))))))

 



 

