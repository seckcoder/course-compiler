#lang racket
(require "utilities.rkt")
(require "int_exp.rkt")
;;(require "register_allocator.rkt")

(define (range start end)
  (let loop ([i start] [res '()])
    (cond [(eq? i end) (reverse res)]
	  [else (loop (add1 i) (cons i res))])))

(define (test-compiler compiler checker test-family test-nums)
  (for ([test-name (map (lambda (n) (format "~a_~a" test-family n)) 
			test-nums)])
       (debug "checking passes" '())
       (checker test-name)
       (debug "running compiler" '())
       (if (system (format "racket ~a tests/~a.scm" compiler test-name))
	   (if (system (format "gcc runtime.o tests/~a.s" test-name))
	       (let* ([input (if (file-exists? (format "tests/~a.in" test-name))
				 (format " < tests/~a.in" test-name)
				 "")]
		      [result (system/exit-code (format "./a.out~a" input))])
		 (if (eq? result 42)
		     (begin (display ".")(flush-output))
		     (error (format "test ~a failed, output: ~a" 
				    test-name result))))
	       (void))
	   (void)))
  (newline)(display "tests passed")(newline)
  )

(test-compiler "int_exp_compiler.rkt" (check-passes int-exp-passes) 
	       "s0" (range 1 11))

#;(test-compiler "reg_int_exp_compiler.rkt" (check-passes reg-int-exp-passes) 
	       "s0" (range 1 11))
