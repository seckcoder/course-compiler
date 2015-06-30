#lang racket
(require "utilities.rkt")
(require "int_exp.rkt")
(require "register_allocator.rkt")
(require "conditionals.rkt")

(define (range start end)
  (let loop ([i start] [res '()])
    (cond [(eq? i end) (reverse res)]
	  [else (loop (add1 i) (cons i res))])))

(define (check-compiler checker test-family test-nums)
  (debug "checking passes" '())
  (for ([test-name (map (lambda (n) (format "~a_~a" test-family n)) 
			test-nums)])
       (checker test-name)
       )
  (newline)(display "passed checks")(newline)
  )

(define (test-compiler compiler checker test-family test-nums)
  (for ([test-name (map (lambda (n) (format "~a_~a" test-family n)) 
			test-nums)])
       (debug "checking passes" '())
       (checker test-name)
       (debug "running compiler" '())
       (compiler (format "tests/~a.scm" test-name))
       (debug "finished compiling" '())
       (if (system (format "gcc runtime.o tests/~a.s" test-name))
	   (void) (exit))

       (let* ([input (if (file-exists? (format "tests/~a.in" test-name))
			 (format " < tests/~a.in" test-name)
			 "")]
	      [result (system/exit-code (format "./a.out~a" input))])
	 (if (eq? result 42)
	     (begin (display test-name)(display ".")(flush-output))
	     (error (format "test ~a failed, output: ~a" 
			    test-name result))))
       );for
  (newline)(display "tests passed")(newline)
  )

(test-compiler (compile-file int-exp-passes)
	       (check-passes int-exp-passes) 
  	       "s0" (range 1 13))

(test-compiler (compile-file reg-int-exp-passes)
	       (check-passes reg-int-exp-passes) 
   	       "s0" (range 1 13))

(test-compiler (compile-file conditionals-passes) 
	       (check-passes conditionals-passes) 
  	       "s0" (range 1 13))
(test-compiler (compile-file conditionals-passes)
	       (check-passes conditionals-passes) 
  	       "s1" (range 1 19))



