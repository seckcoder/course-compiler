#lang racket

(define (range start end)
  (let loop ([i start] [res '()])
    (cond [(eq? i end) (reverse res)]
	  [else (loop (add1 i) (cons i res))])))

(define (test-compiler compiler test-family test-nums)
  (for ([test-name (map (lambda (n) (format "~a_~a" test-family n)) 
			test-nums)])
       (if (system (format "racket ~a tests/~a.scm" compiler test-name))
	   (if (system (format "gcc runtime.o tests/~a.s" test-name))
	       (let* ([input (if (file-exists? (format "tests/~a.in" test-name))
				 (format " < tests/~a.in" test-name)
				 "")]
		      [result (system/exit-code (format "./a.out~a" input))])
		 (if (eq? result 42)
		     (void)
		     (error (format "test ~a failed, output: ~a" 
				    test-name result))))
	       (void))
	   (void)))
  (display "tests passed")(newline)
  )

(test-compiler "int_exp_compiler.rkt" "s0" (range 1 11))
