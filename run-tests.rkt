#lang racket

(define (range start end)
  (let loop ([i start] [res '()])
    (cond [(eq? i end) (reverse res)]
	  [else 
	   (loop (add1 i) (cons i res))])))


(define (test-compiler compiler num-tests)
  (for ([test-name (map (lambda (n) (format "s0_~a" n)) 
			(range 1 (add1 num-tests)))])
       (if (system (format "racket ~a tests/~a.scm" compiler test-name))
	   (if (system (format "gcc tests/~a.s" test-name))
	       (let ([result (system/exit-code "./a.out")])
		 (if (eq? result 42)
		     (void)
		     (error (format "test ~a failed, output: ~a" 
				    test-name result))))
	       (void))
	   (void)))
  (display "tests passed")(newline)
  )

(test-compiler "int_exp.rkt" 8)
