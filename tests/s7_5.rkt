(define (hello) 24)
(define (world) 24)
(let ([x (vector 0 0)])
  (let ([y (hello)])
    (let ([z (world)])
      (let ([voidx (vector-set! x 0 (hello))])
	(let ([voidy (vector-set! x 1 z)]) ;; change z to (world) for bug -Jeremy
	  (+ (- 6) (+ (vector-ref x 0) (vector-ref x 1)))
	  )))))

