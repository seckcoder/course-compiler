(define (even? [x : Integer]) : Boolean 
  (if (eq? x 0)
      #t
      (odd? (+ (- 1) x))))
(define (odd? [x : Integer]) : Boolean 
  (if (eq? x 0)
      #f
      (even? (+ (- 1) x))))
(let ([vec (vector odd?)])
  (let ([dummy (vector-set! vec 0 even?)])
    (if ((vector-ref vec 0) 21) 999 42)))
