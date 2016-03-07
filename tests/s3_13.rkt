;; A reduction fo s3_13.rkt

#;
(define (minus [n : Integer] [m : Integer]) : Integer
  (+ n (- m)))

(define (zero [x : Integer]) : (Vector)
  (if (eq? x 0)
      (vector)
      (zero (+ (vector-ref (vector x) 0) (- 1)))))

(vector-ref (vector (zero 1) (zero 2) 42) 2)




