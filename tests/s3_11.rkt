(define (f [n : Integer] [v : (Vector Integer)]) : Integer
  (if (eq? n 100)
      (vector-ref v 0)
      (f (+ n 1) (vector (vector-ref v 0)))))

(f 0 (vector 42))
