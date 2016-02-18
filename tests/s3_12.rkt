
(define (id [x : Integer]) : Integer x)

(define (f [n : Integer] [clos : (Vector (Integer -> Integer) (Vector Integer))]) : Integer
  (if (eq? n 100)
      ((vector-ref clos 0) (vector-ref (vector-ref clos 1) 0))
      (f (+ n 1) (vector (vector-ref clos 0) (vector-ref clos 1)))))

(f 0 (vector id (vector 42)))
