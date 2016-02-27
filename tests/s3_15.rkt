
(define (minus [n : Integer] [m : Integer]) : Integer
  (+ n (- m)))

(define (map-vector [f : (Integer Integer -> Integer)]
                    [v : (Vector Integer)]) : (Vector Integer)
  (vector (f (vector-ref v 0) 1)))

(vector-ref (map-vector minus (vector 43)) 0)


