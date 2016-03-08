(let ([v (vector 4 (vector 2 (vector 6 (vector (vector 1 42) (vector 3)))))])
  (vector-ref (vector-ref (vector-ref (vector-ref (vector-ref v 1) 1) 1) 0) 1))
