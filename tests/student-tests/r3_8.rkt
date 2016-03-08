(let ([v (vector (vector 0))])
  (let ([void (vector-set! (vector-ref v 0) 0 42)])
    (vector-ref (vector-ref v 0) 0)))
