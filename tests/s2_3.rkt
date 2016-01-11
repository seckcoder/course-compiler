(let ([v1 (vector 42)])
  (let ([v2 (vector v1)])
    (vector-ref (vector-ref v2 0) 0)))