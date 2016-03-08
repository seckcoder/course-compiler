(let ([v (vector 0)])
  (let ([void (vector-set! v 0 42)])
    (vector-ref v 0)))
