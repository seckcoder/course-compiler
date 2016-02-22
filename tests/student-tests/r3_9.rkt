(let ([v (vector (vector 0))])
  (let ([void (vector-set! v 0 v)])
    42))
