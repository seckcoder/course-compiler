(let ([v (vector 0)])
  (let ([void (vector-set! v 0 #f)])
    (vector-ref v 0)))
