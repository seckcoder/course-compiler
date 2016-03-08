(let ([v (vector (vector 0))])
  (let ([v2 (vector #t)])
    (let ([void (vector-set! v 0 v2)])
      (vector-ref (vector-ref v 0) 0))))
