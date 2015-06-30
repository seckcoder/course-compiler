(let ([v (vector 0 0)])
  (let ([_ (vector-set! v 0 38)])
    (let ([_ (vector-set! v 1 4)])
      (+ (vector-ref v 0) (vector-ref v 1)))))
