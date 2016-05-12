(let ([a (vector (vector 777) 98)])
  (let ([b (vector (vector-ref a 0) 99 100)])
    (let ([_ (vector-set! (vector-ref b 0) 0 42)])
      (vector-ref (vector-ref a 0) 0))))
