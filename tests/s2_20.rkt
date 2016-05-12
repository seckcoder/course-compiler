(let ([a (vector 777)])
  (let ([b (vector a a)])
    (let ([_ (vector-set! (vector-ref b 0) 0 42)])
      (vector-ref a 0))))
