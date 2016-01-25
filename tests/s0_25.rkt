(let ([a 1])                  ; a -> 0
  (let ([b 42])               ; b -> 1
    (let ([f b])              ; f -> 2
      (let ([e (+ a b)])      ; e -> 0
       (let ([d f])           ; d -> 0
          d)))))
        