 (define (id [f : (Integer -> Integer)]) : (Integer -> Integer) f)
 (define (inc [x : Integer]) : Integer (+ x 1))
 ((id inc) 41)
