(define (cell) : (Integer -> (Integer -> Integer))
  (let ([vec (vector 0)])
    (lambda: ([msg : Integer]) : (Integer -> Integer)
             (if (eq? msg 0)
                 (lambda: ([dummy : Integer]) : Integer
                         (vector-ref vec 0))
                 (lambda: ([set : Integer]) : Integer
                         (let ([dummy (vector-set! vec 0 set)])
                           42))))))


(let ([c (cell)])
  (let ([dummy ((c 0) 42)])
    ((c 1) 0)))
