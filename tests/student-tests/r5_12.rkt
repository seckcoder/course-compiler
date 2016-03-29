(define (app1 [f : (Integer -> Integer)]) : Integer
  (f 42))

(define (add1 [n : Integer]) : Integer (+ n 1))

(app1 (if (eq? (read) 0) add1 (lambda: ([x : Integer]) : Integer x)))
