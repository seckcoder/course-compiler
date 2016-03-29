(define (app1 [f : (Integer -> Integer)] [x : Integer])
  : Integer
  (f x))

(app1 (lambda: ([x : Integer]) : Integer x) 42)
