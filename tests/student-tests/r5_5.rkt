(define (app [f : (Integer -> Integer)] [x : Integer])
  : Integer
  (f x))

(app (lambda: ([x : Integer]) : Integer x) 42)
