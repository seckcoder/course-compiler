(define (foo [fn : (Integer -> Integer)]) : Integer
  (fn 42))

(foo (lambda: ([z : Integer]) : Boolean #f))
