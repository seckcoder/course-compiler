(define (mult [x : Integer] [y : Integer]) : Integer
  (if (eq? 0 x)
      0
      (+ y (mult (+ (- 1) x) y))))
(mult 6 7)
