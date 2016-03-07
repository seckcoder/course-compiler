(define (even? [x : Integer]) : Boolean 
  (if (eq? x 0)
      #t
      (odd? (+ (- 1) x))))
(define (odd? [x : Integer]) : Boolean 
  (if (eq? x 0)
      #f
      (even? (+ (- 1) x))))
(if (even? (read)) 999 42)
