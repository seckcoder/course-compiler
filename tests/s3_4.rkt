(define (sum [x : Integer]) : Integer
   (if (eq? x 1) 1 (+ x (sum (+ x (- 1))))))

(if (eq? (sum 3) 6)
    42
    777)
