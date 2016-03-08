(define (add1 [x : Integer]) : Integer
  (+ x 1))
(define (give-me-add1) : (Boolean -> Integer)
  add1)
((give-me-add1) #t)
