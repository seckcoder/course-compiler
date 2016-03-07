(define (id [x : Integer]) : Integer x)
(define (id2 [y : Integer]) : Integer y)
(id2 (id 42))
