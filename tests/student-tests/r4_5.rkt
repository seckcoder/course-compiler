(define (id [x : Integer]) : Integer x)
(let ([fun id])
  (fun 42))
