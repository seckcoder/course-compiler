
(define (vector-foo vec) (vector-set! vec 0 42))
(define (vector-foo-too vec) (vector-set! vec 1 42))
(define (vector-foo-three vec)
  (let ([veca (vector-set! vec 2 42)])
    (vector-ref veca 2)))
(let ([x (vector-foo (vector-foo-too (vector-foo-three (vector 0 0 0))))])
  x)
