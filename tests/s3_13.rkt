
(define (minus [n : Integer] [m : Integer]) : Integer
  (+ n (- m)))

(define (zero [x : Integer]) : (Vector)
  (if (eq? x 0)
      (vector)
      (zero (minus (vector-ref (vector x) 0) 1))))

(define (one [x : Integer]) : (Vector (Vector) Integer)
  (if (eq? x 0)
      (vector (zero 20) 42)
      (one (minus (vector-ref (vector x) 0) 1))))

(define (two [x : Integer]) : (Vector (Vector) Integer (Vector (Vector) Integer))
  (if (eq? x 0)
      (vector (zero 20) 42 (one 20))
      (two (minus (vector-ref (vector x) 0) 1))))

(define (three [x : Integer]) : (Vector (Vector) Integer (Vector (Vector) Integer) (Vector (Vector) Integer (Vector (Vector) Integer)))
  (if (eq? x 0)
      (vector (zero 20) 42 (one 20) (two 20))
      (three (minus (vector-ref (vector x) 0) 1))))

(vector-ref
 (vector-ref
  (vector-ref
   (vector-ref
    (vector (zero 20) 42 (one 20) (two 20) (three 20))
    4)
   3)
  2)
 1)




