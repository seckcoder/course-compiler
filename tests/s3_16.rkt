(define (minus [m : Integer] [n : Integer]) : Integer
  (+ m (- n)))

(define (z [i : Integer]) : (Vector Integer)
  (if (eq? i 0)
      (vector 42)
      (let ([junk (vector (vector 1) (vector 2) (vector 3) (vector 4) (vector 5))])
        (let ([garbage (vector -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1)])
          (let ([more (vector junk garbage junk garbage junk garbage junk garbage)])
            (z (minus i 1)))))))

(define (o [i : Integer] [v : (Vector Integer)]) : (Vector (Vector Integer))
  (if (eq? i 0)
      (vector v)
      (let ([junk (vector (vector 1) (vector 2) (vector 3) (vector 4) (vector 5))])
        (let ([garbage (vector -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1)])
          (let ([more (vector junk garbage junk garbage junk garbage junk garbage)])
            (o (minus i 1) v))))))

(define (t [i : Integer] [v : (Vector (Vector Integer))])
  : (Vector (Vector (Vector Integer)))
  (if (eq? i 0)
      (vector v)
      (let ([junk (vector (vector 1) (vector 2) (vector 3) (vector 4) (vector 5))])
        (let ([garbage (vector -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1)])
          (let ([more (vector junk garbage junk garbage junk garbage junk garbage)])
            (t (minus i 1) v))))))

(define (h [i : Integer] [v : (Vector (Vector (Vector Integer)))])
  : (Vector (Vector (Vector (Vector Integer))))
  (if (eq? i 0)
      (vector v)
      (let ([junk (vector (vector 1) (vector 2) (vector 3) (vector 4) (vector 5))])
        (let ([garbage (vector -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1)])
          (let ([more (vector junk garbage junk garbage junk garbage junk garbage)])
            (h (minus i 1) v))))))

(define (f [i : Integer] [v : (Vector (Vector (Vector (Vector Integer))))])
  : (Vector (Vector (Vector (Vector (Vector Integer)))))
  (if (eq? i 0)
      (vector v)
      (let ([junk (vector (vector 1) (vector 2) (vector 3) (vector 4) (vector 5))])
        (let ([garbage (vector -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1)])
          (let ([more (vector junk garbage junk garbage junk garbage junk garbage)])
            (f (minus i 1) v))))))

(define (e [i : Integer] [v : (Vector (Vector (Vector (Vector (Vector Integer)))))])
  : (Vector (Vector (Vector (Vector (Vector (Vector Integer))))))
  (if (eq? i 0)
      (vector v)
      (let ([junk (vector (vector 1) (vector 2) (vector 3) (vector 4) (vector 5))])
        (let ([garbage (vector -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1)])
          (let ([more (vector junk garbage junk garbage junk garbage junk garbage)])
            (e (minus i 1) v))))))


(vector-ref
 (vector-ref
  (vector-ref
   (vector-ref
    (vector-ref
     (vector-ref
      (e 20 (f 20 (h 20 (t 20 (o 20 (z 20))))))
      0)
     0)
    0)
   0)
  0)
 0)
