(define (o [i : Integer] [v : (Vector Integer)]) : (Vector (Vector Integer))
  (if (eq? i 0)
      (vector v)
      (let ([junk (vector (vector 1) (vector 2)(vector 1) (vector 2)
                          (vector 1))])
        (o (+ i (- 1)) v))))

(define (t [v : (Vector (Vector Integer))])
  : (Vector (Vector (Vector Integer)))
  (vector v))

(define (h [v : (Vector (Vector (Vector Integer)))])
  : (Vector (Vector (Vector (Vector Integer))))
  (vector v))


(define (f [v : (Vector (Vector (Vector (Vector Integer))))])
  : (Vector (Vector (Vector (Vector (Vector Integer)))))
  (vector v))

(define (e [v : (Vector (Vector (Vector (Vector (Vector Integer)))))])
  : (Vector (Vector (Vector (Vector (Vector (Vector Integer))))))
  (vector v))

(vector-ref
 (vector-ref
  (vector-ref
   (vector-ref
    (vector-ref
     (vector-ref
      (e (vector (h (t (o 1 (vector 42))))))
      0)
     0)
    0)
   0)
  0)
 0)



