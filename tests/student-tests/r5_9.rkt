(define (make-wrapper [in : (Integer -> Integer)] [out : (Integer -> Integer)])
  : ((Integer -> Integer) -> (Integer -> Integer))
  (lambda: ([fn : (Integer -> Integer)]) : (Integer -> Integer)
           (lambda: ([x : Integer]) : Integer
                    (out (fn (in x))))))

(define (add1 [x : Integer]) : Integer (+ x 1))
(define (sub1 [x : Integer]) : Integer (+ x (- 1)))

(define (constfun [x : Integer]) : Integer 42)
(define (double [x : Integer]) : Integer (+ x x))

(let ([wrapper (make-wrapper add1 sub1)])
  (let ([wrapconst (wrapper constfun)])
    (let ([wrapdub (wrapper double)])
      (let ([a (wrapdub 11)])
        (constfun 777)))))
