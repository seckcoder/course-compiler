 (define (tailrecur [x : Integer]) : Integer
   (if (eq? x 0) 0 (tailrecur (+ x (- 1)))))
 (if (eq? 0 (tailrecur 99))
     42
     777)
