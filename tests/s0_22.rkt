(let ([v 1])                ; v = 1       v->rbx
  (let ([w 46])             ; w = 46      w->8
    (let ([x (+ v 7)])      ; x = 8       x->16
      (let ([y  (+ 4 x)])   ; y = 12      y->rbx
	(let ([z  (+ x w)]) ; z = 54      z->16
	  (+ z (- y)))))))      ; z - y = 42