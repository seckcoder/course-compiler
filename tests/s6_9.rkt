(define (hello) : Any (inject 24 Integer))
(define (world) : Any (inject 24 Integer))

(let ([x (inject (vector (inject 0 Integer) (inject 0 Integer))
                 (Vector Any Any))])
  (let ([y (inject (vector-set! (project x (Vector Any Any)) 0
				((project (inject hello (-> Any)) (-> Any))))
		   Void)])
    (let ([z (inject (vector-set! (project x (Vector Any Any)) 1
				  ((project (inject world (-> Any))
					    (-> Any))))
		     Void)])
      (let ([a (project x (Vector Any Any))])
	(+ (- 6) (+ (project (vector-ref a 0) Integer)
		    (project (vector-ref a 1) Integer)))))))
