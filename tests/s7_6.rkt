(define (hopefully-int) (lambda (x) (let ([maybe-int (read)])
				     (if (eq? maybe-int 42) x
					42))))
(define (hopefully-bool) (lambda (x) (and (not x) #t)))
(if (hopefully-bool) ((hopefully-int) 42)
  (+ ((hopefully-int) 42) 0))
