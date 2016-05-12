(define (world) : Any (inject 42 Integer))

; Allocate a vector of 1 any, initialized with an injected 0, and then inject it
; Project the vector and write the result of the function (world), which returns an injected 42, into the 0th element
; Bind a variable to the projected vector
; Read out the 0th element and project it to integer.

(let ((x (inject (vector (inject 0 Integer)) (Vector Any))))
    (let ([voidy (vector-set! (project x (Vector Any)) 0 (world))])
      (let ((a (project x (Vector Any))))
        (project (vector-ref a 0) Integer))))

;; ;; Works

; Allocate a vector of 1 any, initialized with an injected 0, and then inject it
; Project the vector and write the result of the function (world), which returns an injected 42, into the 0th element
; Bind a variable to the projected vector
; Read out the 0th element and project it to integer.


;; (define (world) : Any (inject 42 Integer))
;; (let ((x (inject (vector (inject 0 Integer)) (Vector Any))))
;;   (let ((a (project x (Vector Any))))
;;     (let ([y (vector-set! a 0 (world))])
;;         (project (vector-ref a 0) Integer))))


;; ;; Works
;; (define (world) : Any (inject 42 Integer))
;; (let ((x (vector (inject 0 Integer))))
;;     (let ([y (vector-set! x 0 (world))])
;;       (project (vector-ref x 0) Integer)))

;; ;; Works:
;; (let ((x (inject (vector (inject 0 Integer)) (Vector Any))))
;;     (let ([y (vector-set! (project x (Vector Any)) 0 (inject 42 Integer))])
;;       (let ((a (project x (Vector Any))))
;;         (project (vector-ref a 0) Integer))))

;; ;; Does not work
;; (define (world) : Integer 42)
;; (let ((x (inject (vector (inject 0 Integer)) (Vector Any))))
;;     (let ([y (vector-set! (project x (Vector Any)) 0 (inject (world) Integer))])
;;       (let ((a (project x (Vector Any))))
;;         (project (vector-ref a 0) Integer))))

