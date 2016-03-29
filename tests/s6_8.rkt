(define (hello29999) : Any (inject 24 Integer))
(define (world30000) : Any (inject 24 Integer))

(let ((x30001
          (vector (inject 0 Integer) (inject 0 Integer))
          ))
    (let ((y30002
           (inject
            (vector-set! x30001
             0
             (
              (project (inject hello29999 (-> Any)) (-> Any))))
            Void)))
      (let ((z30003
             (inject
              (vector-set! x30001
               1
               (
                (project
                 (inject world30000 (-> Any))
                 (-> Any))))
              Void)))
        (inject
         (+ (- (project (inject 6 Integer) Integer))            
            (+
             (project (vector-ref x30001 0) Integer)
             (project (vector-ref x30001 1) Integer)))
         Integer))))
