(define (hello29999) : Any (inject 24 Integer))
(define (world30000) : Any (inject 24 Integer))

(let ((x30001
         (inject
          (vector (inject 0 Integer) (inject 0 Integer))
          (Vector Any Any))))
    (let ((y30002
           (inject
            (vector-set!
             (project x30001 (Vector Any Any))
             0
             (
              (project (inject hello29999 (-> Any)) (-> Any))))
            Void)))
      (let ((z30003
             (inject
              (vector-set!
               (project x30001 (Vector Any Any))
               1
               (
                (project
                 (inject world30000 (-> Any))
                 (-> Any))))
              Void)))
        (inject
         (+
          (project
           (inject (- (project (inject 6 Integer) Integer)) Integer)
           Integer)
          (project
           (inject
            (+
             (project (vector-ref (project x30001 (Vector Any Any)) 0) Integer)
             (project (vector-ref (project x30001 (Vector Any Any)) 1) Integer))
            Integer)
           Integer))
         Integer))))
