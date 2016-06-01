
;; This test is supose to keep everything alive in the heap
;; causing allocation that has to check forwarding pointers.

(let ([v0 (vector 42)])
  (let ([v1 (vector v0 v0)])
    (let ([v2 (vector v1 v1 v1 v1)])
      (let ([v3 (vector v2 v2 v2 v2 v2 v2 v2 v2)])
        (let ([v4 (vector v3 v3 v3 v3 v3 v3 v3 v3 v3 v3 v3 v3 v3 v3 v3 v3)])
          (vector-ref
           (vector-ref
            (vector-ref
             (vector-ref
              (vector-ref v4 4) 3) 2) 1) 0))))))
