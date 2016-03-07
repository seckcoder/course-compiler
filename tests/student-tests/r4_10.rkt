(define (uhoh [x : Integer]) : Integer
  (if (eq? x 0)
      (uhoh x)
      x))
(uhoh 42)
