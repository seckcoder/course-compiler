(program
 (define (fact [x : Integer]) : Integer
    (if (eq? x 1) 1 (* x (fact (- x 1)))))
 (if (eq? (fact 5) 120)
     42
     777))
