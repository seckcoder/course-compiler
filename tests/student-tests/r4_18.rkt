(define (big [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] 
             [f : Integer] [g : Integer] [h : Integer] [i : Integer] [j : Integer]) : Integer
        (+ d j))
(define (big2 [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] 
              [f : Integer] [g : Integer] [h : Integer]) : Integer
        (+ d h))
(let ([a (big 1 2 3 10 5 6 7 8 9 11)])
  (let ([b (big2 1 2 3 10 5 6 7 11)])
    (+ a b)))
             
