(program
 (define (id-k-comb [x : Integer]) : Integer
   ((lambda ([x : Integer]) : Integer x)
    ((lambda ([y : Integer]) : Integer x) 6)))
 (id-k-comb 5))
