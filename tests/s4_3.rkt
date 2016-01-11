 (define (idkcomb [x : Integer]) : Integer
   ((lambda: ([x : Integer]) : Integer x)
    ((lambda: ([y : Integer]) : Integer x) 444)))
 (idkcomb 42)
