(program
 (define (double-id [x : Integer]) : Integer
   ((lambda ([x : Integer]) : Integer x) x))
 (double-id 5))
