(let ([v (inject (vector (inject 42 Integer)) (Vector Any))])
  (project (vector-ref (project v (Vector Any)) 0) Integer))