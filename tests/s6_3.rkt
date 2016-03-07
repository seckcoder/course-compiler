(let ([v (inject (lambda: ([x : Any]) : Any
		   (inject (+ (project x Integer) 2) Integer))
		 (Any -> Any))])
  (let ([a (inject 40 Integer)])
    (project ((project v (Any -> Any)) a) Integer)))
