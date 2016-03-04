(let ([v (inject (lambda: ([x : Any]) : Any
		   (inject (+ (project x Integer) 2) Integer))
		 (Any -> Any))])
  (if (procedure? v)
      42
      777))
