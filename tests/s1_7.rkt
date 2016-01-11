(let ([x (read)])
  (let ([y (read)])
    (let ([z (eq? x y)])
      (if z
	  42
	  777))))