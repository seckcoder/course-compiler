(let ([x (if (let ([x #t]) (if x x #f)) #t #f)]) (if x 42 777))
