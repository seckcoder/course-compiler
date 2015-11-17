#lang racket
(define (primitives) (set '+ '- '* 'read))

(define (collect-locals)
  (lambda (ast)
    (match ast
      [`(assign ,x ,e) (list x)]
      [`(return ,e) '()]
      [else
       (error "unmatched in collect-locals S0" ast)]
      )))

(define (map2 f ls)
  (if (null? ls) (values '() '())
      (let-values (((a d) (f (car ls)))
                   ((da dd) (map2 f (cdr ls))))
        (values (cons a da) (cons d dd)))))

(define (flatten need-atomic)
  (lambda (e)
    (match e
      [(? symbol?) (values e '())]
      [(? integer?) (values e '())]
      [`(let ([,x ,e]) ,body)
       (define-values (new-e e-ss) ((flatten #f) e))
       (define-values (new-body body-ss) ((flatten #f) body))
       (values new-body (append e-ss `((assign ,x ,new-e)) body-ss))]
      [`(,op ,es ...) #:when (set-member? (primitives) op)
       (define-values (new-es sss) (map2 (flatten #t) es))
       (define ss (append* sss))
       (define prim-apply `(,op ,@new-es))
       (cond [need-atomic
              (define tmp (gensym 'tmp))
              (values tmp (append ss `((assign ,tmp ,prim-apply))))]
             [else (values prim-apply ss)])]
      [`(program ,extra ,e)
       (define-values (new-e ss) ((flatten #f) e))
       (define xs (append* (map (collect-locals) ss)))
       `(program ,(remove-duplicates xs) ,@(append ss `((return ,new-e))))]
      )))


;; select-instructions : C0 -> psuedo-x86

(define (binary-op->inst op)
  (match op
    ['+ 'add] ['- 'sub] ['* 'imul]
    [else (error "in binary-op->inst unmatched" op)]
    ))

(define (unary-op->inst op)
  (match op
    ['- 'neg] [else (error "in unary-op->inst unmatched" op)]
    ))

(define (commutative? op)
  (match op
    ['+ #t] ['* #t] 
    [else #f]))

(define (select-instructions)
  (lambda (e)
    (match e
      [(? symbol?) `(var ,e)]
      [(? integer?) `(int ,e)]
      [`(register ,r) `(register ,r)]
      [`(return ,e)
       (( select-instructions) `(assign (register rax) ,e))]
      [`(assign ,lhs (read))
       (define new-lhs (( select-instructions) lhs))
       `((call _read_int) (mov (register rax) ,new-lhs))]
      [`(assign ,lhs ,x) #:when (symbol? x)
       (define new-lhs (( select-instructions) lhs))
       (cond [(equal? `(var ,x) new-lhs) '()]
             [else `((mov (var ,x) ,new-lhs))])]
      [`(assign ,lhs ,n) #:when (integer? n)
       (define new-lhs (( select-instructions) lhs))
       `((mov (int ,n) ,new-lhs))]
      [`(assign ,lhs (,op ,e1 ,e2))
       (define new-lhs (( select-instructions) lhs))
       (define new-e1 (( select-instructions) e1))
       (define new-e2 (( select-instructions) e2))
       (define inst (binary-op->inst op))
       (cond [(equal? new-e1 new-lhs)
              `((,inst ,new-e2 ,new-lhs))]
             [(equal? new-e2 new-lhs)
              `((,inst ,new-e1 ,new-lhs))]
             ;; The following can shorten the live range of e2. -JGS
             [(and ( commutative? op) 
                   (integer? e1) (symbol? e2))
              `((mov ,new-e2 ,new-lhs) (,inst ,new-e1 ,new-lhs))]
             [else `((mov ,new-e1 ,new-lhs) (,inst ,new-e2 ,new-lhs))])]
      [`(assign ,lhs (,op ,e1))	
       (define new-lhs (( select-instructions) lhs))
       (define new-e1 (( select-instructions) e1))
       (define inst (unary-op->inst op))
       (cond [(equal? new-e1 new-lhs)
              `((,inst ,new-lhs))]
             [else `((mov ,new-e1 ,new-lhs) (,inst ,new-lhs))])]
      [`(program ,xs ,ss ...)
       `(program ,xs ,@(append* (map ( select-instructions) ss)))]
      [else (error "instruction selection, unmatched " e)])))
