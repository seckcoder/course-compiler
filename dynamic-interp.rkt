#lang racket
(require racket/fixnum)
(require "utilities.rkt" (prefix-in runtime-config: "runtime-config.rkt"))
(provide interp-r7)

(define get-injected-type
  (lambda (e)
    (match e
      [`(inject ,v ,ty) ty])))

(define valid-op?
  (lambda (op)
    (member op '(+ - and or not))))

(define interp-r7-op
  (lambda (op es)
    (match `(,op ,es)
      [`(+ ((inject ,v1 Integer) (inject ,v2 Integer)))
       `(inject ,(fx+ v1 v2) Integer)]
      [`(- ((inject ,v Integer)))
       `(inject ,(fx- 0 v) Integer)]
      [`(and (,v1 ,v2))
       (match v1
         [`(inject #f Boolean) v1]
         [else v2])]
      [`(or (,v1 ,v2))
       (match v1
         [`(inject #f Boolean) v2]
         [else v1])]
      [`(not (,v1))
       (match v1
         [`(inject #f Boolean) `(inject #t Boolean)]
         [else `(inject #f Boolean)])])))
         
(define (interp-r7 env)
  (lambda (ast)
    (vomit "interp-r7" ast env)
    (match ast
      [(? symbol?) (lookup ast env)]
      [`(function-ref ,f) (lookup f env)]
      [`(function-ref ,f ,n) (lookup f env)] ;; This is to deal with the detail of our translation that it keeps the arity of functions in the funref 
      [(? integer?) `(inject ,ast Integer)]
      [#t `(inject #t Boolean)]
      [#f `(inject #f Boolean)]
      [`(read) `(inject ,(read-fixnum) Integer)]
      [`(lambda (,xs ...) ,body)
       `(inject (lambda ,xs ,body ,env) (,@(map (lambda (x) 'Any) xs) -> Any))]
      [`(define (,f ,xs ...) ,body)
       (mcons f `(lambda ,xs ,body))]
      [`(program ,ds ... ,body)
       (let ([top-level (map (interp-r7 '()) ds)])
         ;; Use set-cdr! on define lambda's for mutual recursion
         (for/list ([b top-level])
           (set-mcdr! b (match (mcdr b)
                          [`(lambda ,xs ,body)
                           `(inject (lambda ,xs ,body ,top-level) 
                                    (,@(map (lambda (x) 'Any) xs) -> Any))])))
         ((interp-r7 top-level) body))]
      [`(vector ,es ...)
       (let* ([elts (map (interp-r7 env) es)]
              [tys (map get-injected-type elts)])
         `(inject ,(apply vector (map (interp-r7 env) es)) (Vector ,@tys)))]
      [`(vector-set! ,e1 ,n ,e2)
       (let ([e1^ ((interp-r7 env) e1)]
             [e2^ ((interp-r7 env) e2)])
         (match e1^ 
           [`(inject ,vec ,ty) 
            (vector-set! vec n e2^)
            `(inject (void) Void)]))]
      [`(vector-ref ,e ,n)
       (let ([e^ ((interp-r7 env) e)])
         (match e^ 
           [`(inject ,vec ,ty) 
            (vector-ref vec n)]))]
      [`(let ([,x ,e]) ,body)
       (let ([v ((interp-r7 env) e)])
         ((interp-r7 (cons (cons x v) env)) body))]
      [`(,op ,es ...) #:when (valid-op? op)
       (interp-r7-op op (map (interp-r7 env) es))]
      [`(eq? ,l ,r)
       `(inject ,(equal? ((interp-r7 env) l) ((interp-r7 env) r)) Boolean)]
      [`(if ,q ,t ,f)
       (match ((interp-r7 env) q)
         [`(inject #f Boolean)
          ((interp-r7 env) f)]
         [else ((interp-r7 env) t)])]
      [`(app ,f ,es ...) 
       (define new-args (map (interp-r7 env) es))
       (let ([f-val ((interp-r7 env) f)])
         (match f-val 
           [`(inject (lambda (,xs ...) ,body ,lam-env) ,ty)
            (define new-env (append (map cons xs new-args) lam-env))
            ((interp-r7 new-env) body)]
           [else (error "interp-r7, expected function, not" f-val)]))]
      [`(,f ,es ...)
       (define new-args (map (interp-r7 env) es))
       (let ([f-val ((interp-r7 env) f)])
         (match f-val 
           [`(inject (lambda (,xs ...) ,body ,lam-env) ,ty)
            (define new-env (append (map cons xs new-args) lam-env))
            ((interp-r7 new-env) body)]
           [else (error "interp-r7, expected function, not" f-val)]))])))
