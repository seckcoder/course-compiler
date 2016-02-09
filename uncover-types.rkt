#lang racket

(provide uncover-types)

;; Given a program return a type environment for all variables
(define (uncover-types prog)
  ;; Associate var with type in env but ensure it doesn't
  ;; conflict with any other type that we uncovered previously.
  (define (env-set env var type)
    (let ([ty? (hash-ref env var #f)])
      (cond
        [(not ty?) (hash-set env var type)]
        [(equal? type ty?) env]
        [else
         (error 'env-set
                "conflicting types for ~a, ~a and ~a" var type ty?)])))
  (define (primitive? x)
    (set-member? '(+ - * read and or not eq?) x))
  ;; look up a variable in the environment
  (define (env-ref env var)
    (define (err) (error 'env-ref "unbound ~a in ~a" var env))
    (hash-ref env var err))
  ;; Recur with the flow of execution is stmts accumulating an
  ;; environment the enviroment that is present at the end of ss.
  (define ((ut-seq env) ss) (foldl ut-stmt env ss))
  ;; Build an environment extended the given env with any
  ;; variables assigned in x.
  (define (ut-stmt stmt env)
    ;; return the type of an expression
    (define (ut-expr expr)
      (match expr
        [(? symbol? x)  (env-ref env x)]
        [`(allocate ,l ,t) t]
        [`(vector ,(app ut-expr t*) ...) `(Vector ,@t*)] 
        [`(vector-ref ,(app ut-expr `(Vector ,t* ...)) ,i)
         (list-ref t* i)]
        [`(vector-set! ,v ,i ,e) 'Void]
        [(? integer?)  'Integer]
        [(? boolean?)  'Boolean]
        [`(,(? primitive? op) ,_ ...)
         (case op
           [(+ - * read) 'Integer]
           [(and or not eq?) 'Boolean])]
        [else (error 'uncover-types-expr "unmatched ~v" expr)]))
    ;; Body of uncover-type-stmt
    (match stmt
      [`(assign ,(? symbol? lhs) ,(app ut-expr t))
       (match t
         ;; This line is expiremental.
         ;; by not adding void types to the environment we ensure
         ;; that any attempt to reference them will result in an
         ;; internal compiler error, a further advantage is that the
         ;; environment locals form for your ASTs will be smaller
         ;; Feel free to uncomment
         ;; ['Void env]
         [other (env-set env lhs t)])]
      [`(if ,t ,(app (ut-seq env) c-env) ,(app (ut-seq env) a-env))
       ;; merge resulting environments making sure that they agree
       ;; any error here would be the result of a incorrect transformation
       ;; in an earlier pass.
       (for/fold ([env c-env]) ([(k v) (in-hash a-env)])
         (env-set env k v))]
      [otherwise env]))
  ;; Body of uncover-type
  (match prog
    [`(program (,xs ...) (type ,ty) . ,ss)
     (let ([env ((ut-seq (hash)) ss)])
       (for ([x (in-list xs)])
         (let ([err (lambda ()
                      (error 'uncover-type "failed to find ~a" x))])
           (hash-ref env x err)))
       ;; Feel free to remove this if you prefer working
       ;; with hashtable instead.
       (hash->list env))]
    [else (error 'uncover-type "unmatched ~a" prog)]))
