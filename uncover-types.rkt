#lang racket
(provide uncover-types uncover-types-define)
;; This file provides the uncover-types function which can be used to
;; recover type information for variables in the program body. This
;; function can be used to help simplify the complexity of
;; expose-allocation and uncover-call-live-roots.  Expose-allocation
;; needs the type of each allocated vector in order to correctly tag
;; the vector, and uncover-call-live-roots needs the type information
;; to identify roots at each collection call site.
;;
;; In the match clause for 'program' in expose-allocation, the uncover
;; types function can be called to get an association list mapping
;; variables to types. This map can then be passed as a parameter into
;; expose-allocation so that you can determine the type of a vector
;; needed for 'allocate' by looking up the type of the variable to
;; which that vector is assigned.  After processing the entire program
;; the type environment can be saved for the next pass in the locals
;; slot of the program form.
;;
;; While processing the program form of uncover-call-live-roots, this
;; environment can be retrieved from the locals slot and again passed
;; without change throughout the processing of the body of the
;; program.  When we find a variable in expression possition and the
;; type of the variable is a Vector type then we consider this
;; variable to be a live root.  All such live roots are collected at
;; calls to the collector and stored in the live set. After this pass
;; the original locals form can be restored by taking the car of all
;; pairs in the association list.

;; Here is a minimal example of its use.
(module+ test
  (require "utilities.rkt")
  
  (define test-prog1
    '(program (foo bar baz bam)
              (type Integer)
              (assign foo (vector 777))
              (assign bar (vector foo foo))
              (assing _   (vector-set! foo 0 42))
              (assign baz (vector-ref bar 1))
              (assign bam (vector-ref baz 0))
              (return bam)))

  (lookup 'foo (uncover-types test-prog1)) ;; => 'Integer
  (lookup 'baz (uncover-types test-prog1)) ;; => '(Vector Integer)
  (lookup 'bam (uncover-types test-prog1)) ;; => 'Integer

  (define test-prog2
    '(program (v.1 f.1 r.1)
              (type Integer)
              (defines
                (define (foo [bar : Integer]) : Integer
                  (r.2)
                  (assign r.2 (+ bar 2))
                  (return r.2)))
              (assign v.1 (vector (function-ref foo)))
              (assign f.1 (vector-ref v.1 0))
              (assign r.1 (app f.1 40))
              (return r.1)))

  (match-define `(,global-env (,foo-local-env) ,prog-local-env)
    (uncover-types test-prog2))

  (lookup 'foo global-env)     ;; => '(Integer -> Integer)
  (lookup 'r.1 prog-local-env) ;; => 'Integer
  (lookup 'r.2 foo-local-env)  ;; => 'Integer
  )



;; uncover-types infers the type environment containing all variables in prog.
;; This code assumes that variables have explicitly one type, but
;; may be assigned multiple times. Any attempt to assign the
;; same variable multiple times will result in a runtime error
;; with a message about the type conflict.
;; uncover-types : prog -> (listof (pairof id type))
(define (uncover-types prog)
  (match prog
    [`(program (,xs ...) (type ,ty) (defines ,ds ...) ,ss ...)
     ;; first collect all the defines into a flat global environment
     (let* ([g-env (for/hash ([d ds])
                     (match d
                       [`(define (,f [,x* : ,t*] ...) : ,t . ,r)
                        (values f `(,@t* -> ,t))]
                       [else (error 'uncover-type "unmatched ~a" d)]))]
            ;; Then proccess each define
            [l-env* (for/list ([d ds])
                      (hash->list (uncover-types-define d g-env)))]
            [l-env ((uncover-types-seq (hash) g-env) ss)])
        (list (hash->list g-env) l-env* (hash->list l-env)))]
    [`(program (,xs ...) (type ,ty) . ,ss)
     (let ([env ((uncover-types-seq (hash) 'no-global-env) ss)])
       (for ([x (in-list xs)])
         (let ([err (lambda ()
                      (error 'uncover-type "failed to find ~a" x))])
           (hash-ref env x err)))
       ;; Feel free to remove this if you prefer working
       ;; with hashtable instead.
       (hash->list env))]
    [else (error 'uncover-type "unmatched ~a" prog)]))

;; Return the local environment for a define
(define (uncover-types-define def g-env)
  (match def
    [`(define (,f [,x* : ,t*] ...) : ,t
        (,l* ...) ,s* ...)
     (let* ([x.t* (map cons x* t*)]
            [f.t  `(,f . (,@t* -> ,t))]
            [l-env  (make-immutable-hash (cons f.t x.t*))]
            [l-env^ ((uncover-types-seq l-env g-env) s*)])
       (for ([l (in-list l*)])
         (hash-ref l-env^ l (thunk (error 'unbound "~a" l))))
       l-env^)]
    [else (error 'uncover-type "unmatched ~a" def)]))

;; Build an type environment for all the variables assigned in the
;; sequence of statements.
;; uncover-types-seq :
;;      (hashtable id type) -> (listof stmt) -> (hashtable id type)
(define ((uncover-types-seq l-env g-env) ss)
  (foldl (uncover-types-stmt g-env) l-env ss))

;; Build an environment extending the given env with any
;; variables assigned in stmt.
;; uncover-types-stmt : stmt (hashtable id type) -> (hashtable id type)
(define ((uncover-types-stmt g-env) stmt l-env)
  ;; Associate var with type in env but ensure it doesn't
  ;; conflict with any other type that we uncovered previously.
  (define (env-set env var type)
    (let ([ty? (hash-ref env var #f)])
      (cond
        [(not ty?) (hash-set env var type)]
        [(equal? type ty?) env]
        [else
         (error 'uncover-types
                "conflicting types for ~a, ~a and ~a"
                var type ty?)])))
  (match stmt
    [`(assign ,(? symbol? lhs) ,(app (uncover-type-exp l-env g-env) t))
     (match t
       ;; This line is expiremental.
       ;; By not adding Void types to the environment we ensure
       ;; that any attempt to reference them will result in an
       ;; internal compiler error, a further advantage is that the
       ;; environment locals form for your ASTs will be smaller
       ;; Feel free to uncomment if you want these properties.
       ;; ['Void env]
       [other (env-set l-env lhs t)])]
    [`(if ,t
          ,(app (uncover-types-seq l-env g-env) c-env)
          ,(app (uncover-types-seq l-env g-env) a-env))
     ;; Merge resulting environments making sure that they agree
     ;; any error here would be the result of assinging a variable
     ;; with different types in each branch. 
     (for/fold ([l-env c-env]) ([(k v) (in-hash a-env)])
       (env-set l-env k v))]
    [otherwise l-env]))

;; Reconstruct the type of expr given the current type environment
;; uncover-type-exp : (hashtable id type) -> expr -> type
(define ((uncover-type-exp l-env g-env) expr)
  ;; Find the type of var in env
  (define (env-ref env var)
    (let ([err (thunk (error 'uncover-types "unbound ~a in ~a" var env))])
      (hash-ref env var err)))
  ;; Is x a primitive in the compiler?
  ;; This should be probabaly be replaced by some global helper
  ;; with an extensible list.
  (define (primitive? x)
    (set-member? '(+ - * read and or not eq?) x))
  (match expr
    [(? symbol? x)  (env-ref l-env x)]
    [`(function-ref ,f) (env-ref g-env f)]
    [`(app ,(app (uncover-type-exp l-env g-env) t) ,_ ...)
     (match t
       [`(,_ ... -> ,g) g]
       [else (error 'uncover-type-exp "unmatched funtion type ~a" t)])]
    [`(allocate ,l ,t) t]
    [`(vector ,(app (uncover-type-exp l-env g-env) t*) ...) `(Vector ,@t*)] 
    [`(vector-ref ,(app (uncover-type-exp l-env g-env) `(Vector ,t* ...)) ,i)
     (list-ref t* i)]
    [`(vector-set! ,v ,i ,e) 'Void]
    [(? integer?)  'Integer]
    [(? boolean?)  'Boolean]
    [`(,(? primitive? op) ,_ ...)
     (case op
       [(+ - * read) 'Integer]
       [(and or not eq?) 'Boolean])]
    [else (error 'uncover-types-expr "unmatched ~v" expr)]))
