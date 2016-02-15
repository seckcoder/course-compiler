#lang racket

(provide uncover-types)
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
  
  (define test-prog
    '(program (foo bar baz bam)
              (type Integer)
              (assign foo (vector 777))
              (assign bar (vector foo foo))
              (assing _   (vector-set! foo 0 42))
              (assign baz (vector-ref bar 1))
              (assign bam (vector-ref baz 0))
              (return bam)))

  (lookup 'foo (uncover-types test-prog)) ;; => 'Integer
  (lookup 'baz (uncover-types test-prog)) ;; => '(Vector Integer)
  (lookup 'bam (uncover-types test-prog)) ;; => 'Integer
)



;; uncover-types infers the type environment containing all variables in prog.
;; This code assumes that variables have explicitly one type, but
;; may be assigned multiple times. Any attempt to assign the
;; same variable multiple times will result in a runtime error
;; with a message about the type conflict.
;; uncover-types : prog -> (listof (pairof id type))
(define (uncover-types prog)
  ;; Body of uncover-type
  (match prog
    [`(program (,xs ...) (type ,ty) . ,ss)
     (let ([env ((uncover-types-seq (hash)) ss)])
       (for ([x (in-list xs)])
         (let ([err (lambda ()
                      (error 'uncover-type "failed to find ~a" x))])
           (hash-ref env x err)))
       ;; Feel free to remove this if you prefer working
       ;; with hashtable instead.
       (hash->list env))]
    [else (error 'uncover-type "unmatched ~a" prog)]))



;; Build an type environment for all the variables assigned in the
;; sequence of statements.
;; uncover-types-seq :
;;      (hashtable id type) -> (listof stmt) -> (hashtable id type)
(define ((uncover-types-seq env) ss) (foldl uncover-types-stmt env ss))

;; Build an environment extending the given env with any
;; variables assigned in stmt.
;; uncover-types-stmt : stmt (hashtable id type) -> (hashtable id type)
(define (uncover-types-stmt stmt env)
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
    [`(assign ,(? symbol? lhs) ,(app (uncover-type-exp env) t))
     (match t
       ;; This line is expiremental.
       ;; By not adding Void types to the environment we ensure
       ;; that any attempt to reference them will result in an
       ;; internal compiler error, a further advantage is that the
       ;; environment locals form for your ASTs will be smaller
       ;; Feel free to uncomment if you want these properties.
       ;; ['Void env]
       [other (env-set env lhs t)])]
    [`(if ,t
          ,(app (uncover-types-seq env) c-env)
          ,(app (uncover-types-seq env) a-env))
     ;; Merge resulting environments making sure that they agree
     ;; any error here would be the result of assinging a variable
     ;; with different types in each branch. 
     (for/fold ([env c-env]) ([(k v) (in-hash a-env)])
       (env-set env k v))]
    [otherwise env]))

;; Reconstruct the type of expr given the current type environment
;; uncover-type-exp : (hashtable id type) -> expr -> type
(define ((uncover-type-exp env) expr)
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
    [(? symbol? x)  (env-ref env x)]
    [`(allocate ,l ,t) t]
    [`(vector ,(app (uncover-type-exp env) t*) ...) `(Vector ,@t*)] 
    [`(vector-ref ,(app (uncover-type-exp env) `(Vector ,t* ...)) ,i)
     (list-ref t* i)]
    [`(vector-set! ,v ,i ,e) 'Void]
    [(? integer?)  'Integer]
    [(? boolean?)  'Boolean]
    [`(,(? primitive? op) ,_ ...)
     (case op
       [(+ - * read) 'Integer]
       [(and or not eq?) 'Boolean])]
    [else (error 'uncover-types-expr "unmatched ~v" expr)]))
