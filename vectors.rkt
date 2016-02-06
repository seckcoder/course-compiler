#lang racket
(require "conditionals.rkt"
         "interp.rkt"
         "utilities.rkt"
         "runtime-config.rkt")

(provide compile-R2 vectors-passes vectors-typechecker)

(define compile-R2
  (class compile-R1
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'vector 'vector-ref 'vector-set!)))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S2 -> S2    
    (define/override (type-check env)
      (lambda (e)
        (vomit "vectors/type-check" e env)
	(match e
          [`(vector ,es ...)
           `(Vector ,@(map (send this type-check env) es))]
          [`(vector-ref ,e-vec ,i)
           (define t ((send this type-check env) e-vec))
           (match t
             [`(Vector ,ts ...)
              (unless (i . < . (length ts))
                (error "index too large for vector-ref:" i))
              (list-ref ts i)]
             [else (error "expected a vector in vector-ref, not" t)])]
          [`(vector-set! ,e-vec ,i ,e-arg)
           (define t ((send this type-check env) e-vec))
           (define t-arg ((send this type-check env) e-arg))
           (match t
             [`(Vector ,ts ...)
              (unless (i . < . (length ts))
                (error "index too large for vector-set!:" i))
              (unless (equal? (list-ref ts i) t-arg)
                (error "type mismatch in vector-set!" 
                       (list-ref ts i) t-arg)) ]
             [else (error "expected a vector in vector-set!, not" t)])]
          [`(eq? ,e1 ,e2)
           (match `(,((send this type-check env) e1)
                    ,((send this type-check env) e2))
             [`((Vector ,ts1 ...) (Vector ,ts2 ...))
              'Boolean]
             [else ((super type-check env) e)])]
          [else ((super type-check env) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniqueify : S1 -> C1-expr x (C1-stmt list)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S1 -> C1-expr x (C1-stmt list)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots : (hashtable id type) (set id) -> C1-Expr  -> C1-Expr x (set id)
    ;; This is a reimplementation of type check which could be fixed if we ellaborated
    ;; the types at every previous step in the compiler.
   
    ;; root? returns true if x is a root or false otherwise.
    ;; root? : (Hashtable id type) id -> boolean
    (define/public (root? env x)
      (let* ([e (lambda () (error 'root? "unbound ~a" x))]
             [t (hash-ref env x e)])
        (root-type? t)))

    (define/public (root-type? t)
      (and (pair? t) (eq? (car t) 'Vector)))

    ;; This is the clause that processes expressions
    ;; It returns the type and any live roots of the expression.
    (define (set-union* l*) (foldl set-union (set) l*))
    (define (primitive? x) (set-member? (send this primitives) x))

    #;
    (define/public (uncover-type-exp env)
    (define (recur x) ((uncover-type-exp env) x))
    (lambda (e)
      (match e
        [(? symbol? x)  (env-ref env x)]
        [`(vector ,(app recur t*) ...) `(Vector ,@t*)]
        ;; I has to be a literal integer ;
        [`(vector-ref ,(app recur `(Vector ,t* ...)) ,i)
         (list-ref t* i)]
        [(? integer?)  `Integer]
        [(? boolean?)  `Boolean]
        [`(,(? primitive? op) ,_ ...)
         (case op
           [(+ - * read) 'Integer]
           [(and or not eq?) 'Boolean])]
        [else (error 'uncover-live-roots-exp "unmatched ~a" e)])))

  ;; Uncover the 
  (define/public (uncover-env-stmt env)
    (define (stmt s env) ((uncover-env-stmt env) s))
    (lambda (s)
      (vomit "uncover env statement" s env)
      (flush-output)
      (match s
        [`(assign ,v ,(app (uncover-type-exp env) t)) (env-set env v t)]
        [`(if ,r ,c ,a) (env-merge (foldl stmt env c) (foldl stmt env a))]
        [otherwise env])))

  (define/public (uncover-call-live-seq env clr*)
    ;; This pass could do better if it had most of the type information precomputed
    (lambda (x)
      (vomit "uncover call live sequence" x env clr*)
      (match x
        ;; Base Case for list recusion -- the starting root set is the live root set
        ['() (values '() clr*)]
        ;; env is collected and forward threaded through the recursion
        ;; then lives are collected through each return and used to
        ;; rebuild the ast at each step
        [(cons s ss)           
         (let*-values ([(ss clr*) ((uncover-call-live-seq env clr*) ss)]
                       [(s  clr*) ((uncover-call-live-roots env clr*) s)])
           (vomit "let body" env ss s clr*)
           (values `(,s . ,ss) clr*))
         #;
         (let ([env^ ((uncover-env-stmt env) s)])
         (vomit "in let" env env^) (flush-output)
         )]          
      [else (error 'vectors/introduce-rootset "unmatched ~a" x)])))

(define/public (uncover-call-live-roots env clr*)
  ;; This pass could do better if it had most of the type information precomputed
  (lambda (x)
    (define (recur x) ((uncover-call-live-roots env clr*) x))
    (vomit "uncover call live roots" x env clr*)
    (match x
      ;; Base Case for list recusion -- the starting root set is the live root set
      [`(program ,x.ts ,ss ...)
       (vomit "uncover call live program")
       (let ([v* (get-vars)])
         (unless (null? v*)
           (error 'uncover-call-live-roots
                  "empty vars invariant" v*)))
       (let*-values ([(new-env) (make-immutable-hash x.ts)]
                     [(ss clr*) ((uncover-call-live-seq new-env clr*) ss)]
                     [(xs)  (map car x.ts)]
                     [(xs^) (get-vars)])
         (unless (set-empty? clr*)
           (error 'uncover-call-live-roots 
                  "empty program call live roots invariant ~a" clr*))
         `(program ,(append xs xs^) ,@ss))]
      ;; Remove variables when they are assigned
      [`(assign ,v ,e) ;; v is not live in e
       (vomit "uncover call live program")
       (let*-values ([(clr*)   (set-remove clr* v)]
                     [(e clr*) ((uncover-call-live-roots env clr*) e)])
         (values `(assign ,v ,e) clr*))]
      ;; The union of both branches are still allive
      [`(if ,t ,c* ,a*)
       (vomit "uncover call live if")
       (let-values ([(c* c-clr*) ((uncover-call-live-seq env clr*) c*)]
                    [(a* a-clr*) ((uncover-call-live-seq env clr*) a*)])
         (let*-values ([(b-clr*) (set-union c-clr* a-clr*)]
                       [(t clr*) ((uncover-call-live-roots env b-clr*) t)])
           (values `(if ,t ,c* ,a*) clr*)))]
      [`(return ,(app recur e lr*)) (values `(return ,e) lr*)]
      ;; Exp Cases
      [(? symbol? x)
       (values x (if (root? env x) (set-add clr* x) clr*))]
      [(or (? integer? x) (? boolean? x)) (values x clr*)]
      [(and x `(allocate ,l ,t)) (values x clr*)]
      [(and x `(collect ,size))
       (define call-live-roots (set->list clr*))
       (values `(call-live-roots ,call-live-roots
                                 (collect ,size))
               clr*)]
      [`(initialize ,stack ,heap)
       (unless (set-empty? clr*)
         (error 'uncover-call-live-roots
                "call live roots exist during initialization of rootstack"))
       (values `(initialize ,stack ,heap) (set))]
      [`(collection-needed? ,size) (values x clr*)]
      [`(,(? primitive? op)
         ,(app (uncover-call-live-roots env (set)) e* clr**) ...)
       (values `(,op ,@e*) (set-union clr* (set-union* clr**)))]

      #|
      [`(vector-set! ,(app recur e1 lr*) ,i
      ,(app (uncover-call-live-roots env (set)) e2 clr*^))
      (values `(vector-set! ,e1 ,i ,e2) (set-union clr* clr*^))]
      [`(vector ,(and (app (uncover-type-exp env) t*)
      (app (uncover-call-live-roots env (set)) e* clr**))
      ...)
      (let ([clr* (set-union clr* (set-union* clr**))]
      [type `(Vector ,@t*)])
      (values `(vector ,clr* ,type ,@e*) clr*))]
      [`(vector-ref ,(app (uncover-call-live-roots env clr*) e lr*) ,i)
      (values `(vector-ref ,e ,i) lr*)]
      |#
     
      [else (error 'vectors/uncover-call-live-roots "unmatched ~a" x)])))

;; Merge two hash tables that do not have contradictory key/value pairs
(define (env-merge e1 e2)
  (vomit "env-merge" e1 e2)
  (define res
    ;; add each of the keys in e2 to e1
    (for/fold ([e1 e1]) ([(k v) (in-hash e2)])
      ;; but first check to see if the key already exists in e1
      (let ([v? (hash-ref e1 k #f)])
        (cond
          ;; If it doesn't exist no problem just add the key value pair
          [(not v?) (hash-set e1 k v)]
          ;; if it does exits make sure the values are equal?
          [(equal? v? v) e1]
          [else
           (error 'env-merge "inconsistent environments ~a ~a" e1 e2)]))))
  (vomit "env-merge" res)
  res)

(define (env-ref env x)
  (hash-ref env x (lambda () (error 'env-ref "unmatched ~a" x))))

(define (env-set env k v)
  (let ([v? (hash-ref env k #f)])
    (if (and v? (not (equal? v v?)))
        (error 'env-set "~a : ~a is inconsistent with ~a" k v env)
        (hash-set env k v))))

(define vars (box '()))
(define (get-vars)
  (let ((tmp (unbox vars)))
    (set-box! vars '())
    tmp))
(define (unique-var [x 'u])
  (let ((tmp (gensym x)))
    (set-box! vars (cons tmp (unbox vars)))
    tmp))

(define/public (uncover-type-exp env)
  (define (recur x) ((uncover-type-exp env) x))
  (lambda (e)
    (vomit "uncover-type-exp" e env)
    (match e
      [(? symbol? x)  (env-ref env x)]
      [`(allocate ,l ,t) t]
      [`(vector ,(app recur t*) ...) `(Vector ,@t*)]
      ;; I has to be a literal integer
      [`(vector-ref ,(app recur `(Vector ,t* ...)) ,i)
       (list-ref t* i)]
      [(? integer?)  `Integer]
      [(? boolean?)  `Boolean]
      [`(,(? primitive? op) ,_ ...)
       (case op
         [(+ - * read) 'Integer]
         [(and or not eq?) 'Boolean])]
      [else (error 'uncover-live-roots-exp "unmatched ~a" e)])))

(define/public (expose-allocation env)
  (define (recur x) ((expose-allocation) x))
  (lambda (x)
    (vomit "expose allocation" x env)
    (match x
      [`(program ,xs . ,ss)
       (vomit "expose allocation program" xs ss)
       (define-values (ss^ env^) ((expose-allocation-seq env) ss))
       (define xs^ (append xs (get-vars)))
       (for ([x xs^])
         (unless (hash-ref env^ x #f)
           (error 'expose-allocation "type inference invalid ~a" x)))
       (let ([xs-t (hash->list env^)])
         `(program ,xs-t (initialize ,(rootstack-size) ,(heap-size))
                   . ,ss^))]
      [`(assign ,lhs (vector ,(and (app (uncover-type-exp env) t*) e*) ...))
       (vomit "expose allocation assign" lhs t* e*)
       (let* ([length (length e*)]
              [size (* (+ length 1) 8)]
              [type `(Vector ,@t*)])
         (define-values (inits vars)
           (for/lists (i* v*)
                      ([e (in-list e*)]
                       [n (in-naturals)])
             (let ([void (unique-var 'void)])
               (values `(assign ,void (vector-set! ,lhs ,n ,e))
                       void))))
         (define new-env
           (for/fold ([env env]) ([v (in-list vars)])
             (hash-set env v 'Void)))
         (values
          `((if (collection-needed? ,size)
                ((collect ,size))
                ())
            (assign ,lhs (allocate ,length ,type))
            ,@inits)
          (env-set new-env lhs type)))]
      [`(assign ,lhs ,(app (uncover-type-exp env) t))
       (vomit "expose allocation assign" lhs t)
       (values (list x) (env-set env lhs t))]
      [`(if ,t ,c ,a)
       (vomit "expose allocation if" t c a env)
       (let-values ([(c c-env) ((expose-allocation-seq env) c)]
                    [(a a-env) ((expose-allocation-seq env) a)])
         (vomit "expose allocation if 2" c a c-env a-env)
         (values `((if ,t ,c ,a)) (env-merge c-env a-env)))]
      [otherwise
       (vomit "expose allocation other")
       (values `(,x) env)])))

(define/public (expose-allocation-seq env)
  (lambda (ss)
    (vomit "expose allocation sequence" ss env)
    (match ss
      ['()
       (vomit "null")
       (values '() env)]
      [(cons s ss)
       (vomit "cons" s ss)
       (let*-values ([(s^  env^)  ((expose-allocation env) s)]
                     [(ss^ env^^) ((expose-allocation-seq env^) ss)])
         (values (append s^ ss^) env^^))]
      [else (error 'expose-allocation-seq)])))

#|
(define initializers
  ;; Starts at 1 because the tag is in the first cell
  (cons
   `(movq (int ,meta-tag) (offset ,new-lhs 0))
   (for/list ([e new-es] [i (in-range 1)])
     #;(when (vector-type? e)
     (error 'vectors/select-instructions "need find all vector types"))
     ;; Need to add the code here for setting the tag bits
     `(movq ,e (offset ,new-lhs ,(* i 8))))))

#;
`((movq (int ,bytes) (reg rdi))
(callq alloc)
(movq (reg rax) ,new-lhs)
. ,initializers)

`(;; rdi is the rootstack pointer in all racket calls
;; Get the next free memory locations
(movq (global-value free_ptr) (reg rcx))
;; Create a copy so that if the check succeeds we can set new-lhs
(movq (reg rcx) (reg rdx))
;; Put the number of bytes in the second argument register
;; if the check fails we are now ready to call collect
(movq (int ,bytes) (reg rsi))
;; Add bytes to free ptr to find the end of allocated memory
;; rcx is chosen because it isn't needed to call collect
;; but it must be ready if the check succeeds to store as the new
;; free pointer.
(addq (reg rsi) (reg rcx))
;; Get the end of the allocation space
(movq (global-value fromspace_end) (reg rax))
;; perform the comparison
(cmpq (reg rcx) (reg rax))
;; check the less than flag
;; al is chosen because it will be smashed by the if
(setl (byte-reg al))
;; scale the value up to proper size
(movzbq (byte-reg al) (reg r8))
(if (reg r8)
    ((movq (reg rcx) (global-value free_ptr))
     (movq (reg rdx) ,new-lhs))
    ;; rdi has root stack
    ;; rsi has bytes to allocate
    ((callq debug_collect)
     (movq (reg rax) (reg rsi))
     (movq (reg rax) ,new-lhs)
     (addq (int ,bytes) (reg rsi))
     (movq (reg rsi) (global-value free_ptr))))
,@initializers)]
[`(,s . ,ss)
 |#
 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; introduce-rootset : Uid -> stmt -> (listof stmt)

 ;; do not split live ranges of variable at call sites
 (define/public (introduce-rootstack rs-var)
   (lambda (x)
     (define (recur x) ((introduce-rootstack rs-var) x))
     (match x
       [`(call-live-roots (,clr* ...) (collect ,size))
        (define rs-var^ (unique-var 'rootstack))
        (define frame-size  (* (length clr*) 8))
        (define pushes
          (for/list ([root (in-list clr*)] [i (in-naturals)])
            `(movq (var ,root) (offset (var ,rs-var) ,(* i 8)))))
        ;; reverse order of pushes
        (define pops
          (for/fold ([pops '()]) ([root (in-list clr*)] [i (in-naturals)])
            `((movq (offset (var ,rs-var) ,(* i 8)) (var ,root)) . ,pops)))
        `(,@pushes
          (assign ,rs-var^ (+ ,rs-var ,frame-size))
          (collect ,rs-var^ ,size)
          ,@pops)]
       [`(if ,t (,(app recur c**) ...) (,(app recur a**) ...))
        `((if ,t ,(append* c**) ,(append* a**)))]
       [`(program ,xs (initialize ,stack ,heap) . ,ss)
        (unless (null? (get-vars))
          (error 'introduce-rootstack "empty rootstack invariant"))
        (let* ([x   (unique-var 'rootstack)]
               [s   `(assign ,x (global-value rootstack_begin))]
               [ss  (append* (map (introduce-rootstack x) ss))]
               [xs  (append xs (get-vars))])
          `(program ,xs (initialize ,stack ,heap) ,s . ,ss))]
       [otherwise `(,x)])))
 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; select-instructions : C2 -> psuedo-x86

 (define/override (select-instructions)
   (lambda (x)
     (vomit "select instructions" x vars)
     (match x
       [`(global-value ,l) `(,x)]
       ;; Gets caught in the unary app case otherwise
       [`(assign ,lhs (global-value ,l))
        (define lhs^ ((select-instructions) lhs))
        `((movq (global-value ,l) ,lhs^))]
       [`(initialize ,s ,h)
        `((movq (int ,s) (reg rdi))
          (movq (int ,h) (reg rsi))
          (callq initialize))]
       [`(movq ,lhs ,rhs) `(,x)]
       [`(assign ,lhs (allocate ,length (Vector ,ts ...)))
        (define lhs^ ((select-instructions) lhs))
        (define size (* (add1 length) 8))
        ;;highest 7 bits are unused
        ;;lowest 1 bit is 0 saying this is not a forwarding pointer
        (define isForward-tag 0)
        ;;next 6 lowest bits are the length
        (define length-tag (arithmetic-shift size 1))
        ;;bits [6,56] are a bitmask indicating if [0,50] are pointers
        (define ptr-tag
          (for/fold ([tag 0])
                    ([t (in-list ts)]
                     [i (in-naturals 7)])
            (bitwise-ior tag (arithmetic-shift (b2i (root-type? t)) i))))
        (define tag (bitwise-ior ptr-tag length-tag isForward-tag))
        `((movq (global-value free_ptr) ,lhs^)
          (addq (int ,size) (global-value free_ptr))
          (movq (int ,tag) (offset ,lhs^ 0)))]
       [`(collect ,rs ,size)
        (define rs^ ((select-instructions) rs))
        (define size^ ((select-instructions) size))
        `((movq ,rs^ (reg rdi))
          (movq ,size^ (reg rsi))
          (callq collect))]
       [`(if (collection-needed? ,size) ,cs ,as)
        (define cs^  (append* (map (select-instructions) cs)))
        (define as^  (append* (map (select-instructions) as)))
        (define data (unique-var 'end-data))
        (define lt   (unique-var 'lt))
        (vomit "collection needed?" data lt)
        `((movq (global-value free_ptr) (var ,data))
          (addq (int ,size) (var ,data))
          (cmpq (var ,data) (global-value fromspace_end))
          (setl (byte-reg al))
          (movzbq (byte-reg al) (var ,lt))
          #| purposefully fliped clauses because we want (not lt)|#
          (if (eq? (int 0) (var ,lt)) ,as^ ,cs^))]
       [`(assign ,lhs (vector-ref ,e-vec ,i))
        (define lhs^ ((send this select-instructions) lhs))
        (define e-vec^ ((send this select-instructions) e-vec))
        `((movq (offset ,e-vec^ ,(* (add1 i) 8)) ,lhs^))]
       [`(assign ,lhs (vector-set! ,e-vec ,i ,e-arg))
        (define new-lhs ((send this select-instructions) lhs))
        (define new-e-vec ((send this select-instructions) e-vec))
        (define new-e-arg ((send this select-instructions) e-arg))
        `((movq ,new-e-arg (offset ,new-e-vec ,(* (add1 i) 8))))]
       [`(program ,xs . ,ss)
        (vomit "program" xs)
        (unless (null? (get-vars))
          (error 'select-instructions "empty vars invariant broken"))
        (let* ([ss (append* (map (select-instructions) ss))])
          (let ([xs^ (get-vars)])
            (let ([xs (append xs xs^)])
              (vomit "program" xs xs^)
              `(program ,xs ,@ss))))]
       [else ((super select-instructions) x)]
       )))
 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; uncover-live
 (define/override (free-vars a)
   (match a
     [`(global-value ,l) (set)]
     [`(offset ,e ,i) (send this free-vars e)]
     [else (super free-vars a)]
     ))

 (define/override (write-vars x)
   (match x
     [`(setl ,d) (send this free-vars d)]
     [else (super write-vars x)]))

 (define/override (read-vars x)
   (match x
     [`(setl ,d) (set)]
     [else (super read-vars x)]))
 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86
 (define/override (assign-homes homes)
   (lambda (e)
     (match e
       [`(global-value ,l) e]
       [`(offset ,e ,i)
        (define new-e ((assign-homes homes) e))
        `(offset ,new-e ,i)]
       [`(setl ,e)
        (define new-e ((assign-homes homes) e))
        `(setl ,new-e)]
       [else ((super assign-homes homes) e)]
       )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; patch-instructions : psuedo-x86 -> x86

 (define/override (on-stack? a)
   (match a
     [`(offset ,e ,i) #t]
     [else (super on-stack? a)]))


 (define/override (instructions)
   (set-add (super instructions) 'setl))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; print-x86 : x86 -> string

(define/override (print-x86)
  (lambda (e)
    (match e
      [`(offset (stack ,n) ,i)
       (format "~a(%rbp)" (- i n))]
      [`(offset ,e ,i)
       (format "~a(~a)" i ((send this print-x86) e))]
      [`(global-value ,label)
       (format "~a(%rip)" (label-name (symbol->string label)))]
      [`(setl ,d) (format "\tsetl\t~a\n" ((send this print-x86) d))]
      [else ((super print-x86) e)]
      )))));; compile-R2

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define vectors-typechecker
  (let ([compiler (new compile-R2)])
    (send compiler type-check '())))
(define vectors-passes
  (let ([compiler (new compile-R2)]
	[interp (new interp-R2)])
    `(("type-check" ,(send compiler type-check '())
       ,(send interp interp-scheme '()))
      ("uniquify" ,(send compiler uniquify '())
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("expose allocation"
       ,(send compiler expose-allocation (hash))
       ,(send interp interp-C '()))
      ("uncover call live roots"
       ,(send compiler uncover-call-live-roots (hash) (set))
       ,(send interp interp-C '()))

      ("introduce rootstack"
       ,(send compiler introduce-rootstack 'rootstack)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler build-interference
                                   (void) (void))
       ,(send interp interp-x86 '()))
      ("build move graph" ,(send compiler
                                 build-move-graph (void))
       ,(send interp interp-x86 '()))
      ("allocate registers" ,(send compiler allocate-registers)
       ,(send interp interp-x86 '()))
      ("lower conditionals" ,(send compiler lower-conditionals)
       ,(send interp interp-x86 '()))
      ("patch instructions" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ("print x86" ,(send compiler print-x86) #f)
      )))
