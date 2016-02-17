#lang racket
(require "conditionals.rkt"
         "interp.rkt"
         "utilities.rkt"
         "runtime-config.rkt"
         "uncover-types.rkt")

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
    ;; expose allocation : C1 -> ?

    (define/public (expose-allocation)
      (lambda (x)
        (match x
          [`(program (,xs ...) (type ,ty) . ,ss)
           ;;(define-values (ss^ env^) ((expose-allocation-seq env) ss))
           (let*-values ([(ss^ env^) (expose-allocation-seq ss (hash))]
                         [(xs) (append xs (reset-vars))])
             (when (at-debug-level? 1)
               (for ([x xs])
                 (unless (hash-ref env^ x #f)
                   (error 'expose-allocation "var not in env ~a" x)))
               (let ([env^^ (make-immutable-hash (uncover-types x))])
                 (for ([(k v) (in-hash env^)])
                   (or (eq? 'Void v)
                       (let ([v? (hash-ref env^^ k #f)])
                         (and v? (eq? v v?)))))))
             (let ([xs (hash->list env^)])
               `(program ,xs (type ,ty)
                         (initialize ,(rootstack-size) ,(heap-size))
                         ,@ss^)))]
          [else (error 'expose-allocation "umatched ~a" x)])))
    
    ;; Follow the control flow, build the environment, and return
    ;; expression rebuilt using types from environment.
    (define/public (expose-allocation-seq ss env)
      (match ss
          ['() (values '() env)]
          [(cons s ss) 
           (let*-values ([(s^  env^)  (expose-allocation-stmt s env)]
                         [(ss^ env^^) (expose-allocation-seq  ss env^)])
             (values (append s^ ss^) env^^))]
          [else (error 'expose-allocation-seq)]))
    
    (define/public (expose-allocation-stmt stmt env)
      (match stmt
            [`(assign ,lhs ,e)
           (define t ((uncover-type-expr env) e))
           (define env^ (env-set env lhs t))
           (match* (e t)
             [(`(vector ,e* ...) `(Vector ,t* ...))
              (define len  (length e*))
              (define size (* (+ len 1) 8))
              (define-values (inits vars)
                (for/lists (i* v*)
                           ([e (in-list e*)]
                            [n (in-naturals)])
                  (let ([v (unique-var 'void)])
                    (values `(assign ,v (vector-set! ,lhs ,n ,e)) v))))
              (define env^^
                (for/fold ([env^ env^]) ([v (in-list vars)])
                  (hash-set env^ v 'Void)))
              (values
               `((if (collection-needed? ,size)
                     ((collect ,size))
                     ())
                 (assign ,lhs (allocate ,len ,t))
                 ,@inits)
               env^^)]
             [(e t) (values `(,stmt) env^)])]
            [`(if ,t ,c ,a)
             (let-values ([(c c-env) (expose-allocation-seq c env)]
                          [(a a-env) (expose-allocation-seq a env)])
               (values `((if ,t ,c ,a)) (env-merge c-env a-env)))]
            [`(return ,e) (values `(,stmt) env)]
            [else (error 'expose-allocation-stmt "unmatched ~a" stmt)]))
      
    
    ;; Return the type of an expression given a type environment
    (define/public (uncover-type-expr env)
      (define (recur e)
        (match e
          [(? symbol? x)  (env-ref env x)]
          [`(allocate ,l ,t) t]
          [`(vector ,(app recur t*) ...) `(Vector ,@t*)]
          ;; I has to be a literal integer
          [`(vector-ref ,(app recur `(Vector ,t* ...)) ,i)
           (list-ref t* i)]
          [(? integer?)  'Integer]
          [(? boolean?)  'Boolean]
          [(list (? primitive? op) _ ...)
           (case op
             [(+ - * read) 'Integer]
             [(and or not eq?) 'Boolean])]
          [other (error 'uncover-type-expr "unmatched ~v" other)]))
      recur)
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots : (hashtable id type) (set id) -> C1-Expr  -> C1-Expr x (set id)
    ;; This is a reimplementation of type check which could be fixed if we ellaborated
    ;; the types at every previous step in the compiler.
   
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
        [else (error 'vectors/uncover-call-live-root-seq "unmatched ~a" x)])))
  
  (define/public (uncover-call-live-roots env clr*)
    ;; This pass could do better if it had most of the type information precomputed
    (lambda (x)
      ;; Recursion case were the call live root set is threaded through
      (define (recur x) ((uncover-call-live-roots env clr*) x))
      ;; Recursion where the call live root set is left empty.
      ;; This is usually done because it is known that multiple sets derived
      ;; through the recursive case will be combined.
      (define (recur/mt-clt) ((uncover-call-live-roots env clr*) x))
      (vomit "uncover call live roots" x env clr*)
      (match x
        ;; Base Case for list recusion -- the starting root set is the live root set
        [`(program ,x.ts ,ty ,ss ...)
         (let*-values ([(new-env) (make-immutable-hash x.ts)]
                       [(ss clr*) ((uncover-call-live-seq new-env clr*) ss)]
                       [(xs)  (map car x.ts)]
                       [(xs^) (reset-vars)])
           (unless (set-empty? clr*)
             (error 'uncover-call-live-roots 
                    "empty program call live roots invariant ~a" clr*))
           `(program ,(append xs xs^) ,ty ,@ss))]
        ;; Remove variables when they are assigned
        [`(assign ,v ,e) ;; v is not live in e
         (let*-values ([(clr*)   (set-remove clr* v)]
                       [(e clr*) ((uncover-call-live-roots env clr*) e)])
           (values `(assign ,v ,e) clr*))]
        ;; The union of both branches are still alive
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
        [`(,(? primitive? op) ,(app (uncover-call-live-roots env (set)) e* clr**) ...)
         (values `(,op ,@e*) (set-union clr* (set-union* clr**)))]     
        [else (error 'vectors/uncover-call-live-roots "unmatched ~a" x)])))

  ;; root? returns true if x is a root or false otherwise.
  ;; root? : (Hashtable id type) id -> boolean
  (define/public (root? env x)
    (let* ([e (lambda () (error 'root? "unbound ~a" x))]
           [t (hash-ref env x e)])
      (root-type? t)))

  (define/public (root-type? t)
    (and (pair? t) (eq? (car t) 'Vector)))

  ;; Merge two hash tables that do not have contradictory key/value pairs
  (define/public (env-merge e1 e2)
    ;; add each of the keys in e2 to e1
    (for/fold ([e1 e1]) ([(k v) (in-hash e2)])
      ;; but first check to see if the key already exists in e1
      (let ([v? (hash-ref e1 k #f)])
        (cond
          ;; If it doesn't exist just add the key value pair
          [(not v?) (hash-set e1 k v)]
          ;; if it does exits make sure the values are equal?
          [(equal? v? v) e1]
          [else
           (error 'env-merge "inconsistent environments ~a ~a" e1 e2)]))))

  (define/public (env-ref env x)
    (hash-ref env x (lambda () (error 'env-ref "unmatched ~a" x))))
  
  (define/public (env-set env k v)
    (let ([v? (hash-ref env k #f)])
      (if (and v? (not (equal? v v?)))
          (error 'env-set "~a : ~a is inconsistent with ~a" k v env)
          (hash-set env k v))))


  ;; vars is a private field holding freshly allocated variables that
  ;; can be accessed throught the reset-vars, reset-vars, and unique-var
  ;; methods.
  (define vars (box '()))

  ;; create and remember a new unique variable
  (define/public (unique-var [x 'u] [t? #f])
    (let ((x (gensym x))
          (old-vars (unbox vars)))
      (if t?
          (set-box! vars `((,x . ,t?) ,old-vars))
          (set-box! vars `(,x . ,old-vars)))
      x))

  ;; look at the current state of vars
  (define/public (get-new-vars) (unbox vars))

  ;; reset and retrieve the current state of vars
  (define/public (reset-vars)
    (let ((tmp (unbox vars)))
      (set-box! vars '())
      tmp))
  
  (define (set-union* ls)
    (foldr set-union (set) ls))

  (define (primitive? x)
    (set-member? (send this primitives) x))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; select-instructions : C2 -> psuedo-x86

  (define/override (select-instructions [rs-var 'Unknown])
    (define (known-invariant rs-var x)
      (when (eq? 'Unkown rs-var)
        (error 'select-instructions "known invariant broken ~a" x)))
    (lambda (x)
      (vomit "select instructions" x vars)
      (match x
        [`(call-live-roots (,clr* ...) . ,ss)
         (if (null? clr*)
             (append* (map (select-instructions rs-var) ss))
             (let ([rs-var^ (unique-var 'rootstack)]
                   [frame-size  (* (length clr*) 8)]
                   [pushes
                    (for/list ([root (in-list clr*)] [i (in-naturals)])
                      `(movq (var ,root) (offset (var ,rs-var) ,(* i 8))))]
                   [pops
                    (for/list ([root (in-list clr*)] [i (in-naturals)])
                      `(movq (offset (var ,rs-var) ,(* i 8)) (var ,root)))])
               `(,@pushes
                 (movq (var ,rs-var) (var ,rs-var^))
                 (addq (int ,frame-size) (var ,rs-var^))
                 ,@(append* (map (select-instructions rs-var^) ss))
                 ,@pops)))]
        [`(initialize ,s ,h)
         (known-invariant rs-var x)
         `((movq (int ,s) (reg rdi))
           (movq (int ,h) (reg rsi))
           (callq initialize)
           (movq (global-value rootstack_begin) (var ,rs-var)))]
        [`(collect ,size)
         (known-invariant rs-var x)
         `((movq (var ,rs-var) (reg rdi))
           (movq ,((select-instructions rs-var) size) (reg rsi))
           (callq collect))]
        [`(assign ,lhs (allocate ,length (Vector ,ts ...)))
         (define lhs^ ((select-instructions rs-var) lhs))
         ;; Add one quad word for the meta info tag
         (define size (* (add1 length) 8))
         ;;highest 7 bits are unused
         ;;lowest 1 bit is 0 saying this is not a forwarding pointer
         (define is-not-forward-tag 1)
         ;;next 6 lowest bits are the length
         (define length-tag (arithmetic-shift length 1))
         ;;bits [6,56] are a bitmask indicating if [0,50] are pointers
         (define ptr-tag
           (for/fold ([tag 0]) ([t (in-list ts)] [i (in-naturals 7)])
             (bitwise-ior tag (arithmetic-shift (b2i (root-type? t)) i))))
         ;; Combine the tags into a single quad word
         (define tag (bitwise-ior ptr-tag length-tag is-not-forward-tag))
         `((movq (global-value free_ptr) ,lhs^)
           (addq (int ,size) (global-value free_ptr))
           (movq (int ,tag) (offset ,lhs^ 0)))]
        [`(if (collection-needed? ,size) ,cs ,as)
         (define cs^  (append* (map (select-instructions rs-var) cs)))
         (define as^  (append* (map (select-instructions rs-var) as)))
         (define data (unique-var 'end-data))
         (define lt   (unique-var 'lt))
         `((movq (global-value free_ptr) (var ,data))
           (addq (int ,size) (var ,data))
           (cmpq (var ,data) (global-value fromspace_end))
           (setl (byte-reg al))
           (movzbq (byte-reg al) (var ,lt))
           #| purposefully fliped clauses because we want (not lt)|#
           (if (eq? (int 0) (var ,lt)) ,as^ ,cs^))]
        [`(assign ,lhs (vector-ref ,e-vec ,i))
         (define lhs^ ((select-instructions rs-var) lhs))
         (define e-vec^ ((select-instructions rs-var) e-vec))
         `((movq (offset ,e-vec^ ,(* (add1 i) 8)) ,lhs^))]
        [`(assign ,lhs (vector-set! ,e-vec ,i ,e-arg))
         (define new-lhs ((select-instructions rs-var) lhs))
         (define new-e-vec ((select-instructions rs-var) e-vec))
         (define new-e-arg ((select-instructions rs-var) e-arg))
         `((movq ,new-e-arg (offset ,new-e-vec ,(* (add1 i) 8))))]
        ;; If has to be overridden because it needs to propagate
        [`(if ,cnd ,thn-ss ,els-ss)
         (let ([cnd ((select-instructions rs-var) cnd)]
               [thn-ss (append* (map (select-instructions rs-var) thn-ss))]
               [els-ss (append* (map (select-instructions rs-var) els-ss))])
           `((if ,cnd ,thn-ss ,els-ss)))]
        [`(program ,xs (type ,ty) . ,ss)
         (define rs-var (unique-var 'rootstack))
         (define ss^ (append* (map (select-instructions rs-var) ss)))
         `(program ,(append xs (reset-vars)) (type ,ty) ,@ss^)]
        [otherwise ((super select-instructions) otherwise)])))

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
      [`(movq ,s (offset ,d ,i)) (set)]
      [`(setl ,d) (send this free-vars d)]
      [else (super write-vars x)]))
  
  (define/override (read-vars x)
    (match x
      [`(movq ,s (offset ,d ,i)) (set-union (free-vars s) (free-vars d))]
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
          [else ((super assign-homes homes) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : psuedo-x86 -> x86

(define/override (on-stack? a)
  (match a
    [`(offset ,e ,i) #t]
    [`(global-value ,l) #t]
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
    `(
;    ("type-check" ,(send compiler type-check '())
;       ,(send interp interp-scheme '()))
      ("uniquify" ,(send compiler uniquify '())
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-C '()))
      ("uncover call live roots"
       ,(send compiler uncover-call-live-roots (hash) (set))
       ,(send interp interp-C '()))
      ("instruction selection"
       ,(send compiler select-instructions 'rootstack)
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
