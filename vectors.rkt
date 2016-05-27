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
          ['(void) (values '(has-type (void) Void) 'Void)]
          [`(vector ,(app (type-check env) e* t*) ...)
           (let ([t `(Vector ,@t*)])
             (values `(has-type (vector ,@e*) ,t) t))]
          [`(vector-ref ,(app (type-check env) e t) ,i)
           (match t
             [`(Vector ,ts ...)
              (unless (and (exact-nonnegative-integer? i)
                           (i . < . (length ts)))
		      (error 'type-check "invalid index ~a" i))
              (let ([t (list-ref ts i)])
                (values `(has-type (vector-ref ,e (has-type ,i Integer)) ,t) 
			t))]
             [else (error "expected a vector in vector-ref, not" t)])]
          [`(vector-set! ,(app (type-check env) e-vec^ t-vec) ,i 
			 ,(app (type-check env) e-arg^ t-arg)) 
           (match t-vec
             [`(Vector ,ts ...)
              (unless (and (exact-nonnegative-integer? i)
                           (i . < . (length ts)))
                (error 'type-check "invalid index ~a" i))
              (unless (equal? (list-ref ts i) t-arg)
                (error 'type-check "type mismatch in vector-set! ~a ~a" 
                       (list-ref ts i) t-arg))
              (values `(has-type (vector-set! ,e-vec^
                                              (has-type ,i Integer)
                                              ,e-arg^) Void) 'Void)]
             [else (error 'type-check
                          "expected a vector in vector-set!, not ~a"
                          t-vec)])]
          [`(eq? ,(app (type-check env) e1 t1) ,(app (type-check env) e2 t2))
           (match* (t1 t2)
             [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))
              (values `(has-type (eq? ,e1 ,e2) Boolean) 'Boolean)]
             [(other wise) ((super type-check env) e)])]
          [else ((super type-check env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniqueify : S1 -> C1-expr x (C1-stmt list)



    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S1 -> C1-expr x (C1-stmt list)

    

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose allocation : C1 -> ?

    (define/public (expose-allocation)
      (lambda (x)
        (match x
          [`(program (,xs ...) (type ,ty) . ,(app expose-allocation-seq ss))
           `(program ,(append xs (reset-vars)) (type ,ty)
                     (initialize ,(rootstack-size) ,(heap-size))
                     ,@ss)]
          [else (error 'expose-allocation "umatched ~a" x)])))
    
    ;; Follow the control flow, build the environment, and return
    ;; expression rebuilt using types from environment.
    (define/public (expose-allocation-seq ss)
      (append* (map (expose-allocation-stmt) ss)))
    
    (define/public ((expose-allocation-stmt) stmt)
      (match stmt
        [`(assign ,lhs (has-type ,e ,t))
         (match e
           [`(vector ,e* ...)
	    (define len  (length e*))
	    (define size (* (+ len 1) 8))
	    (define vec `(has-type ,lhs ,t))
	    (define-values (inits)
	      (for/list ([e (in-list e*)]
			 [n (in-naturals)])
			(let ([v (unique-var 'void)])
			  `(assign ,v
				   (has-type
				    (vector-set! ,vec (has-type ,n Integer) ,e)
				    Void)))))
	    `((if (has-type (collection-needed? ,size) Boolean)
		  ((collect ,size))
		  ())
	      (assign ,lhs (has-type (allocate ,len) ,t))
	      ,@inits)]
           [else (list stmt)])]
        [`(if ,t ,(app expose-allocation-seq c) ,(app expose-allocation-seq a))
         `((if ,t ,c ,a))]
        [`(return ,e) (list stmt)]
        [else (error 'expose-allocation-stmt "unmatched ~a" stmt)]))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots : C1-Expr  -> C1-Expr x (set id)

    (define/public (uncover-call-live-roots)
      (lambda (x)
        (vomit "uncover call live roots" x)
        (match x
          [`(program ,xs ,ty
                     . ,(app (uncover-call-live-roots-seq (set)) ss clr*))
           (unless (set-empty? clr*)
             (error 'uncover-call-live-roots 
                    "empty program call live roots invariant ~a" clr*))
           `(program ,(append xs (reset-vars)) ,ty ,@ss)]
          [else (error 'vectors/uncover-call-live-roots "unmatched ~a" x)])))
    
    ;; This is a foldr with two accumulator values, curried for ease
    ;; of use with pattern matching
    ;; uclr-seq : (set id) -> (listof stmt) -> (values (listof stmt) (set id))
    (define/public (uncover-call-live-roots-seq clr*)
      (lambda (x)
        (vomit "uncover call live sequence" x clr*)
        (cond
          [(null? x) (values '() clr*)]
          [(pair? x)           
           (define-values (ss clr1*)
	     ((uncover-call-live-roots-seq clr*) (cdr x)))
	   (define-values (s  clr2*) 
	     (uncover-call-live-roots-stmt (car x) clr1*))
	   (values `(,s . ,ss) clr2*)]
          [else (error 'vectors/uncover-call-live-root-seq "unmatched ~a" x)]
	  )))
  
    ;; uclr-stmt : stmt (set id) -> (values stmt (set id))
    (define/public (uncover-call-live-roots-stmt stmt clr*)
      (vomit "uncover-call-live-roots-stmt" stmt clr*)
      (match stmt
        [(and x `(collect ,size))
         (values `(call-live-roots ,(set->list clr*) (collect ,size)) clr*)]
        [`(assign ,v ,(app uncover-call-live-roots-exp e-clr*))
         (values stmt (set-union (set-remove clr* v) e-clr*))]
        [`(if ,(and t (app uncover-call-live-roots-exp t-clr*))
              ,(app (uncover-call-live-roots-seq clr*) c* c-clr*)
              ,(app (uncover-call-live-roots-seq clr*) a* a-clr*))
         ;; I am not sure what the grammar says ,t should be. -Andre
         (values `(if ,t ,c* ,a*) (set-union c-clr* a-clr* t-clr*))]
        [`(return ,(app uncover-call-live-roots-exp e-clr*))
         ;; Applying some meta reasoning here there shouldn't be any
         ;; call-live roots after a return therefore just e-clr* and
         ;; not (set-union clr* e-clr*)
         (values stmt e-clr*)]
        [`(initialize ,stack ,heap)
         (unless (set-empty? clr*)
           (error 'uncover-call-live-roots
                  "call live roots exist during initialization of rootstack"))
         (values `(initialize ,stack ,heap) clr*)]
        [else (error 'uncover-call-live-roots-stmt "unmatched ~a" stmt)]))

    ;; uclr-exp : expr -> (set id)
    (define/public (uncover-call-live-roots-exp e)
      (vomit "uncover-call-live-roots-exp" e)
      (match e
        [`(has-type (void) ,t) (set)]
        [`(has-type ,(? symbol? x) ,t)
         (if (root-type? t)
             (set x)
             (set))]
        [`(has-type ,e ,t)
         (uncover-call-live-roots-exp e)]
        [(or (? integer?) (? boolean?)
             `(allocate ,_)
             `(collection-needed? ,_))
         (set)]
        [`(,(? primitive? op) ,(app uncover-call-live-roots-exp clr**) ...)
         (set-union* clr**)]
        [else (error 'vectors/uncover-call-live-roots-exp "unmatched ~a" e)]))

    (define/public (root-type? t)
      (match t
        [`(Vector ,T ...)
	 #t]
	[else #f]))
    
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
  
  (define (primitive? x)
    (set-member? (primitives) x))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; select-instructions : C2 -> psuedo-x86

  (define/override (select-instructions)
    (lambda (x)
      (vomit "select instructions" x)
      (match x
        [`(void) `(int 0)]
	[`(assign ,(app (select-instructions) lhs^) (void))
	 `((movq (int 0) ,lhs^))]
        [`(assign ,lhs (has-type (allocate ,length) (Vector ,ts ...)))
         (define lhs^ ((select-instructions) lhs))
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
	   (movq ,lhs^ (reg r11))
           (movq (int ,tag) (deref r11 0)))]        
        [`(call-live-roots (,clr* ...) . ,ss)
         (if (null? clr*)
             (append* (map (select-instructions) ss))
             (let ([frame-size  (* (length clr*) 8)]
                   [pushes
                    (for/list ([root (in-list clr*)] [i (in-naturals)])
                      `(movq (var ,root)
			     (deref ,rootstack-reg ,(* i 8))))]
                   [pops
                    (for/list ([root (in-list clr*)] [i (in-naturals)])
                      `(movq (deref ,rootstack-reg ,(* i 8))
			     (var ,root)))])
               `(,@pushes
                 (addq (int ,frame-size) (reg ,rootstack-reg))
                 ,@(append* (map (select-instructions) ss))
                 (subq (int ,frame-size) (reg ,rootstack-reg))		 
                 ,@pops)))]
        [`(initialize ,s ,h)
         `((movq (int ,s) (reg rdi))
           (movq (int ,h) (reg rsi))
           (callq initialize)
           (movq (global-value rootstack_begin) (reg ,rootstack-reg)))]
        [`(collect ,size)
         `((movq (reg ,rootstack-reg) (reg rdi))
           (movq ,((select-instructions) size) (reg rsi))
           (callq collect))]
        [`(if (has-type (collection-needed? ,size) Boolean) ,cs ,as)
         (define cs^  (append* (map (select-instructions) cs)))
         (define as^  (append* (map (select-instructions) as)))
         (define data (unique-var 'end-data))
         (define lt   (unique-var 'lt))
         ;;cmp arg2, arg1 GAS Syntax
         
         ;;Note that the GAS/AT&T syntax can be rather confusing, as
         ;;for example cmp $0, %rax followed by jl branch will branch
         ;;if %rax < 0 (and not the opposite as might be expected from
         ;;the order of the operands).

         `((movq (global-value free_ptr) (var ,data))
           (addq (int ,size) (var ,data))
           (cmpq (global-value fromspace_end) (var ,data))
           (set l (byte-reg al))
           (movzbq (byte-reg al) (var ,lt))
           ;; (not (< end-data fromspace_end)) implies collection-need? 
           (if (eq? (int 0) (var ,lt)) ,cs^ ,as^))]
        [`(assign ,lhs (vector-ref ,e-vec (has-type ,i ,Integer))) 
         ;; We should try to do this in patch instructions
         (define lhs^ ((select-instructions) lhs))
         (define e-vec^ ((select-instructions) e-vec))
         `((movq ,e-vec^ (reg r11))
	   (movq (deref r11 ,(* (add1 i) 8)) ,lhs^))]
        [`(assign ,lhs (vector-set! ,e-vec (has-type ,i ,Integer) ,e-arg))
         (define new-lhs ((select-instructions) lhs))
         (define new-e-vec ((select-instructions) e-vec))
         (define new-e-arg ((select-instructions) e-arg))
         `((movq ,new-e-vec (reg r11))
	   (movq ,new-e-arg (deref r11 ,(* (add1 i) 8)))
           (movq (int 0) ,new-lhs))]
        ;; If has to be overridden because it needs to propagate
        [`(if ,cnd ,thn-ss ,els-ss)
         (let ([cnd ((select-instructions) cnd)]
               [thn-ss (append* (map (select-instructions) thn-ss))]
               [els-ss (append* (map (select-instructions) els-ss))])
           `((if ,cnd ,thn-ss ,els-ss)))]
        [`(program ,xs (type ,ty) . ,ss)
         (define ss^ (append* (map (select-instructions) ss)))
         `(program ,(append (reset-vars) xs) (type ,ty) ,@ss^)]
        [else ((super select-instructions) x)])))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; uncover-live
  (define/override (free-vars a)
    (match a
       [`(global-value ,l) (set)]
       ;[`(offset ,e ,i) (free-vars e)]
       [else (super free-vars a)]
       ))

  (define/override (write-vars x)
    (match x
      ;[`(movq ,s (offset ,d ,i)) (set)]
      [`(set l ,d) (free-vars d)]
      [else (super write-vars x)]))
  
  (define/override (read-vars x)
    (match x
      ;[`(movq ,s (offset ,d ,i)) (set-union (free-vars s) (free-vars d))]
      [`(set l ,d) (set)]
      [else (super read-vars x)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86
    (define/override (assign-homes homes)
      (lambda (e)
        (match e
          [`(global-value ,l) e]
          #;[`(offset ,e ,i)
           (define new-e ((assign-homes homes) e))
           `(offset ,new-e ,i)]
          [`(set l ,e)
           (define new-e ((assign-homes homes) e))
           `(set l ,new-e)]
          [else ((super assign-homes homes) e)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : psuedo-x86 -> x86

(define/override (in-memory? a)
  (match a
	 ;[`(offset ,e ,i) #t]
    [`(global-value ,l) #t]
    [else (super in-memory? a)]))

#;(define/override (instructions)
  (set-add (super instructions) 'setl))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; print-x86 : x86 -> string

(define/override (print-x86)
  (lambda (e)
    (match e
      #;[`(offset (stack ,n) ,i)
       ;(error "offset, stack case " n)
       (format "~a(%rbp)" (- i n))]
      #;[`(offset ,e ,i)
       (format "~a(~a)" i ((print-x86) e))]
      [`(global-value ,label)
       (format "~a(%rip)" (label-name (symbol->string label)))]
      #;[`(setl ,d) (format "\tsetl\t~a\n" ((print-x86) d))]
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
       ,(send compiler uncover-call-live-roots)
       ,(send interp interp-C '()))
      ("instruction selection"
       ,(send compiler select-instructions)
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
