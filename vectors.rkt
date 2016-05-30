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
    
    (inherit-field use-move-biasing optimize-if)
    (inherit allocate-homes comparison-ops)
    
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

    ;; nothing to do

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose-allocation

    (define/public (expose-allocation)
      (lambda (e)
        (verbose "expose-allocation" e)
	(match e
           [`(has-type (vector ,(app (expose-allocation) e*) ...) ,vec-type)
	    ;; 1. evaluate the e* and let-bind them to x*
	    ;; 2. allocate the vector
	    ;; 3. initialize the vector
	    ;; (1 comes before 2 because e* may trigger GC).
	    (define len  (length e*))
	    (define size (* (+ len 1) 8))
	    (define vec (gensym 'alloc))
	    (define x* (map (lambda (e) (gensym 'vecinit)) e*))
	    (define init-vec (foldr
			      (lambda (x n rest)
				(let ([v (gensym 'initret)])
				  `(let ([,v (has-type (vector-set! ,vec ,n ,x)
						       Void)])
				     ,rest)))
			      vec x* (range len)))
	    (define voidy (gensym 'collectret))
	    (define alloc-init-vec
	      `(has-type 
		(let ([,voidy
		       (has-type
			(if (has-type
			     (< (has-type 
				 (+ (has-type (global-value free_ptr) Integer)
				    (has-type ,size Integer))
				 Integer)
				(has-type (global-value fromspace_end) Integer))
			     Boolean)
			    (has-type (void) Void)
			    (has-type (collect ,size) Void))
			Void)])
		  (has-type 
		   (let ([,vec (has-type (allocate ,len ,vec-type) ,vec-type)])
		     ,init-vec)
		   ,vec-type))
		,vec-type))
	    (foldr
	     (lambda (x e rest)
	       `(has-type (let ([,x ,e])
			    ,rest)
			  ,vec-type))
	     alloc-init-vec x* e*)]
	   [`(has-type ,(app (expose-allocation) e) ,t)
	    `(has-type ,e ,t)]
	   [(? symbol?) e]
	   [(? integer?) e]
	   [(? boolean?) e]
	   [`(void) e]
	   [`(if ,(app (expose-allocation) cnd) 
		 ,(app (expose-allocation) thn)
		 ,(app (expose-allocation) els))
	    `(if ,cnd ,thn ,els)]
	   [`(and ,(app (expose-allocation) e1)
		  ,(app (expose-allocation) e2))
	    `(and ,e1 ,e2)]
	   [`(,op ,es ...) #:when (set-member? (primitives) op)
	    (define new-es (map (expose-allocation) es))
	    `(,op ,@new-es)]
	   [`(let ([,x ,(app (expose-allocation) rhs)]) 
	       ,(app (expose-allocation) body))
	    `(let ([,x ,rhs]) ,body)]
          [`(program (type ,ty) ,(app (expose-allocation) body))
	   (define voidy (gensym 'initret))
	   `(program (type ,ty) 
		     (let ([,voidy (has-type (initialize ,(rootstack-size)
							 ,(heap-size))
					     Void)])
		       ,body))]
          [else
	   (error "in expose-allocation, unmatched" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S1 -> C1-expr x (C1-stmt list) x ((var x type) list)

    (define/override (flatten-if if-type new-thn thn-ss new-els els-ss xs)
      (lambda (cnd)
        (vomit "flatten-if" cnd)
	(match cnd
          [`(has-type ,cnd ,t)
           (match cnd
             [#t #:when optimize-if
                 (values new-thn thn-ss xs)]
             [#f #:when optimize-if
                 (values new-els els-ss xs)]
             [`(let ([,x ,e]) ,body) #:when optimize-if
              (define-values (new-e e-ss xs1) ((flatten #f) e))
              (define-values (new-body body-ss xs2)
                ((flatten-if if-type new-thn thn-ss new-els els-ss xs) body))
              (values new-body
                      (append e-ss
                              `((assign ,x ,new-e))
                              body-ss)
		      (append xs1 xs2))]
             [`(not ,cnd) #:when optimize-if
              ((flatten-if if-type new-els els-ss new-thn thn-ss xs) cnd)]
             [`(,cmp ,e1 ,e2) 
	      #:when (and optimize-if (set-member? (comparison-ops) cmp))
              (define-values (new-e1 e1-ss xs1) ((flatten #t) e1))
              (define-values (new-e2 e2-ss xs2) ((flatten #t) e2))
              (define tmp (gensym 'if))
              (define thn-ret `(assign ,tmp ,new-thn))
              (define els-ret `(assign ,tmp ,new-els))
              (values tmp
                      (append e1-ss e2-ss 
                              `((if (,cmp ,new-e1 ,new-e2)
                                    ,(append thn-ss (list thn-ret))
                                    ,(append els-ss (list els-ret)))))
		      (cons (cons tmp if-type) (append xs1 xs2 xs))
		      )]
             [else
              (define-values (new-cnd cnd-ss xs1) 
		((flatten #t) `(has-type ,cnd ,t)))
	      (define tmp (gensym 'if))
	      (define thn-ret `(assign ,tmp ,new-thn))
	      (define els-ret `(assign ,tmp ,new-els))
	      (values tmp
		      (append cnd-ss
			      `((if (eq? #t ,new-cnd)
				    ,(append thn-ss (list thn-ret))
				    ,(append els-ss (list els-ret)))))
		      (cons (cons tmp if-type) (append xs1 xs))
		      )])]
          [other (error 'flatten-if "unmatched ~a" other)])))    

    (define/override (flatten need-atomic)
      (lambda (e)
        (verbose "flatten" e)
	(match e
	  [`(void) (values '(void) '() '())]
	  [`(collect ,size)
	   (values '(void) `((collect ,size)) '())]
	  [`(initialize ,stack-len ,heap-len)
	   (values '(void) `((initialize ,stack-len ,heap-len)) '())]
	  [`(allocate ,len ,type)
	   (define tmp (gensym 'alloc))
	   (values tmp
		   `((assign ,tmp (allocate ,len ,type))) 
		   (list (cons tmp type)))]
	  [`(global-value ,name)
	   (define tmp (gensym 'global))
	   (values tmp
		   `((assign ,tmp (global-value ,name))) 
		   (list (cons tmp 'Integer)))]
	  [`(has-type (and ,e1 ,e2) ,t)
	   (define-values (new-e1 e1-ss xs1) ((flatten #t) e1))
	   (define-values (new-e2 e2-ss xs2) ((flatten #f) e2))
	   (define tmp (gensym 'and))
	   (values tmp
		   (append e1-ss
			   `((if (eq? #t ,new-e1)
				 ,(append e2-ss `((assign ,tmp ,new-e2)))
				 ((assign ,tmp #f)))))
		   (cons (cons tmp t) (append xs1 xs2))
		   )]

          [`(has-type (,op ,es ...) ,t) #:when (set-member? (primitives) op)
	   (define-values (new-es sss xss) (map3 (flatten #t) es))
	   (define ss (append* sss))
	   (define xs (append* xss))
	   (define prim-apply `(,op ,@new-es))
	   (cond
	    [need-atomic
	     (define tmp (gensym 'tmp))
	     (values tmp
		     (append ss `((assign ,tmp ,prim-apply)))
		     (cons (cons tmp t) xs) )]
	    [else (values prim-apply ss xs)])]

	   [`(let ([,x (has-type ,rhs ,rhs-t)]) ,body)
	    (define-values (new-rhs rhs-ss xs1)
	      ((flatten #f) `(has-type ,rhs ,rhs-t)))
	    (define-values (new-body body-ss xs2) ((flatten need-atomic) body))
	    (values new-body 
		    (append rhs-ss `((assign ,x ,new-rhs)) body-ss)
		    (cons (cons x rhs-t) (append xs1 xs2)))]

	  [`(has-type (if ,cnd ,thn ,els) ,if-type)
	   (define-values (new-thn thn-ss xs1) ((flatten #t) thn))
	   (define-values (new-els els-ss xs2) ((flatten #t) els))
	   ((flatten-if if-type new-thn thn-ss new-els els-ss (append xs1 xs2))
	    cnd)]

	  [`(has-type ,e ,t)
	   ((flatten need-atomic) e)]

          [else
	   ((super flatten need-atomic) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots : C1-Expr  -> C1-Expr x (set id)

    (define/public (uncover-call-live-roots)
      (lambda (x)
        (vomit "uncover call live roots" x)
        (match x
          [`(program ,xs ,ty ,ss ...)
	   (define-values (new-ss clr*)
	     ((uncover-call-live-roots-seq (set) xs) ss))

           (unless (set-empty? clr*)
             (error 'uncover-call-live-roots 
                    "empty program call live roots invariant ~a" clr*))
           `(program ,(append xs (reset-vars)) ,ty ,@new-ss)]
          [else (error 'vectors/uncover-call-live-roots "unmatched ~a" x)])))
    
    ;; This is a foldr with two accumulator values, curried for ease
    ;; of use with pattern matching
    ;; uclr-seq : (set id) -> (listof stmt) -> (values (listof stmt) (set id))
    (define/public (uncover-call-live-roots-seq clr* xs)
      (lambda (x)
        (vomit "uncover call live sequence" x clr*)
        (cond
          [(null? x) (values '() clr*)]
          [(pair? x)           
           (define-values (ss clr1*)
	     ((uncover-call-live-roots-seq clr* xs) (cdr x)))
	   (define-values (s  clr2*) 
	     (uncover-call-live-roots-stmt (car x) clr1* xs))
	   (values (cons s ss) clr2*)]
          [else (error 'vectors/uncover-call-live-root-seq "unmatched ~a" x)]
	  )))
  
    ;; uclr-stmt : stmt (set id) -> (values stmt (set id))
    (define/public (uncover-call-live-roots-stmt stmt clr* xs)
      (vomit "uncover-call-live-roots-stmt" stmt clr*)
      (match stmt
        [(and x `(collect ,size))
         (values `(call-live-roots ,(set->list clr*) (collect ,size)) clr*)]
        [`(assign ,v ,(app (uncover-call-live-roots-exp xs) e-clr*))
         (values stmt (set-union (set-remove clr* v) e-clr*))]
        [`(if ,(and t (app (uncover-call-live-roots-exp xs) t-clr*))
              ,(app (uncover-call-live-roots-seq clr* xs) c* c-clr*)
              ,(app (uncover-call-live-roots-seq clr* xs) a* a-clr*))
         ;; I am not sure what the grammar says ,t should be. -Andre
         (values `(if ,t ,c* ,a*) (set-union c-clr* a-clr* t-clr*))]
        [`(return ,(app (uncover-call-live-roots-exp xs) e-clr*))
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
    (define/public ((uncover-call-live-roots-exp xs) e)
      (vomit "uncover-call-live-roots-exp" e)
      (match e
        [`(void) (set)]
        [(? symbol? x)
         (if (root-type? (lookup x xs))
             (set x)
             (set))]
        [(or (? integer?) (? boolean?)
             `(allocate ,_ ,_)
             `(collection-needed? ,_))
         (set)]
	[`(global-value ,name)
	 (set)]
        [`(,(? primitive? op) ,(app (uncover-call-live-roots-exp xs) clr**) ...)
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
          (set-box! vars `((,x . ,t?) . ,old-vars))
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
        [`(assign ,(app (select-instructions) lhs) (global-value ,name))
	 `((movq (global-value ,name) ,lhs))]
        [`(assign ,lhs (allocate ,length (Vector ,ts ...)))
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
        [`(assign ,lhs (vector-ref ,e-vec ,i)) 
         ;; We should try to do this in patch instructions
         (define lhs^ ((select-instructions) lhs))
         (define e-vec^ ((select-instructions) e-vec))
         `((movq ,e-vec^ (reg r11))
	   (movq (deref r11 ,(* (add1 i) 8)) ,lhs^))]
        [`(assign ,lhs (vector-set! ,e-vec ,i ,e-arg))
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
         `(program ,xs (type ,ty) ,@ss^)]
        [else ((super select-instructions) x)])))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; uncover-live
  (define/override (free-vars a)
    (match a
       [`(global-value ,l) (set)]
       [else (super free-vars a)]
       ))

  (define/override (write-vars x)
    (match x
      [`(set l ,d) (free-vars d)]
      [else (super write-vars x)]))
  
  (define/override (read-vars x)
    (match x
      [`(set l ,d) (set)]
      [else (super read-vars x)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/override (build-interference live-after G)
      (lambda (ast)
	(match ast
           [`(program (,xs ,lives) (type ,ty) ,ss ...)
	    (define G (make-graph (map car xs)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((build-interference live-after G) inst)))
	    (print-dot G "./interfere.dot")
	    `(program (,xs ,G) (type ,ty) ,@new-ss)]
           [`(program (,xs ,lives) ,ss ...)
	    (define G (make-graph (map car xs)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((build-interference live-after G) inst)))
	    (print-dot G "./interfere.dot")
	    `(program (,xs ,G) ,@new-ss)]
	   [else
	    ((super build-interference live-after G) ast)]
	   )))

    (define/override (build-move-graph G)
      (lambda (ast)
	(match ast
           [`(program (,xs ,IG) (type ,ty) ,ss ...)
            (define MG (make-graph (map car xs)))
            (define new-ss
              (if use-move-biasing
                  (let ([nss 
                         (for/list ([inst ss])
                           ((build-move-graph MG) inst))])
                    (print-dot MG "./move.dot")
                    nss)
                  ss))
            `(program (,xs ,IG ,MG) (type ,ty) ,@new-ss)]
           [`(program (,xs ,IG) ,ss ...)
            (define MG (make-graph (map car xs)))
            (define new-ss
              (if use-move-biasing
                  (let ([nss 
                         (for/list ([inst ss])
                           ((build-move-graph MG) inst))])
                    (print-dot MG "./move.dot")
                    nss)
                  ss))
            `(program (,xs ,IG ,MG) ,@new-ss)]

	   [else
	    ((super build-move-graph G) ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/override (allocate-registers)
      (lambda (ast)
	(match ast
           [`(program (,locals ,IG ,MG) (type ,ty) ,ss ...)
	    (define-values (homes stk-size) 
	      (allocate-homes IG MG (map car locals) ss))
	    `(program ,stk-size (type ,ty)
		      ,@(map (assign-homes homes) ss))]
           [`(program (,locals ,IG ,MG) ,ss ...)
	    (define-values (homes stk-size) 
	      (allocate-homes IG MG (map car locals) ss))
	    `(program ,stk-size 
		      ,@(map (assign-homes homes) ss))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86
    (define/override (assign-homes homes)
      (lambda (e)
        (match e
          [`(global-value ,l) e]
          [`(set l ,e)
           (define new-e ((assign-homes homes) e))
           `(set l ,new-e)]
	   [`(program ,xs (type ,ty) ,ss ...)
	    ((super assign-homes homes)
	     `(program ,(map car xs) (type ,ty) ,@ss))]
	   [`(program ,xs ,ss ...)
	    ((super assign-homes homes)
	     `(program ,(map car xs) ,@ss))]
          [else
	   ((super assign-homes homes) e)])))

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
      [`(global-value ,label)
       (format "~a(%rip)" (label-name (symbol->string label)))]
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
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
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
