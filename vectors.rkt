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
    
    (inherit-field use-move-biasing optimize-if largest-color)
    (inherit color-graph comparison-ops variable-size first-offset)
    
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

    (define/override (uniquify env)
      (lambda (e)
	(define recur (uniquify env))
	(match e
           ['(void) '(void)]
	   [else
	    ((super uniquify env) e)]
	   )))

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
	   `(program (type ,ty) ,body)]
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
	  [`(allocate ,len ,type)
	   (cond [need-atomic
		  (define tmp (gensym 'alloc))
		  (values tmp
			  `((assign ,tmp (allocate ,len ,type))) 
			  (list (cons tmp type)))]
		 [else
		  (values `(allocate ,len ,type) '() '())])]
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
  ;; select-instructions : C2 -> psuedo-x86

  (define/public (root-type? t)
    (match t
       [`(Vector ,T ...)
	#t]
       [else #f]))
  
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

    (define/override (build-interference live-after G xs)
      (lambda (ast)
	(match ast
	   [`(callq ,f)
	    (for ([v live-after])
		 (for ([u caller-save]
		       #:when (not (equal? v u)))
		      (add-edge G u v)))
	    (for ([v live-after])
		 (cond [(and (not (set-member? registers v))
			     (root-type? (lookup v xs)))
			(for ([u callee-save])
			      (add-edge G u v))]))
	    ast]
           [`(program (,xs ,lives) (type ,ty) ,ss ...)
	    (define G (make-graph (map car xs)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((build-interference live-after G xs) inst)))
	    (print-dot G "./interfere.dot")
	    `(program (,xs ,G) (type ,ty) ,@new-ss)]
           [`(program (,xs ,lives) ,ss ...)
	    (define G (make-graph (map car xs)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
	         ((build-interference live-after G xs) inst)))
	    (print-dot G "./interfere.dot")
	    `(program (,xs ,G) ,@new-ss)]
	   [`(if ,cnd ,thn-ss ,thn-lives ,els-ss ,els-lives)
	    (define (build-inter inst live-after)
	      ((build-interference live-after G xs) inst))
	    (define new-thn (map build-inter thn-ss thn-lives))
	    (define new-els (map build-inter els-ss els-lives))
	    `(if ,cnd ,new-thn ,new-els)]
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

    (define/public (allocate-homes locals color)
      (define num-stack-spills 0)
      (define num-root-spills 0)
      (define num-regs (vector-length registers-for-alloc))	    
      (debug "making home assignment")
      (define homes
	(make-hash
	 (for/list ([xt locals])
		   (define x (car xt))
		   (define c (hash-ref color x))
		   (cond [(< c num-regs)
			  `(,x . (reg ,(vector-ref 
					registers-for-alloc c)))]
			 [(root-type? (cdr xt))
			  (define i num-root-spills)
			  (set! num-root-spills (add1 i))
			  `(,x . (deref ,rootstack-reg
					,(- (* (add1 i)
					       (variable-size)))))]
			 [else
			  (define i num-stack-spills)
			  (set! num-stack-spills (add1 i))
			  `(,x . (deref rbp
					,(- (+ (first-offset)
					       (* i (variable-size))))))])
		   )))
      (values homes num-stack-spills num-root-spills))

    (define/override (allocate-registers)
      (lambda (ast)
	(match ast
           [`(program (,locals ,IG ,MG) (type ,ty) ,ss ...)
	    (define color (color-graph IG MG (map car locals)))
	    (define-values (homes num-stack-spills num-root-spills)
	      (allocate-homes locals color))
	    `(program (,(* num-stack-spills (variable-size))
		       ,(* num-root-spills (variable-size)))
		      (type ,ty)
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
          [else
	   ((super assign-homes homes) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lower-conditionals : psuedo-x86 -> x86
    (define/override (lower-conditionals)
      (lambda (e)
	(match e
	   [`(program ,space (type ,ty) ,ss ...)
	    (let ([new-ss (append* (map (lower-conditionals) ss))])
	      `(program ,space (type ,ty) ,@new-ss))]
	   [else
	    ((super lower-conditionals) e)]
	   )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : psuedo-x86 -> x86

    (define/override (in-memory? a)
      (match a
	     [`(global-value ,l) #t]
	     [else (super in-memory? a)]))
    
    (define/override (patch-instructions)
      (lambda (e)
	(match e
	   [`(program ,space (type ,ty) ,ss ...)
	    `(program ,space (type ,ty)
		      ,@(append* (map (patch-instructions) ss)))]
	   [else ((super patch-instructions) e)]
	   )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; print-x86 : x86 -> string

(define/override (print-x86)
  (lambda (e)
    (match e
      [`(global-value ,label)
       (format "~a(%rip)" (label-name (symbol->string label)))]
      [`(program (,stack-space ,root-space) (type ,ty) ,ss ...)
       (define callee-reg (set->list callee-save))
       (define save-callee-reg
	 (for/list ([r callee-reg])
		   (format "\tpushq\t%~a\n" r)))
       (define restore-callee-reg
	 (for/list ([r (reverse callee-reg)])
		   (format "\tpopq\t%~a\n" r)))
       (define callee-space (* (length (set->list callee-save))
			       (variable-size)))
       (define stack-adj (- (align (+ callee-space stack-space) 16)
			    callee-space))
       (define initialize-heaps
	 (string-append
	  (format "\tmovq $~a, %rdi\n" (rootstack-size))
	  (format "\tmovq $~a, %rsi\n" (heap-size))
	  (format "\tcallq ~a\n" (label-name "initialize"))
	  (format "\tmovq ~a, %~a\n" 
		  ((print-x86) '(global-value rootstack_begin))
		  rootstack-reg)))
       (define initialize-roots
	 (for/list ([i (range (/ root-space (variable-size)))])
		   (string-append 
		    (format "\tmovq $0, (%~a)\n" rootstack-reg)
		    (format "\taddq $~a, %~a\n" 
			    (variable-size) rootstack-reg))))
       (string-append
	(format "\t.globl ~a\n" (label-name "main"))
	(format "~a:\n" (label-name "main"))
	(format "\tpushq\t%rbp\n")
	(format "\tmovq\t%rsp, %rbp\n")
	(string-append* save-callee-reg)
	(format "\tsubq\t$~a, %rsp\n" stack-adj)
	initialize-heaps
	(string-append* initialize-roots)
	"\n"
	(string-append* (map (print-x86) ss))
	"\n"
	(print-by-type ty)
	(format "\tmovq\t$0, %rax\n")
	(format "\tsubq $~a, %~a\n" root-space rootstack-reg)
	(format "\taddq\t$~a, %rsp\n" stack-adj)
	(string-append* restore-callee-reg)
	(format "\tpopq\t%rbp\n")
	(format "\tretq\n"))]
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
      ;; ("uncover call live roots"
      ;;  ,(send compiler uncover-call-live-roots)
      ;;  ,(send interp interp-C '()))
      ("instruction selection"
       ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler build-interference
                                   (void) (void) (void))
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
