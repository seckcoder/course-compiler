#lang racket
(require "conditionals.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-R2 vectors-passes vectors-typechecker)



(define compile-R2
  (class compile-R1
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'vector 'vector-ref 'vector-set! '<)))

    (define/public (relops-table)
      (make-immutable-hash
       '((=  . je)
         (<  . jl) (<= . jle)
         (>  . jg) (>= . jge))))

    (define/public (relop? x)
      (if (hash-ref x (send this relops-table) #f) #t #f))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S2 -> S2    
    (define/override (type-check env)
      (lambda (e)
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
    ;; uncover-call-live-roots : C1-Expr (Uid -> Type) -> C1-Expr x (Uid list)


    ;; Merge two hash tables that do not have contradictory key/value pairs
    (define (hash-merge h1 h2)
      ;; h2 is consistent with h1
      (for ([(k v) (in-hash h1)])
        (let ([v? (hash-ref h2 k #f)])
          (unless (and v? (eq? v? v))
            (error 'vectors/hash-merger "h2 is not consistent with h1"))))
      ;; h1 is consistent with h2 and do the merge
      (for/fold ([env h2])
                ([(k v) (in-hash h1)])
        (let ([v? (hash-ref h2 k #f)])
          (cond
            [(not v?) (hash-set c-env k v)]
            [(eq? v? v) env]
            [else (error 'vectors/introduce-rootset
                         "h1 is not consistent with h2")]))))

    (define (env-ref env)
      (lambda (x)
        (hash-ref env x (lambda () (error 'vectors/env-ref "unmatched ~a" x)))))

    (define/public (root-type? env x)
      (let ([t ((env-ref env) x)])
        (and (pair? t) (eq? (car t) 'Vector))))
    
    (define/public (uncover-live-exp env)
      (lambda (e)
        (match e
          [else (error 'uncover-live-roots-exp "unmatched ~a" e)])))

    (define/public (uncover-live-stmt env)
      (lambda (s)
        (match s
          [else (error 'uncover-live-roots-stmt "unmatched ~a" s)])))

    (define/public (uncover-type-exp x)
      (match x
        [`(,op ...) ]))
    
    (define/public (uncover-env-stmt env)
      (lambda (s)
        (match s
          [(assign ,v ,exp)]
          [else (error 'vectors/uncover-env-stmt s)])))
    
    (define/public (uncover-live-roots env [base (set)])
      ;; This pass could do better if it had most of the type information precomputed
      (lambda (ss)
        (match ss
          ;; Base Case for list recusion
          [`() (values '() base)]
          ;; Interesting cases
          [`((assign ,v (vector ,vs ...)) . ,ss)
           (define var-types   (map (env-ref env) vs))
           (define vector-type `(Vector ,@var-types))
           (define new-env (hash-set v vector-type))
           (define-values (ss^ ss-lr)
             ((uncover-live-roots new-env base) ss))
           (define live-roots
             (set-union ss-lr (list->set (filter (vector-type? env) vs))))
           (values `((assign ,v (vector ,live-roots ,vector-type ,@vs)) . ,ss^)
                   live-roots)]
          [`((assign ,v (vector-ref ,e-vec ,i)) . ,ss)
           (match-define `(Vector ,n-type ...) ((env-ref env) e-vec))
           (define v-type (list-ref n-type i))
           (define-values (ss-rec ss-lr)
             ((uncover-live-roots (hash-set env v v-type) base) ss))
           (values `((assign ,v (vector-ref ,e-vec ,i)) . ,ss-rec)
                   (set-union ss-lr (set e-vect)))]
          [`((vector-set! ,e-vec ,i ,e-arg) . ,ss)
           (define live-roots
             (if ((vector-type? env) e-arg)
                 (set e-vec e-arg)
                 (set e-vec)))
           (define-values (ss-rec ss-lr) ((uncover-live-roots env base) ss))
           (values `((vector-set! ,e-vec ,i ,e-arg) . ,ss-rec)
                   (set-union ss-lr live-roots))]
          ;; App case doesn't exist yet but would be an interesting case
          [`((if ,t ,c ,a) . ,(app (uncover-live-roots env base) ss^ clr*))
           (define (a^ a-clr*) ((uncover-live-roots env clr*) a))
           (define (c^ c-clr*) ((uncover-live-roots env clr*) c))
           (define (t^ t-clr*) ((uncover-live-roots env (set-union c-clr a-clr)) t))
           (values `((if ,t^ ,c^ ,a^) . ,ss^) t-clr)]
          [((assign ,v ,rhs) . ,ss)
           ;; TODO
           ]
          [(,s . ,ss)
           ;; TODO
           ]
          ;; mostly boring 
          [`(assign ,lhs (vector ,es ...)) (error 'introduce-rootset/todo/vector)]
          [else (error 'vectors/introduce-rootset "unmatched ~a" ss)])))

        ;; expose-allocation
        (define/public (expose-allocation)
          (lambda (ss)
            (define (recur x) ((expose-allocation) x))
            (match ss
              [`() `()]
              [`(program . ,(app recur ss)) `(program (initialize) . ,ss)]
              [`(,(assign ,lhs (vector ,cl ,t ,es ...)) . ,(app recur ss))
               (unless (symbol? lhs)
                 (error 'vectors/expose-allocation "invalid ~a" lhs))
               (for ([e (in-list es)])
                 (unless (or (symbol? e) (boolean? e) (integer? e))
                   (error 'vectors/expose-allocation "invalid ~a" e)))
               (define length (length es))           
               (define size   (* (+ length 1) 8))
               `((if (collection-needed? ,size)
                     ((call-live cl
                      (collect size)))
                     ())
                 (assign lhs (allocate ,t ,size))
                 . ,(let inits ([es es][i 0])
                      (if (null? es)
                          ss
                          `((vector-set ,lhs ,i ,(car es))
                            . ,(inits (cdr es) (add1 0))))))]
              [`((if ,t ,(app recur c) ,(app recur a)) . ,(app recur ss))
               `((if ,t ,c ,a) . ,ss)]
              [`(,(app recur s) . ,(app recur ss)) `(,s . ,ss)])))

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
    ;; introduce-rootset : C1-Expr (Uid x Uid)

    ;; do not split live ranges of variable at call sites
    (define/public (introduce-rootstack rs-var)
      (lambda (s)
        (define (recur x) ((introduce-rootstack rs-var env) x))
        (match s
          [`(program (initialize) ,ss ...)
           (define rs-var (gensym 'rootstack))
           `(program (initialize)
                     (assign ,rs-var ,(global-value rootstack_begin))
                     (append* (map (introduce-rootstack rs-var) ss)))]
          [(call-live-roots (,clr* ...) (collect ,size))
           ;; We could consider having a frame marker of some sort
           (define new-rs-var  (gensym 'rootstack))
           (define frame-size  (* (length clr*) 8))
           (define pushes
             (for/list ([root (in-list clr*)] [i (in-naturals)])
               `(movq ,root (offset ,rs-var ,(* i 8)))))
           ;; reverse order of pushes
           (define pops
             (for/fold ([pops '()]) ([root (in-list clr*)] [i (in-naturals)])
               `((movq ,root (offset ,rs-var ,(* i 8))) . ,pops)))
           `(,@pushes
             (assign ,new-rs (+ ,rs-var ,frame-size))
             (collect ,new-rs ,size)
             ,@pops  
             ,@ss-rec)]
          ;; This is the only node that has to worry about congruence for now
          [`(if ,(app recur t) (,(app recur c) ...) (,(app recur a) ...))
           `(if ,t ,c ,a)]
          [otherwise s])))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : C2 -> psuedo-x86

    (define/override (select-instructions)
      (lambda (e)
	(match e
          [`(assign ,lhs (allocate (Vector ts ...) ,length))
           (define tmp (gensym tmp))
           (define lhs^ ((select-intructions) lhs))
           (define size (* (add1 length) 8))
           (define tag
             (for/fold ([tag length])
                       ([t (in-list ts)]
                        [i (in-naturals 6)])
               (if (and (pair? t) (eq? Vector (car t)))
                   (bitwise-ior tag (arithmetic-shift 1 i))
                   tag)))
           `((movq (Global-Value free_ptr) (reg rax))
             (movq (reg rax) ,lhs)
             (addq (int ,size) ,(var rax))
             (movq (reg rax) (global-value free_ptr))
             (movq (offset ,lhs 0) (int ,tag)))]
          [`(collect ,rs ,size)
           (define rs^ ((select-insrtructions) rs))
           (define size^ ((select-instructions) size))
           `((movq ,rs^ (reg rdi))
             (movq ,size^ (ref rsi))
             (callq collect))]
          [`(if (collection-needed? ,size) ,cs ,as)
           (define cs^  (append* (map (select-instructions) cs)))
           (define as^  (append* (map (select-instructions) as)))
           (define data (gensym 'end-data))
           (define heap (gensym 'end-heap))
           `((movq (global-value free-ptr) (reg rsi))
             (addq (int ,size) (reg rsi))
             (movq (global-value fromspace_end) (var heap))
             (cmpq (reg rsi) (var heap))
             (setl (byte-reg al))
             (movzbq (byte-reg al) (var rax))
             (if (reg rax) as^ cs^)) #| purposefully fliped |#]
          [`(assign ,lhs (vector-ref ,e-vec ,i))
           (define new-lhs ((send this select-instructions) lhs))
           (define new-e-vec ((send this select-instructions) e-vec))
           `((movq (offset ,new-e-vec ,(* i 8)) ,new-lhs))]
          [`(assign ,lhs (vector-set! ,e-vec ,i ,e-arg))
           (define new-lhs ((send this select-instructions) lhs))
           (define new-e-vec ((send this select-instructions) e-vec))
           (define new-e-arg ((send this select-instructions) e-arg))
           `((movq ,new-e-arg (offset ,new-e-vec ,(* i 8))))]
          #|
           [`(if (,(? relop? relop) ,a1 ,a2)
                 (,(app (send this select-instructions) then-sss) ...)
                 (,(app (send this select-instructions) else-sss) ...))
            `(if (,relop? ,a1 ,a2)
                 ,(append* then-sss)
                 ,(append* else-sss))]
           |#
           [`(program ,xs (initialize) ,ss ...)
            `(program ,xs (callq initialize)

                      ,@(append* (map (send this select-instructions) ss)))]
	   [else ((super select-instructions) e)]
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

    
    (define/override (patch-instructions)
      (lambda (e)
        (match e
          #;
          [`(if (,(? relop? relop) ,a1 ,a2)
          (,(app (send this patch-instructions) then-sss) ...)
          (,(app (send this patch-instructions) else-sss) ...))
        (define else-label (gensym 'else))
        (define join-label (gensym 'if_end))
        (define jump
          (hash-ref relop (send this relops-table)
                    (error 'INTERNAL/vector "undefined relop ~a" relop)))
        `((cmpq ,a1 ,a2)
          (,jump ,else-label)
          ,@(append* then-sss)
          (jmp ,join-label)
          (label ,else-label)
          ,@(append* else-sss)
          (label ,join-label))]
      [other ((super patch-instructions) other)])))


    
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
	   )))
    ));; compile-R2

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
