#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(provide interp-scheme interp-C interp-x86 interp-R0 interp-R1 interp-R2 interp-R3 interp-R4 )

(define interp-scheme
  (lambda (p)
    ((send (new interp-R4) interp-scheme '()) p)))

(define interp-C
  (lambda (p)
    ((send (new interp-R4) interp-C '()) p)))

(define interp-x86
  (lambda (p)
    ((send (new interp-R4) interp-x86 '()) p)))

;; This (dynamically scoped) parameter is used for goto
(define program (make-parameter '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S0: integer arithmetic and 'let'

(define interp-R0
  (class object%
    (super-new)

    (field (result (gensym 'result)))

    (define/public (primitives)
      (set '+ '- 'read))

    (define/public (interp-op op)
      (match op
         ['+ fx+]
	 ['- (lambda (n) (fx- 0 n))]
	 ['read read-fixnum]
	 [else (error "in interp-op S0, unmatched" op)]))

    (define/public (interp-scheme env)
      (lambda (ast)
        (vomit "R0/interp-scheme" ast env)
	(match ast
           [(? symbol?)
	    (lookup ast env)]
	   [(? integer?) ast]
	   [`(let ([,x ,e]) ,body)
	    (let ([v ((send this interp-scheme env) e)])
	      ((send this interp-scheme (cons (cons x v) env)) body))]
	   [`(program ,e) ((send this interp-scheme '()) e)]
	   [`(,op ,args ...) #:when (set-member? (send this primitives) op)
	    (apply (interp-op op) (map (send this interp-scheme env) args))]
	   [else
	    (error (format "no match in interp-scheme S0 for ~a" ast))]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; C0
    ;;
    ;; atomic   a  ::= n | x
    ;; expr     e  ::= a | (op a ...)
    ;; stmt     s  ::= (assign x e) | (return a)
    ;; program  p  ::= (program (x ...) s ...)

    (define/public (seq-C env)
      (lambda (ss)
	(let loop ([env env] [ss ss])
	  (cond [(null? ss)
		 env]
		[else
		 (loop ((send this interp-C env) (car ss)) 
		       (cdr ss))]))))
	
    (define/public (interp-C env)
      (lambda (ast)
        (vomit "R0/interp-C" ast env)
        (match ast
          [(? symbol? x) (lookup x env)]
          [(? integer? i) i]
          [`(assign ,x ,e)
           (let ([v ((send this interp-C env) e)])
             (cons (cons x v) env))]
          [`(return ,e)
           (let ([v ((send this interp-C env) e)])
             (cons (cons result v) env))]
          [`(program ,xs ,ss ...)
           (define env ((send this seq-C '()) ss))
           (lookup result env)]
          [`(,op ,args ...) #:when (set-member? (send this primitives) op)
                            (apply (interp-op op) (map (send this interp-C env) args))]
          [else
           (error "no match in interp-C0 for " ast)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; psuedo-x86 and x86
    ;; s,d ::= (var x) | (int n) | (reg r) | (stack n)
    ;; i   ::= (movq s d) | (addq s d) | (subq s d) | (imulq s d) 
    ;;       | (negq d) | (callq f)
    ;; psuedo-x86 ::= (program (x ...) i ...)

    (define/public (get-name ast)
      (match ast
        [(or `(var ,x) `(reg ,x) `(stack ,x)) x]
        [else
         (error 'interp-R0/get-name "doesn't have a name: ~a" ast)]))

    (field [x86-ops (make-immutable-hash
                     `((addq 2 ,+)
                       (subq 2 ,-)
                       (negq 1 ,-)))])
    
    (define/public (interp-x86-op op)
      (define (err)
        (error 'interp-R0/interp-x86-op "unmatched ~a" op))
      (cadr (hash-ref x86-ops op err)))
                             


    (define/public (interp-x86-exp env)
      (lambda (ast)
	(match ast
	   [(or `(var ,x) `(reg ,x) `(stack ,x))
            (lookup x env)]
	   [`(int ,n) n]
	   [else
	    (error 'interp-R0/interp-x86-exp "unhandled ~a" ast)])))

    (define/public (interp-x86 env)
      (lambda (ast)
        (when (pair? ast)
          (vomit "R0/interp-x86" (car ast) env))
        (match ast
	   ['() env]
	   [`((callq read_int) . ,ss) 
	    ((send this interp-x86 (cons (cons 'rax (read)) env)) ss)]
           #|
           [`((callq malloc) . ,ss)
	    (define num-bytes ((send this interp-x86-exp env) '(reg rdi)))
	    (define vec (make-vector (/ num-bytes 8)))
	    (define new-env (cons (cons 'rax vec) env))
	    ((send this interp-x86 new-env) ss)]
          
           [`((callq alloc) . ,ss)
	    (define num-bytes ((send this interp-x86-exp env) '(reg rdi)))
	    (define vec (make-vector (/ num-bytes 8)))
	    (define new-env (cons (cons 'rax vec) env))
	    ((send this interp-x86 new-env) ss)]
           [`((callq initialize) . ,ss)
            ;; Could do some work here if we decide to lower the
            ;; representation of vectors for this interpreter. 
            ((send this interp-x86 env) ss)]
	   |#
           [`((movq ,s ,d) . ,ss)
            (define x (send this get-name d))
	    (define v ((send this interp-x86-exp env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`(program ,xs ,ss ...) 
	    (let ([env ((send this interp-x86 '()) ss)])
              (lookup 'rax env))]
	   [`((,binary-op ,s ,d) . ,ss)
	    (let ([s ((send this interp-x86-exp env) s)] 
		  [d ((send this interp-x86-exp env) d)]
                  [x (send this get-name d)]
		  [f (send this interp-x86-op binary-op)])
              ((send this interp-x86 (cons (cons x (f d s)) env)) ss))]
	   [`((,unary-op ,d) . ,ss)
	    (let ([d ((send this interp-x86-exp env) d)]
		  [x (send this get-name d)]
		  [f (send this interp-x86-op unary-op)])
	      ((send this interp-x86 (cons (cons x (f d)) env)) ss))]
	   [else (error "no match in interp-x86 S0 for " ast)]
	   )))

    )) ;; class interp-R0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S1: Booleans and conditionals

(define interp-R1
  (class interp-R0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'eq? 'and 'or 'not)))

    (define/override (interp-op op)
      (match op
         ['eq? (lambda (v1 v2)
                 (cond [(and (fixnum? v1) (fixnum? v2)) (eq? v1 v2)]
                       [(and (boolean? v1) (boolean? v2)) (eq? v1 v2)]))]
         ['not (lambda (v) (match v [#t #f] [#f #t]))]
	 ['and (lambda (v1 v2)
		 (cond [(and (boolean? v1) (boolean? v2))
			(and v1 v2)]))]
	 [else (super interp-op op)]))

    (define/override (interp-scheme env)
      (lambda (ast)
        (vomit "R1/interp-scheme" env)
	(match ast
          [#t #t]
          [#f #f]
          [`(and ,e1 ,e2)
           (match ((send this interp-scheme env) e1)
             [#t (match ((send this interp-scheme env) e2)
                   [#t #t] [#f #f])]
             [#f #f])]
          [`(if ,cnd ,thn ,els)
           (if ((send this interp-scheme env) cnd)
               ((send this interp-scheme env) thn)
               ((send this interp-scheme env) els))]
          [`(program (type ,ty) ,e) ((send this interp-scheme '()) e)]
          [else ((super interp-scheme env) ast)]
          )))

    (define/override (interp-C env)
      (lambda (ast)
	(vomit "R1/interp-C" ast)
	(match ast
           [#t #t]
           [#f #f]
	   [`(if ,cnd ,thn ,els)
	    (if ((send this interp-C env) cnd)
		((send this seq-C env) thn)
		((send this seq-C env) els))]
	   [`(program ,xs (type ,ty) ,ss ...)
            ((super interp-C env) `(program ,xs ,@ss))]
	   [else ((super interp-C env) ast)]
	   )))


    (define (goto-label label ss)
      (cond [(null? ss)
	     (error "goto-label, couldn't find label" label)]
	    [else
	     (match (car ss)
		[`(label ,l) #:when (eq? l label)
		 (cdr ss)]
		[else
		 (goto-label label (cdr ss))])]))

    (define byte2full-reg
      (lambda (r)
	(match r
	   ['al 'rax]
	   ['bl 'rbx]
	   ['cl 'rcx]
	   ['dl 'rdx]
	   )))

    (define/override (get-name ast)
      (match ast
	 [`(byte-reg ,r)
	  (super get-name `(reg ,(byte2full-reg r)))]
	 [else (super get-name ast)]))

    ;; Extending the set of known operators is essentially the
    ;; same as overriding the interp-x86-op with new functionallity
    (inherit-field x86-ops)
    (set! x86-ops (hash-set* x86-ops
                   'notq `(1 ,bitwise-not)
                   'andq `(2 ,bitwise-and)
                   'xorq `(2 ,bitwise-xor)))

    (define/override (interp-x86-exp env)
      (lambda (ast)
	(match ast
          [`(byte-reg ,r)
           ((send this interp-x86-exp env) `(reg ,(byte2full-reg r)))]
          [#t 1]
          [#f 0]
          [`(eq? ,e1 ,e2)
           (if (eq? ((send this interp-x86-exp env) e1)
                    ((send this interp-x86-exp env) e2))
               1
               0)]
          [else ((super interp-x86-exp env) ast)]
          )))
    
    (define/override (interp-x86 env)
      (lambda (ast)
        (when (pair? ast)
          (vomit "R1/interp-x86" (car ast) env))
        (match ast
          [`((sete ,d) . ,ss)
           (define eflags ((send this interp-x86-exp env) '(reg __flag)))
           (define zero   (arithmetic-shift (bitwise-and eflags #b1000000) -6))
           (define name (send this get-name d))
           ((send this interp-x86 (cons (cons name zero) env)) ss)]
          ;; if's are present before patch-instructions
          [(or `((if ,cnd ,thn ,els) . ,ss)
               `((if ,cnd ,thn ,_ ,els ,_) . ,ss))
           (if (not (eq? 0 ((send this interp-x86-exp env) cnd)))
               ((send this interp-x86 env) (append thn ss))
               ((send this interp-x86 env) (append els ss)))]

          [`((label ,l) . ,ss)
           ((send this interp-x86 env) ss)]
          [`((cmpq ,s1 ,s2) . ,ss)
           (let* ([v1 ((send this interp-x86-exp env) s1)] 
                  [v2 ((send this interp-x86-exp env) s2)]
                  [zero   (arithmetic-shift (b2i (eq? v1 v2)) 6)]
                  [eflags (bitwise-ior zero)])
             ((send this interp-x86 (cons (cons '__flag eflags) env)) ss))]
          [`((movzbq ,s ,d) . ,ss)
           (define x (send this get-name d))
           (define v ((send this interp-x86-exp env) s))
           ((send this interp-x86 (cons (cons x v) env)) ss)]
          [`((jmp ,label) . ,ss)
           ((send this interp-x86 env) (goto-label label (program)))]
          [`((je ,label) . ,ss)
           (let* ([eflags (lookup '__flag env)]
                  [zero   (bitwise-and #b1000000 eflags)]
                  [zero?  (i2b (arithmetic-shift zero -6))])
             (cond [zero? 
                    ((send this interp-x86 env) (goto-label label (program)))]
                   [else ((send this interp-x86 env) ss)]))]

          #|[`(program ,xs ,ss ...)
             (parameterize ([program ss])
               ((super interp-x86 '()) ast))]
            [else ((super interp-x86 env) ast)]
          )))|#
	    
;; TODO Fix this once all the tests pass
	
#|[`((sete ,d) . ,ss)
	    (let ([v ((send this interp-x86-exp env) '(reg __flag))]
		  [x (send this get-name d)])
	      ((send this interp-x86 (cons (cons x v) env)) ss))]
	   ;; if's are present before patch-instructions
          [(or `((if ,cnd ,thn ,els) . ,ss)
               `((if ,cnd ,thn ,_ ,els ,_) . ,ss))
           (if (not (eq? 0 ((send this interp-x86-exp env) cnd)))
               ((send this interp-x86 env) (append thn ss))
               ((send this interp-x86 env) (append els ss)))]
	   [`((label ,l) . ,ss)
	    ((send this interp-x86 env) ss)]
	   [`((cmpq ,s1 ,s2) . ,ss)
	    (let ([v1 ((send this interp-x86-exp env) s1)] 
		  [v2 ((send this interp-x86-exp env) s2)])
	      ((send this interp-x86 (cons (cons '__flag 
						 (b2i (eq? v1 v2))) 
					   env))
	       ss))]
	   [`((movzbq ,s ,d) . ,ss)
	    (define x (send this get-name d))
	    (define v ((send this interp-x86-exp env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`((jmp ,label) . ,ss)
	    ((send this interp-x86 env) (goto-label label (program)))]
	   [`((je ,label) . ,ss)
	    (let ([flag (lookup '__flag env)])
	      (cond [(i2b flag)
		     ((send this interp-x86 env) (goto-label label (program)))]
		    [else ((send this interp-x86 env) ss)]))]
           |#
	   [`(program ,xs (type ,ty) ,ss ...)
            (send this display-by-type ty ((send this interp-x86 env) `(program ,xs ,@ss)) env)]
	   [`(program ,xs ,ss ...)
	    (parameterize ([program ss])
	     ((super interp-x86 '()) ast))]
	   [else ((super interp-x86 env) ast)]
	   )))

    (define/public (display-by-type ty val env)
      (match ty
        ['Boolean (if val #t #f)]
        ['Integer val]
        ['Void (void)]
        [`(Vector ,tys ...)
         (list->vector (map (lambda (ty index) (display-by-type ty ((send this memory-read) (+ val 8 (* 8 index))) env)) tys (range (length tys))))]
        [else (error (format "don't know how to display type ~a" ty))]))

    ));; class interp-R1
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S2: Vectors

(define interp-R2
  (class interp-R1
    (super-new)
    ;; The simulated global state of the program 
    ;; define produces private fields
    (define memory (box '()))
    (define uninitialized 'uninitialized-value-from-memory)
    (define free_ptr        (box uninitialized))
    (define fromspace_begin (box uninitialized))
    (define fromspace_end   (box uninitialized))
    (define rootstack_begin (box uninitialized))
    (define rootstack_end   (box uninitialized))
    ;; field is like define but public
    (field [stack-size 8000 #;Bytes]
           [heap-size  10000   #;Bytes]
           [global-label-table
            (make-immutable-hash
             `((free_ptr         . ,free_ptr)
               (fromspace_begin  . ,fromspace_begin)
               (fromspace_end    . ,fromspace_end)
               (rootstack_begin  . ,rootstack_begin)
               (rootstack_end    . ,rootstack_end)))])

    (define/public (memory-read)
      (lambda (addr)
        (let-values ([(start stop name vect) (fetch-page addr)])
          (let ([value (vector-ref vect (arithmetic-shift (- addr start) -3))])
            (when (equal? value uninitialized)
              (error 'interp-R2/memory-read
                     "read uninitialized memory at address ~s"
                     addr))
            value))))

    (define/public (memory-write!)
      (lambda (addr value)
        (let-values ([(start stop name vect) (fetch-page addr)])
          (vector-set! vect (arithmetic-shift (- addr start) -3) value))))
    
    (define/public (collect!)
      (lambda (bytes_requested rootset)
        (error 'interp-R2/collect! "not yet implemented")))

    (define/public (initialize!)
      (lambda (stack-length heap_length)
        (set-box! memory '())
        (let* ([s-begin (allocate! 'rootstack stack-size)]
               [h-begin (allocate! 'fromspace heap-size)])
          (set-box! rootstack_begin s-begin)
          (set-box! rootstack_end   (+ s-begin stack-size))
          (set-box! fromspace_begin h-begin)
          (set-box! fromspace_end   (+ h-begin heap-size))
          (set-box! free_ptr        h-begin))))

    (define (allocate! name size)
      (unless (and (fixnum? size)
                   (positive? size)
                   (= 0 (modulo size 8)))
        (error 'allocate! "expected non-negative fixnum in ~a" size))
      ;; Find the last address
      (define max-addr 
        (for/fold ([next 8])
                  ([page (in-list (unbox memory))])
          (match-let ([`(page ,_ ,stop ,_ ,_) page])
            (max next stop))))
      ;; Allocate with a small pad (10 - 1000) words so that it isn't likely to
      ;; accidentally use another region.
      ;; The randomness is to dispell any reliance on interp always allocating the
      ;; same way. -Andre
      (define start-addr (+ max-addr (* (+ (random 990) 10) 8)))
      ;; The range is of valid addresses in memory are [start, stop)
      (define stop-addr (+ start-addr size))
      (define vect (make-vector (arithmetic-shift size -3) uninitialized))
      (set-box! memory (cons `(page ,start-addr ,stop-addr ,name ,vect)
                             (unbox memory)))
      start-addr)

    (define (free! addr)
      (set! memory
        (let loop ([memory memory])
          (match memory
            [`() (error 'free "address ~a isn't currently allocated")]
            [`(,(and page `(page ,ptr ,_ ,_ ,_)) . ,pages)
             (if (= addr ptr)
                 pages
                (cons page (loop pages)))]))))
    
    (define (fetch-page addr)
      ;; Create a string containing
      (define (fmt-err addr memory)
        (apply
         string-append
         (cons (format "address ~a out of bounds\n\tcurrent memory regions:\n"
                       addr)
               (for/list ([page (in-list memory)])
                 (match-let ([`(page ,start ,stop ,name ,_) page])
                   (format "\t\t~a\t\t[~a,~a)\n" name start stop))))))
      (unless (and (fixnum? addr)
                   (positive? addr))
        (error 'fetch-page "expected non-negative fixnum in ~a" addr))
      (unless (= 0 (modulo addr 8))
        (error 'fetch-page "expected quadword alligned address in ~a" addr)) 
      (let search ([m (unbox memory)])
        (match m
          [`() (error 'fetch-page (fmt-err addr memory))]
          [`((page ,min ,max ,name ,vect) . ,rest-memory)
           (if (and (<= min addr) (< addr max))
               (values min max name vect)
               (search rest-memory))]
          [other (error 'fetch-page "unmatched ~a" m)])))
             
    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'vector 'vector-ref 'vector-set!)))
    
    (define/override (interp-op op)
      (match op
        ['eq? (lambda (v1 v2)
                (cond [(or (and (fixnum? v1) (fixnum? v2)) 
                           (and (boolean? v1) (boolean? v2))
                           (and (vector? v1) (vector? v2)))
                       (eq? v1 v2)]))]
        ['vector vector]
        ['vector-ref vector-ref]
        ['vector-set! vector-set!]
        [else (super interp-op op)]))
    
    (define (mem-error message expr)
      (lambda (who fmt . args)
        (error who "~a in ~a raise error:\n~a"
               message expr
               (apply format (cons fmt args)))))

    (define (global-value-err ast)
      (lambda ()
        (error 'interp-R2 "global label is unknown in ~a" ast)))
    
    
    (define/public (fetch-global label)
      (let* ([err (global-value-err label)]
             [ref (hash-ref global-label-table label err)]
             [value (unbox ref)])
        (when (equal? value uninitialized)
          (debug "fetch" global-label-table)
          (error 'interp-R2/fetch-global
                 "global value, ~a, used before initialization"
                 label))
        value))

    
    (define/override (interp-C env)
      (lambda (ast)
        (match ast
          ;; I should do better than make these noops - andre
          [`(initialize ,s ,h)
           (unless (and (exact-nonnegative-integer? s)
                        (exact-nonnegative-integer? h))
             (error "intialize must be called with literals"))
           ((initialize!) s h)
           env]
          ;; Determine if a collection is needed.
          ;; Which it isn't because vectors stored in the environment
          ;; is the representation of the heap in the C language,
          ;; but collection is a no-op so we should check to see if
          ;; everything is well formed anyhow.
          [`(collection-needed? ,size)
           (when (or (eq? (unbox free_ptr) uninitialized)
                     (eq? (unbox fromspace_end) uninitialized))
             (error 'interp-x86 "uninitialized state in ~a" ast))
           #t]
          ;; Collection isn't needed or possible in this representation
          [`(collect ,size)
           (unless (exact-nonnegative-integer? ((interp-C env) size))
             (error 'interp-C "invalid argument to collect in ~a" ast)) 
           env]
          [`(collect ,rs ,size)
           (unless (and (exact-nonnegative-integer? ((interp-C env) rs))
                        (exact-nonnegative-integer? ((interp-C env) size)))
             (error 'interp-C "invalid argument(s) to collect in ~a" ast)) 
           env]
          ;; allocate a vector of length l and type t that is initialized.
          [`(allocate ,l ,t) (build-vector l (lambda a uninitialized))]
          ;; Analysis information making introduce rootstack easier
          [`(call-live-roots (,xs ...) ,ss ...)
           (for ([x (in-list xs)])
             (unless (vector? (lookup x env))
               (error 'interp-C
                      "call-live-roots stores non-root ~a in ~a" x ast)))
           ((send this seq-C env) ss)]
          [otherwise ((super interp-C env) ast)])))
    
    (define/override (interp-x86-exp env)     
      (lambda (ast)
        (match ast
          [`(global-value ,label) (fetch-global label)]
          [`(offset ,d ,i)
           (define base ((send this interp-x86-exp env) d))
           (define addr (+ base i))
           ((send this memory-read) addr)]
          [else ((super interp-x86-exp env) ast)]
          )))
    
    (define/public (interp-x86-store env)
      (lambda (ast value)
        (match ast
          [`(global-value ,label)
           (define loc (hash-ref global-label-table label (global-value-err ast)))
           (set-box! loc value)
           env]
          [`(offset ,d ,i)
           (define base ((send this interp-x86-exp env) d))
           (define addr (+ base i))
           ((send this memory-write!) addr value)
           env]
          [dest
           (define name (send this get-name dest))
           (cons (cons name value) env)])))

    (inherit-field x86-ops)
    
    (define (x86-binary-op? x)
      (let ([val (hash-ref x86-ops x #f)])
        (and val (= (car val) 2))))

    (define (x86-unary-op? x)
      (let ([val (hash-ref x86-ops x #f)])
        (and val (= (car val) 1))))
    
    #;(interp-x86 : (env -> (R2-stmt -> env))) 
    (define/override (interp-x86 env)
      (lambda (ast)
        (when (pair? ast)
          (vomit "R2/interp-x86" (car ast) env))
	(match ast
          ;; Get the value of the lt flag which doesn't actually exist
          ;; the lt flag is simulated by overflow == sign for x86
          [`((setl ,d) . ,ss)
           (define eflags ((send this interp-x86-exp env) '(reg __flag)))
           (define overflow (bitwise-and eflags #b100000000000))
           (define sign     (bitwise-and eflags #b000010000000))
           (define lt       (if (= overflow sign) 1 0))
           (define new-env ((send this interp-x86-store env) d lt))
           ((send this interp-x86 new-env) ss)]
          ;; cmpq performs a subq operation and examimines the state
          ;; of the result, this is done without overiting the second
          ;; register(I think). -andre
          [`((cmpq ,s1 ,s2) . ,ss)
           (vomit "cmpq" s1 s2)
           (let* ([v1 ((send this interp-x86-exp env) s1)] 
                  [v2 ((send this interp-x86-exp env) s2)]
                  [_  (vomit "cmpq" v1 v2)]
                  [v3 (- v2 v1)]
                  [zero     (arithmetic-shift (b2i (eq? v3 0)) 6)]
                  [sign     (arithmetic-shift (b2i (< v3 0)) 7)] 
                  ;; Our numbers do not overflow so this bit is always 0
                  [overflow (arithmetic-shift 0 11)]
                  [eflags (bitwise-ior overflow sign zero)])
             ((send this interp-x86 (cons (cons '__flag eflags) env)) ss))]
          ;; Initialize the state of the "runtime"
          [`((callq initialize) . ,ss)
           (define stack-size ((interp-x86-exp env) '(reg rdi)))
           (define heap-size ((interp-x86-exp env) '(reg rsi))) 
           ((initialize!)  stack-size heap-size)
           ((send this interp-x86 env) ss)]
          [`((callq malloc) . ,ss)
           (define num-bytes ((interp-x86-exp env) '(reg rdi)))
           ((send this interp-x86 `((rax . ,(allocate! 'malloc num-bytes)) . ,env)) ss)]
          [`((callq alloc) . ,ss)
           (define num-bytes ((interp-x86-exp env) '(reg rdi)))
           ((send this interp-x86 `((rax . ,(allocate! 'alloc num-bytes)) . ,env)) ss)]
          [`((callq collect) . ,ss)
           ;; TODO move some pointers around
           ((send this interp-x86 env) ss)]
          [`((movq ,s ,d) . ,ss)
           (define value   ((send this interp-x86-exp env) s))
           (define new-env ((send this interp-x86-store env) d value))
           ((send this interp-x86 new-env) ss)]
          [`((,(? x86-binary-op? binop) ,s ,d) . ,ss)
           (define src ((send this interp-x86-exp env) s))
           (define dst ((send this interp-x86-exp env) d))
           (define op  (send this interp-x86-op binop))
           (define new-env ((send this interp-x86-store env) d (op src dst)))
           ((send this interp-x86 new-env) ss)]
          [`((,(? x86-unary-op? unary-op) ,d) . ,ss)
           (define dst ((send this interp-x86-exp env) d))
           (define op  (send this interp-x86-op unary-op))
           (define new-env ((send this interp-x86-store env) d (op dst)))
           ((send this interp-x86 new-env) ss)]
          [else ((super interp-x86 env) ast)])))

    ));; interp-R2

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S3: functions


(define interp-R3
  (class interp-R2
    (super-new)
    (inherit-field result)

    (define/public (non-apply-ast)
      (set-union (send this primitives)
		 (set 'if 'let 'define 'program)))

    (define/override (interp-scheme env)
      (lambda (ast)
        (vomit "R3/interp-scheme" ast env)
        (match ast
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (cons f `(lambda ,xs ,body))]
	   [`(function-ref ,f)
	    (lookup f env)]
	   [`(app ,f ,args ...)
	    (define new-args (map (send this interp-scheme env) args))
	    (let ([f-val ((send this interp-scheme env) f)])
	      (match f-val
	         [`(lambda (,xs ...) ,body)
		  (define new-env (append (map cons xs new-args) env))
		  ((send this interp-scheme new-env) body)]
		 [else (error "interp-scheme, expected function, not" f-val)]))]
	   [`(program (type ,ty) ,ds ... ,body)
	    ((send this interp-scheme env) `(program ,@ds ,body))]
	   [`(program ,ds ... ,body)
	    (let ([top-level (map  (send this interp-scheme '()) ds)])
	      ((send this interp-scheme top-level) body))]
	    #;(let loop ([ds ds] [new-env '()])
	      (cond [(null? ds)
		     ((send this interp-scheme new-env) body)]
		    [else
		     (loop (cdr ds)
			   (cons ((send this interp-scheme new-env) (car ds))
				 new-env))]))
	   [`(,f ,args ...) #:when (not (set-member?
					 (send this non-apply-ast) f))
	    ((send this interp-scheme env) `(app ,f ,@args))]
	   [else ((super interp-scheme env) ast)]
	   )))

    (define/override (interp-C env)
      (lambda (ast)
	(debug "R3/interp-C" ast)
	(match ast
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
	    (cons f `(lambda ,xs ,@ss))]
	   [`(function-ref ,f)
	    (lookup f env)]
	   [`(app ,f ,args ...)
	    (define new-args (map (send this interp-C env) args))
	    (define f-val ((send this interp-C env) f))
	    (match f-val
	       [`(lambda (,xs ...) ,ss ...)
		(define new-env (append (map cons xs new-args) env))
		(define result-env ((send this seq-C new-env) ss))
		(lookup result result-env)]
	       [else (error "interp-C, expected a funnction, not" f-val)])]
           [`(program ,locals (type ,ty) (defines ,ds ...) ,ss ...)
            ((send this interp-C env) `(program ,locals (defines ,@ds) ,@ss))]
	   [`(program ,locals (defines ,ds ...) ,ss ...)
	    (define new-env (map (send this interp-C '()) ds))
	    (define result-env ((send this seq-C new-env) ss))
	    (lookup result result-env)]
	   [else ((super interp-C env) ast)]
	   )))

    (define (stack-arg-name n)
      (string->symbol (string-append "rsp_" (number->string n))))

    (define/public (builtin-funs) 
      (set 'malloc 'alloc 'collect 'initialize 'read_int))
    
    (define/override (get-name ast)
      (match ast
         [`(stack-arg ,n) (stack-arg-name n)]
	 [else (super get-name ast)]
	 ))

    (define (call-function f-val ss env)
      (match f-val
        [`(lambda ,n ,body-ss ...)
         ;; copy some register and stack locations over to new-env
         (define passing-regs
	    (filter (lambda (p) p) (for/list ([r arg-registers])
					     (assq r env))))
	  (define passing-stack
	    (for/list ([i (in-range 
			   0 (max 0 (- n (vector-length
					  arg-registers))))])
		      (define name (stack-arg-name (* i 8)))
		      (define val (lookup name env))
		      (define index (- (+ 16 (* i 8))))
		      (cons index val)))
	  (define new-env (append passing-regs passing-stack env))
	  (define result-env
	    (parameterize ([program body-ss])
			  ((send this interp-x86 new-env) body-ss)))
	  (define res (lookup 'rax result-env))
	  ((send this interp-x86 (cons (cons 'rax res) env)) ss)]
	 [else (error "interp-x86, expected a function, not" f-val)]))
      
    (define/override (interp-x86-exp env)
      (lambda (ast)
	(match ast
	   [`(stack-arg ,n)
	    (define x (stack-arg-name n))
	    (lookup x env)]
	   [`(function-ref ,f)
	    (lookup f env)]
	   [else ((super interp-x86-exp env) ast)]
	   )))

    (define/override (interp-x86 env)
      (lambda (ast)
        (when (pair? ast)
          (debug "R3/interp-x86" (car ast) env))
	(match ast
#|
          [`(define (,f) ,n ,extra ,ss ...)
           (cons f `(lambda ,n ,@ss))]
          ;; Treat lea like mov -Jeremy
          [`((leaq ,s ,d) . ,ss)
           (define x (send this get-name d))
           (define v ((send this interp-x86-exp env) s))
           ((send this interp-x86 (cons (cons x v) env)) ss)]
          [`((indirect-callq ,f) . ,ss)
           (define f-val ((send this interp-x86-exp env) f))
           (call-function f-val ss env)]
          [`((callq ,f) . ,ss) #:when (not (set-member? (send this builtin-funs) f))
           (call-function (lookup f env) ss env)]
          [`(program ,extra (defines ,ds) ,ss ...)
           (parameterize ([program ss])
             (define env (map (send this interp-x86 '()) ds))
             (define result-env ((send this interp-x86 env) ss))
             (lookup 'rax result-env))]
          [else ((super interp-x86 env) ast)]
          )))
|#
	   [`(define (,f) ,n ,extra ,ss ...)
	    (cons f `(lambda ,n ,@ss))]
	   ;; Treat lea like mov -Jeremy
	   [`((leaq ,s ,d) . ,ss)
	    (define x (send this get-name d))
	    (define v ((send this interp-x86-exp env) s))
	    ((send this interp-x86 (cons (cons x v) env)) ss)]
	   [`((indirect-callq ,f) . ,ss)
	    (define f-val ((send this interp-x86-exp env) f))
	    (call-function f-val ss env)]
	   [`((callq ,f) . ,ss) #:when (not (set-member? (send this builtin-funs) f))
	    (call-function (lookup f env) ss env)]
           [`(program ,extra (type ,ty) (defines ,ds ...) ,ss ...)
            (send this display-by-type ty ((send this interp-x86 env)
                                           `(program ,extra (defines ,@ds) ,@ss)) env)]
	   [`(program ,extra (defines ,ds ...) ,ss ...)
            (vomit "program" ast)
            (parameterize ([program ss])
	       (define env (map (send this interp-x86 '()) ds))
	       (define result-env ((send this interp-x86 env) ss))
	       (lookup 'rax result-env))]
	   [else ((super interp-x86 env) ast)]
	   )))

    ));; interp-R3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreters for S4: lambda

(define interp-R4
  (class interp-R3
    (super-new)
    (inherit-field result)

    (define/override (interp-scheme env)
      (lambda (ast)
        (debug "R4/interp-scheme" ast env)
	(match ast
	   [`(lambda: ([,xs : ,Ts] ...) : ,rT ,body)
	    `(lambda ,xs ,body ,env)]
	   [`(app ,f ,args ...)
	    (define new-args (map (send this interp-scheme env) args))
	    (let ([f-val ((send this interp-scheme env) f)])
	      (match f-val
	         [`(lambda (,xs ...) ,body ,lam-env)
		  (define new-env (append (map cons xs new-args) lam-env))
		  ((send this interp-scheme new-env) body)]
		 [else (error "interp-scheme, expected function, not" f-val)]))]
	   [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
	    (mcons f `(lambda ,xs ,body))]
	   [`(program (type ,ty) ,ds ... ,body)
            ((send this interp-scheme env) `(program ,@ds ,body))]
	   [`(program ,ds ... ,body)
	    (let ([top-level (map (send this interp-scheme '()) ds)])
	      ;; Use set-cdr! on define lambda's for mutual recursion
	      (for/list ([b top-level])
			(set-mcdr! b (match (mcdr b)
				       [`(lambda ,xs ,body)
					`(lambda ,xs ,body ,top-level)])))
	      ((send this interp-scheme top-level) body))]
	   [else ((super interp-scheme env) ast)]
	   )))
      

    )) ;; interp-R4


 
