#lang racket
(require "vectors.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "runtime-config.rkt")
(provide compile-R3 functions-passes functions-typechecker)

(define compile-R3
  (class compile-R2
    (super-new)

    (inherit primitives liveness-ss allocate-homes color-graph)

    (define/public (non-apply-ast)
      (set-union (primitives)
		 (set 'if 'let 'define 'program 'void)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S3 -> S3 (for programs)
    ;; type-check : env -> S3 -> type (for expressions)
    (define/public (fun-def-name d)
      (match d
        [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
         f]
        [else (error 'Syntax-Error "ill-formed function definition in ~a" d)]))
      
    (define/public (fun-def-type d)
      (match d
        [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
         `(,@ps -> ,rt)]
        [else (error 'Syntax-Error "ill-formed function definition in ~a" d)]))
    
    (define/override (type-check env)
      (lambda (e)
        (vomit "type-check" e)
        (match e
          [`(,e ,es ...) #:when (not (set-member? (non-apply-ast) e))
           (define-values (e* ty*) (for/lists (e* ty*) ([e (in-list es)])
                                      ((type-check env) e)))
           (define-values (e^ ty) ((type-check env) e))
           (match ty
             [`(,ty^* ... -> ,rt)
              (unless (equal? ty* ty^*)
                (error "parameter and argument type mismatch for function" e))
              (vomit "app" e^ e* rt)
              (values `(has-type (,e^ ,@e*) ,rt) rt)]
             [else (error "expected a function, not" ty)])]
          [`(define (,f ,(and p:t* `[,xs : ,ps]) ...) : ,rt ,body)
	   (define new-env (append (map cons xs ps) env))
           (define-values (body^ ty^) ((type-check new-env) body))
           (unless (equal? ty^ rt)
             (error "body type and return type mismatch for function" e))
	   `(define (,f ,@p:t*) : ,rt ,body^)]
          [`(program ,ds ... ,body)
           (define new-env (for/list ([d ds]) 
			      (cons (fun-def-name d) (fun-def-type d))))
           (define ds^ (for/list ([d ds])
		          ((type-check new-env) d)))
           (define-values (body^ ty) ((type-check new-env) body))
           (vomit "prog" ty ds^ body^)
           `(program (type ,ty) ,@ds^ ,body^)]
          [else ((super type-check env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S3 -> S3

    (define/override (uniquify env)
      (lambda (e)
        (vomit "uniquify" e)
	(match e
          [`(has-type ,e ,t) `(has-type ,((uniquify env) e) ,t)]
          [`(,f ,es ...) #:when (not (set-member? (non-apply-ast) f))
           (define new-es (map (uniquify env) es))
           (define new-f ((uniquify env) f))
           `(,new-f ,@new-es)]
          [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
           (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
           (define new-env (append (map cons xs new-xs) env))
           `(define (,(cdr (assq f env)) 
                     ,@(map (lambda (x t) `[,x : ,t]) new-xs ps)) : ,rt 
                     ,((uniquify new-env) body))]
          [`(program (type ,ty) ,ds ... ,body)
           (define new-env
             (for/list ([d ds])
               (match d
                 [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
                  (define new-f (gensym (racket-id->c-id f)))
                  `(,f . ,new-f)]
                 [else (error "type-check, ill-formed function def")])))
           `(program (type ,ty) ,@(map (uniquify new-env) ds)
                     ,((uniquify new-env) body))]
          [else ((super uniquify env) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal functions and application

    (define/public (reveal-functions funs)
      (lambda (e)
	(let ([recur (reveal-functions funs)])
        (define ret
	  (match e
	     [(? number?) e]
	     [(? symbol?)
	      (cond
                [(memq e funs) `(function-ref ,e)]
                [else e])]
	     [`(let ([,x ,e]) ,body)
	      `(let ([,x ,(recur e)]) ,(recur body))]
	     [`(void)
	     `(void)]
	     [#t #t]
	     [#f #f]
	     [`(if ,cnd ,thn ,els)
	      `(if ,(recur cnd) ,(recur thn) ,(recur els))]
	     [`(define (,f ,params ...) : ,rt ,body)
	      `(define (,f ,@params) : ,rt ,(recur body))]
             [`(has-type ,e ,t) `(has-type ,(recur e) ,t)]
             [`(program (type ,ty) ,ds ... ,body)
	      (define funs (for/list ([d ds]) (fun-def-name d)))
	      `(program (type ,ty) ,@(map (reveal-functions funs) ds)
			,((reveal-functions funs) body))]
	     [`(,op ,es ...) #:when (set-member? (primitives) op)
	      `(,op ,@(map recur es))]
	     [`(,f ,es ...)
	      `(app ,(recur f) ,@(map recur es))]
	     ))
	ret)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose allocation : C1 -> ?
    ;; This pass has to thread a new environment through that isn't extended
    ;; This could be overcome with pointers or we could use 

    (define/override (expose-allocation)
      (lambda (e)
	(verbose "expose-allocation" e)
        (match e
          [`(app ,(app (expose-allocation) es) ...)
	   `(app ,@es)]
	  [`(function-ref ,f)
	   `(function-ref ,f)]
          [`(program (type ,ty) ,ds ...
                     ,(app (expose-allocation) new-e))
	   `(program (type ,ty) ,@(map (lambda (d) (expose-allocation-def d))
				       ds) ,new-e)]
          [else
	   ((super expose-allocation) e)])))

    (define/public (expose-allocation-def def)
      (match def
        [`(define (,f ,p:t* ...) : ,t 
            ,(app (expose-allocation) e))
         `(define (,f ,@p:t*) : ,t ,e)]
        [else (error 'expose-allocation-def "unmatched ~a" def)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S3 -> C3-expr x (C3-stmt list)

    (define/public (flatten-body body)
      (define-values (new-body ss locals) ((flatten #t) body))
      (values locals (append ss `((return ,new-body)))))

    (define/override (flatten need-atomic)
      (lambda (ast)
	(verbose "flatten" ast)
	(match ast
          [`(program (type ,ty) ,ds ... ,body)
           (define-values (locals new-body) (flatten-body body))
           (define new-ds (map (flatten #f) ds))
           `(program ,locals (type ,ty) (defines ,@new-ds) ,@new-body)]
          [`(define (,f [,xs : ,Ts] ...) : ,rt ,body)
           (define-values (locals new-body) (flatten-body body))
           `(define (,f ,@(map (lambda (x t) `[,x : ,t]) xs Ts)) : ,rt ,locals
              ,@new-body)]
          [`(has-type (function-ref ,f) ,t)
           (define tmp (gensym 'tmp))
           (values tmp
                   (list `(assign ,tmp (function-ref ,f)))
		   (list (cons tmp t)))]
          [`(has-type (app ,f ,es ...) ,t) 
           (define-values (new-f f-ss xs1) ((flatten #t) f))
           (define-values (new-es sss xss) (map3 (flatten #t) es))
           (define ss (append f-ss (append* sss)))
	   (define xs2 (append* xss))
           (define fun-apply `(app ,new-f ,@new-es))
           (cond
             [need-atomic
              (define tmp (gensym 'tmp))
              (values tmp
                      (append ss `((assign ,tmp ,fun-apply)))
		      (cons (cons tmp t) (append xs1 xs2))
		      )]
             [else
              (values fun-apply ss (append xs1 xs2))])]
          [else ((super flatten need-atomic) ast)])))
    
    (inherit root-type?)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S3 -> S3

    (define max-stack 0)

    (define/override ((select-instructions) e)
      (vomit "select" e)
      (match e
        [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
         (set! max-stack 0)
         (define n (vector-length arg-registers))
	 ;; move from registers and stack locations to parameters
	 (define-values (first-params last-params) 
	   (cond[(> (length xs) n) (split-at xs n)]
		[else (values xs '())]))
	 (define mov-regs
	   (for/list ([param first-params] [r arg-registers])
		     `(movq (reg ,r) (var ,param))))
	 (define mov-stack
	   (for/list ([param last-params] 
		      [i (in-range 0 (length last-params))])
		     `(movq (deref rbp ,(+ 16 (* i 8))) (var ,param))))
	 (define new-ss
	   (append mov-stack mov-regs
		   (append* (map (select-instructions) ss))))
	 ;; parameters become locals
	 `(define (,f)
	    ,(length xs) (,(append (map cons xs ps) locals) ,max-stack)
	    ,@new-ss)]
        [`(assign ,lhs (function-ref ,f))
         (define new-lhs ((select-instructions) lhs))
         `((leaq (function-ref ,f) ,new-lhs))]
        [`(assign ,lhs (app ,f ,es ...))
	 (define new-lhs ((select-instructions) lhs))
	 (define new-f ((select-instructions) f))
	 (define new-es (map (select-instructions) es))
	 (define n (vector-length arg-registers))
	 (define-values (first-args last-args) 
	   (cond[(> (length new-es) n) (split-at new-es n)]
		[else (values new-es '())]))
	 (define mov-regs
	   (for/list ([arg first-args] [r arg-registers])
		     `(movq ,arg (reg ,r))))
	 ;; replace stack-arg with deref -Jeremy
	 (define mov-stack
	   (for/list ([arg last-args] [i (in-range 0 (length last-args))])
		     `(movq ,arg (stack-arg ,(* i 8)))))
	 (set! max-stack (max max-stack (length last-args)))
	 (append mov-stack mov-regs
		 `((indirect-callq ,new-f) (movq (reg rax) ,new-lhs)))]
        [`(program ,locals (type ,ty) (defines ,ds ...) ,ss ...)
         (define new-ds (map (select-instructions) ds))
         (set! max-stack 0)
         (define new-ss (append* (map (select-instructions) ss)))
         `(program
           (,locals ,max-stack)
           (type ,ty)
           (defines ,@new-ds)
           ,@new-ss)]
        [else ((super select-instructions) e)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> pseudo-x86 -> pseudo-x86*

    (define/override (free-vars a)
      (match a
	 [`(function-ref ,f) (set)]
	 [`(stack-arg ,i) (set)]
	 [else (super free-vars a)]
	 ))

    (define/override (read-vars instr)
      (match instr
         [`(leaq ,s ,d) (free-vars s)]
	 [`(indirect-callq ,arg) 
	   (free-vars arg)]
	 [`(callq ,f) (set)]
     	 [else (super read-vars instr)]))

    (define/override (write-vars instr)
      (match instr
	 [`(indirect-callq ,f) caller-save]
	 [`(leaq ,s ,d)  (free-vars d)]
     	 [else (super write-vars instr)]))

    (define/override (uncover-live live-after)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack) ,ss ...)
	    (define-values (new-ss lives) ((liveness-ss (set)) ss))
	    `(define (,f) ,n (,locals ,max-stack ,(cdr lives)) ,@new-ss)]
           [`(program (,locals ,max-stack) (type ,ty) (defines ,ds ...) ,ss ...)
	    (define-values (new-ss lives) ((liveness-ss (set)) ss))
	    (define new-ds (map (uncover-live (set)) ds))
	    `(program (,locals ,max-stack ,(cdr lives)) (type ,ty) (defines ,@new-ds) ,@new-ss)]
	   [else ((super uncover-live live-after) ast)])))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph

    (define/override (build-interference live-after G xs)
      (lambda (ast)
        (vomit "build-interference" ast live-after G)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack ,lives) ,ss ...)
	    (define new-G (make-graph (map car locals)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
                ((build-interference live-after new-G locals) inst)))
	    `(define (,f) ,n (,locals ,max-stack ,new-G) ,@new-ss)]
           [`(program (,locals ,max-stack ,lives) (type ,ty)
		      (defines ,ds ...) ,ss ...)
	    (define new-G (make-graph (map car locals)))
	    (define new-ds
              (for/list ([d ds])
                ((build-interference (void) (void) (void)) d)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
                ((build-interference live-after new-G locals) inst)))
	    `(program (,locals ,max-stack ,new-G) (type ,ty) 
		      (defines ,@new-ds) ,@new-ss)]
	   [else ((super build-interference live-after G xs) ast)]
	   )))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-move-graph : pseudo-x86* -> pseudo-x86*
    ;; *annotate program with move graph
    
    (define/override (build-move-graph G)
      (lambda (ast)
	(match ast
           [`(program (,locals ,max-stack ,IG) (type ,ty) 
		      (defines ,ds ...) ,ss ...)
	    (define new-ds (for/list ([d ds])
                             ((build-move-graph (void)) d)))
            (define MG (make-graph (map car locals)))
            (define new-ss
              (for/list ([inst ss])
                ((build-move-graph MG) inst)))
            (print-dot MG "./move.dot")
            `(program (,locals ,max-stack ,IG ,MG) (type ,ty)
		      (defines ,@new-ds) ,@new-ss)]
	   [`(define (,f) ,n (,locals ,max-stack ,IG) ,ss ...)
            (define MG (make-graph (map car locals)))
            (define new-ss
              (for/list ([inst ss])
                ((build-move-graph MG) inst)))
	    `(define (,f) ,n (,locals ,max-stack ,IG ,MG) ,@new-ss)]
	   [else ((super build-move-graph G) ast)])))
           
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'leaq)))

    (define/override (assign-homes homes)
      (lambda (e)
	(match e
	   [`(stack-arg ,i) `(stack-arg ,i)] ;; obsolete?? -JGS
	   [`(indirect-callq ,f)
	    `(indirect-callq ,((assign-homes homes) f))]
	   [`(function-ref ,f) `(function-ref ,f) ]
	   [else ((super assign-homes homes) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86

    (define/override (allocate-registers)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack ,IG ,MG) ,ss ...)
	    (define color (color-graph IG MG (map car locals)))
	    (define-values (homes stack-spills root-spills)
	      (allocate-homes locals color))

	    (define new-ss (map (assign-homes homes) ss))
	    (define stack-size (align (+ (* stack-spills (variable-size))
					 (* max-stack (variable-size))) 16))
	    (define root-size (* root-spills (variable-size)))
	    `(define (,f) ,n (,stack-size ,root-size) ,@new-ss)]

	   [`(program (,locals ,max-stack ,IG ,MG) (type ,ty) (defines ,ds ...)
		      ,ss ...)
	    (define new-ds (map (allocate-registers) ds)) 
	    (define color (color-graph IG MG (map car locals)))
	    (define-values (homes stack-spills root-spills) 
	      (allocate-homes locals color))
	    (define new-ss (map (assign-homes homes) ss))

	    (define stack-size (align (+ (* stack-spills (variable-size))
					 (* max-stack (variable-size))) 16))
	    (define root-size (* root-spills (variable-size)))
	    `(program (,stack-size ,root-size) (type ,ty)
		      (defines ,@new-ds) ,@new-ss)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; patch-instructions : psuedo-x86 -> x86

    (define/override (in-memory? a)
      (match a
	 [`(function-ref ,f) #t]
	 [`(stack-arg ,i) #t]
	 [else (super in-memory? a)]))

    (define/override (patch-instructions)
      (lambda (e)
	(match e
	   [`(define (,f) ,n ,stack-space ,ss ...)
	    (define sss (for/list ([s ss]) ((patch-instructions) s)))
	    `(define (,f) ,n ,stack-space ,@(append* sss))]
	   [`(indirect-callq ,f)
	    `((indirect-callq ,f))]
	   [`(program ,stack-space (type ,ty) (defines ,ds ...) ,ss ...)
	    (define new-ds (for/list ([d ds])
				     ((patch-instructions) d)))
	    (define sss (for/list ([s ss]) ((patch-instructions) s)))
	    `(program ,stack-space (type ,ty) (defines ,@new-ds) ,@(append* sss))]
	   [`(leaq ,s ,d)
	    (cond [(in-memory? d)
		   `((leaq ,s (reg rax))
		     (movq (reg rax) ,d))]
		  [else
		   `((leaq ,s ,d))])]
	   [else ((super patch-instructions) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lower-conditionals : psuedo-x86 -> x86

    (define/override (lower-conditionals)
      (lambda (e)
	(match e
	   [`(define (,f) ,n ,stack-space ,ss ...)
	    `(define (,f) ,n ,stack-space
	       ,@(append* (map (lower-conditionals) ss)))]

	   [`(program ,stack-space (type ,ty) (defines ,ds ...) ,ss ...)
	    (define new-ds (for/list ([d ds])
				     ((lower-conditionals) d)))
	    (define new-ss (for/list ([s ss])
				     ((lower-conditionals) s)))
	    `(program ,stack-space (type ,ty) (defines ,@new-ds) ,@(append* new-ss))]
	   [else ((super lower-conditionals) e)]
	   )))

    (inherit variable-size)
    
    ;; Locals now take into account that the first few locals on each
    ;; frame will be the callee saved registers.
    (define number-callee-saves (length (set->list callee-save)))
    
    (define/override (first-offset)
      (+ (super first-offset) (* number-callee-saves (variable-size))))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(function-ref ,f)
	    (format "~a(%rip)" f)]
	   [`(indirect-callq ,f)
	    (format "\tcallq\t*~a\n" ((print-x86) f))]
	   [`(stack-arg ,i)
	    (format "~a(%rsp)" i)]
           [`(define (,f) ,n (,spill-space ,root-space) ,ss ...)
	    (define callee-reg (set->list callee-save))
	    (define save-callee-reg
	      (for/list ([r callee-reg])
			(format "\tpushq\t%~a\n" r)))
	    (define restore-callee-reg
	      (for/list ([r (reverse callee-reg)])
			(format "\tpopq\t%~a\n" r)))
	    (define callee-space (* (length (set->list callee-save))
				    (variable-size)))
	    (define stack-adj (- (align (+ callee-space spill-space) 16)
                                 callee-space))
	    (define initialize-roots
	      (for/list ([i (range (/ root-space (variable-size)))])
			(string-append 
			 (format "\tmovq $0, (%~a)\n" rootstack-reg)
			 (format "\taddq $~a, %~a\n" 
				 (variable-size) rootstack-reg))))
	    (string-append
	     (format "\t.globl ~a\n" f)
	     (format "~a:\n" f)
	     (format "\tpushq\t%rbp\n")
             (format "\tmovq\t%rsp, %rbp\n")
             (string-append* save-callee-reg)
             (format "\tsubq\t$~a, %rsp\n" stack-adj)
	     (string-append* initialize-roots)
             ;; Push callee saves at the bottom of the stack
             ;; frame because the current code for stack nodes
             ;; doesn't reason about them. -andre
	     "\n"
	     (string-append* (map (print-x86) ss))
	     "\n"
             (format "\taddq\t$~a, %rsp\n" stack-adj)	     
             (string-append* restore-callee-reg)
	     (format "\tsubq $~a, %~a\n" root-space rootstack-reg)
             (format "\tpopq\t%rbp\n")
	     (format "\tretq\n")
	     )]
	   [`(program ,space (type ,ty) (defines ,ds ...) ,ss ...)
	    (string-append
	     (string-append* (for/list ([d ds]) ((print-x86) d)))
	     "\n"
	     ((super print-x86) `(program ,space (type ,ty) ,@ss)))]
	   [else ((super print-x86) e)]
	   )))

    ));; compile-R3
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define functions-typechecker
  (let ([compiler (new compile-R3)])
    (send compiler type-check '())))
(define functions-passes
  (let ([compiler (new compile-R3)]
	[interp (new interp-R3)])
    `(
      ;("type-check" ,(send compiler type-check '())
      ;,(send interp interp-scheme '()))
      ("uniquify" ,(send compiler uniquify '())
       ,(send interp interp-scheme '()))
      ("reveal-functions" ,(send compiler reveal-functions '())
       ,(send interp interp-F '()))
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-F '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
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
