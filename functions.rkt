#lang racket
(require "vectors.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "uncover-types.rkt")
(require "runtime-config.rkt")
(provide compile-R3 functions-passes functions-typechecker)

(define compile-R3
  (class compile-R2
    (super-new)

    (define/public (non-apply-ast)
      (set-union (send this primitives)
		 (set 'if 'let 'define 'program)))

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
          [`(,e ,es ...) #:when (not (set-member? (send this non-apply-ast) e))
           (define-values (e* ty*)
             (for/lists (e* ty*) ([e (in-list es)])
               ((type-check env) e)))
           (define-values (e^ ty)
             ((send this type-check env) e))
           (match ty
             [`(,ty^* ... -> ,rt)
              (unless (equal? ty* ty^*)
                (error "parameter and argument type mismatch for function" e))
              (vomit "app" e^ e* rt)
              (values `(has-type (,e^ ,@e*) ,rt) rt)]
             [else (error "expected a function, not" ty)])]
          [`(define (,f ,(and p:t* `[,xs : ,ps]) ...) : ,rt ,body)
           (let-values ([(body^ ty^) ((type-check (append (map cons xs ps) env)) body)])
             `(define (,f ,@p:t*) : ,rt ,body^))]
          [`(program ,ds ... ,body)
           (define new-env
             (for/list ([d ds]) 
               (cons (fun-def-name d) (fun-def-type d))))
           (define ds^
             (for/list ([d ds])
               ((send this type-check new-env) d)))
           (define-values (body^ ty)
             ((send this type-check new-env) body))
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
          [`(,f ,es ...) #:when (not (set-member? (send this non-apply-ast) f))
           (define new-es (map (send this uniquify env) es))
           (define new-f ((send this uniquify env) f))
           `(,new-f ,@new-es)]
          [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
           (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
           (define new-env (append (map cons xs new-xs) env))
           `(define (,(cdr (assq f env)) 
                     ,@(map (lambda (x t) `[,x : ,t]) new-xs ps)) : ,rt 
                     ,((send this uniquify new-env) body))]
          [`(program (type ,ty) ,ds ... ,body)
           (define new-env
             (for/list ([d ds])
               (match d
                 [`(define (,f [,xs : ,ps] ...) : ,rt ,body)
                  (define new-f (gensym (racket-id->c-id f)))
                  `(,f . ,new-f)]
                 [else (error "type-check, ill-formed function def")])))
           `(program (type ,ty) ,@(map (send this uniquify new-env) ds)
                     ,((send this uniquify new-env) body))]
          [else ((super uniquify env) e)]
          )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal functions and application

    (define/public (reveal-functions funs)
      (lambda (e)
	(let ([recur (send this reveal-functions funs)])
        (define ret
	  (match e
	     [(? number?) e]
	     [(? symbol?)
	      (cond
                [(memq e funs) `(function-ref ,e)]
                [else e])]
	     [`(let ([,x ,e]) ,body)
	      `(let ([,x ,(recur e)]) ,(recur body))]
	     [#t #t]
	     [#f #f]
	     [`(if ,cnd ,thn ,els)
	      `(if ,(recur cnd) ,(recur thn) ,(recur els))]
	     [`(define (,f ,params ...) : ,rt ,body)
	      `(define (,f ,@params) : ,rt ,(recur body))]
             [`(has-type ,e ,t) `(has-type ,(recur e) ,t)]
             [`(program (type ,ty) ,ds ... ,body)
	      (define funs (for/list ([d ds]) (fun-def-name d)))
	      `(program (type ,ty) ,@(map (send this reveal-functions funs) ds)
			,((send this reveal-functions funs) body))]
	     [`(,op ,es ...) #:when (set-member? (send this primitives) op)
	      `(,op ,@(map recur es))]
	     [`(,f ,es ...)
	      `(app ,(recur f) ,@(map recur es))]
	     ))
	ret)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S3 -> C3-expr x (C3-stmt list)

    (define (flatten-body body)
      (define-values (new-body ss) ((send this flatten #t) body))
      (define locals (append* (map (send this collect-locals) ss)))
      (values (remove-duplicates locals) 
	      (append ss `((return ,new-body)))))

    (define/override (flatten need-atomic)
      (lambda (ast)
	(match ast
          [`(program (type ,ty) ,ds ... ,body)
           (define-values (locals new-body) (flatten-body body))
           (define new-ds (map (send this flatten #f) ds))
           `(program ,locals (type ,ty) (defines ,@new-ds) ,@new-body)]
          [`(define (,f [,xs : ,Ts] ...) : ,rt ,body)
           (define-values (locals new-body) (flatten-body body))
           `(define (,f ,@(map (lambda (x t) `[,x : ,t]) xs Ts)) : ,rt ,locals
              ,@new-body)]
          [`(has-type (function-ref ,f) ,t)
           (define tmp (gensym 'tmp))
           (values `(has-type ,tmp ,t)
                   (list `(assign ,tmp (has-type (function-ref ,f) ,t))))]
          [`(has-type (app ,f ,es ...) ,t) 
           (define-values (new-f f-ss) ((send this flatten #t) f))
           (define-values (new-es sss) (map2 (send this flatten #t) es))
           (define ss (append f-ss (append* sss)))
           (define fun-apply `(app ,new-f ,@new-es))
           (cond
             [need-atomic
              (define tmp (gensym 'tmp))
              (values `(has-type ,tmp ,t)
                      (append ss `((assign ,tmp (has-type ,fun-apply ,t)))))]
             [else
              (values `(has-type ,fun-apply ,t) ss)])]
          [else ((super flatten need-atomic) ast)])))
    
    (inherit reset-vars unique-var root-type?)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; expose allocation : C1 -> ?
    ;; This pass has to thread a new environment through that isn't extended
    ;; This could be overcome with pointers or we could use 

    (inherit expose-allocation-seq)
    (define/override (expose-allocation)
      (lambda (prog)
        (match prog
          [`(program (,xs ...) (type ,ty)
                     (defines ,(app expose-allocation-def ds) ...)
                     ,ss ...)
           (let ([ss (expose-allocation-seq ss)])
             `(program ,(append (reset-vars) xs)
                       (type ,ty)
                       (defines ,@ds)
                       (initialize ,(rootstack-size) ,(heap-size))
                       ,@ss))]
          [else (error 'expose-allocation "unmatched ~a" prog)])))

    (define/public (expose-allocation-def def)
      (match def
        [`(define (,f ,p:t* ...) : ,t (,l* ...)
            . ,(app expose-allocation-seq ss))
         `(define (,f ,@p:t*) : ,t ,(append (reset-vars) l*) ,@ss)]
        [else (error 'expose-allocation-def "unmatched ~a" def)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots : (hashtable id type) (set id) -> C1-Expr  -> C1-Expr x (set id)
    (inherit uncover-call-live-roots-seq)
    (define/override (uncover-call-live-roots)
      (lambda (x)
        (vomit "uncover call live roots" x)
        (match x
          [`(program ,xs ,ty (defines ,ds ...) ,ss ...)
           (let*-values ([(ds)      (map (uncover-call-live-roots-def) ds)]
                         [(ss clr*) ((uncover-call-live-roots-seq (set)) ss)])
             (unless (set-empty? clr*)
               (error 'uncover-call-live-roots 
                    "empty program call live roots invariant ~a" clr*))
             `(program ,(append (reset-vars) xs) ,ty (defines ,@ds) ,@ss))] 
          [else (error 'uncover-call-live-roots "unmatched ~a" x)])))

    ;; uncover-call-live-roots-def : define -> define
    (define/public ((uncover-call-live-roots-def) def)
      (match def
        [`(define ,(and decl `(,f [,x* : ,_] ...)) : ,t ,l* ,ss ...)
         (let*-values ([(ss clr*) ((uncover-call-live-roots-seq (set)) ss)]
                       [(clr*)    (set-subtract clr* (list->set x*))])
           (unless (set-empty? clr*)
             (error 'uncover-call-live-roots 
                    "empty define call live roots invariant ~a ~a" f clr*))
           `(define ,decl : ,t ,l* ,@ss))]
        [else (error 'uncover-call-live-roots-def "unmatched ~a" def)]))

    ;; uncover-call-live-roots-stmt : stmt (set id) -> stmt (set id) 
    (define/override (uncover-call-live-roots-stmt stmt clr*)
      (vomit "functions/uncover-call-live-roots-stmt" stmt clr*)
      (match stmt
        [`(app ,(app uncover-call-live-roots-exp clr**) ...)
         (values `(call-live-roots ,(set->list clr*) ,stmt)
                 (set-union clr* (set-union* clr**)))]
        [`(assign ,lhs (has-type (app ,e* ...) ,t))
         (let* ([clr* (set-remove clr* lhs)]
                [stmt `(call-live-roots ,(set->list clr*) ,stmt)]
                [clr** (for/list ([e e*]) (uncover-call-live-roots-exp e))]
                [clr* (set-union clr* (set-union* clr**))])
           (values stmt clr*))]
        [else (super uncover-call-live-roots-stmt stmt clr*)]))

    ;;uncover-call-live-roots-exp : expr -> (set id)
    (define/override (uncover-call-live-roots-exp e)
      (vomit "functions/uncover-call-live-roots-exp" e)
      (match e 
        [`(function-ref ,f) (set)]
        [else (super uncover-call-live-roots-exp e)]))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S3 -> S3

    (define max-stack 0)

    (define/override ((select-instructions [rootstack #f]) e)
      (vomit "select" e)
      (match e
        [`(define (,f [,xs : ,ps] ...) : ,rt ,locals ,ss ...)
         (set! max-stack 0)
         (define n (vector-length arg-registers))
         (define rootstack (gensym 'rootstack))
         (let ([xs (cons rootstack xs)])
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
               `(movq (stack ,(- (+ 16 (* i 8)))) (var ,param))))
           (define new-ss
             (append mov-stack mov-regs
                     (append* (map (select-instructions rootstack) ss))))
           ;; parameters become locals
           `(define (,f) ,(length xs) (,(append xs (reset-vars) locals) ,max-stack)
              ,@new-ss))]
        [`(assign ,lhs (has-type (function-ref ,f) ,t))
         (define new-lhs ((select-instructions rootstack) lhs))
         `((leaq (function-ref ,f) ,new-lhs))]
        [`(assign ,lhs (has-type (app ,f ,es ...) ,t))
         (unless rootstack
           (error 'app "no rootstack"))
         (let ([es (cons rootstack es)])
           (define new-lhs ((select-instructions rootstack) lhs))
           (define new-f ((select-instructions rootstack) f))
           (define new-es (map (select-instructions rootstack) es))
           (define n (vector-length arg-registers))
           (define-values (first-args last-args) 
             (cond[(> (length new-es) n) (split-at new-es n)]
                  [else (values new-es '())]))
           (define mov-regs
             (for/list ([arg first-args] [r arg-registers])
               `(movq ,arg (reg ,r))))
           (define mov-stack
             (for/list ([arg last-args] [i (in-range 0 (length last-args))])
               `(movq ,arg (stack-arg ,(* i 8)))))
           (set! max-stack (max max-stack (length last-args)))
           (append mov-stack mov-regs
                   `((indirect-callq ,new-f) (movq (reg rax) ,new-lhs))))]
        [`(program ,locals (type ,ty) (defines ,ds ...) ,ss ...)
         (define rootstack (gensym 'rootstack))
         (define new-ds (map (select-instructions #f) ds))
         (set! max-stack 0)
         (define new-ss
           (append* (map (select-instructions rootstack) ss)))
         `(program
           (,(cons rootstack (append (reset-vars) locals)) ,max-stack)
           (type ,ty)
           (defines ,@new-ds)
           ,@new-ss)]
        [else ((super select-instructions rootstack) e)]))

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
         [`(leaq ,s ,d) (send this free-vars s)]
	 [`(indirect-callq ,arg) 
	   (send this free-vars arg)]
	 [`(callq ,f) (set)]
     	 [else (super read-vars instr)]))

    (define/override (write-vars instr)
      (match instr
	 [`(indirect-callq ,f) caller-save]
	 [`(leaq ,s ,d)  (send this free-vars d)]
     	 [else (super write-vars instr)]))

    (define/override (uncover-live live-after)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack) ,ss ...)
	    (define-values (new-ss lives) ((send this liveness-ss (set)) ss))
	    `(define (,f) ,n (,locals ,max-stack ,(cdr lives)) ,@new-ss)]
           [`(program (,locals ,max-stack) (type ,ty) (defines ,ds ...) ,ss ...)
	    (define-values (new-ss lives) ((send this liveness-ss (set)) ss))
	    (define new-ds (map (send this uncover-live (set)) ds))
	    `(program (,locals ,max-stack ,(cdr lives)) (type ,ty) (defines ,@new-ds) ,@new-ss)]
	   [else ((super uncover-live live-after) ast)])))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph

    (define/override (build-interference live-after G)
      (lambda (ast)
        (vomit "build-interference" ast live-after G)
	(match ast
	   [`(define (,f) ,n (,locals ,max-stack ,lives) ,ss ...)
	    (define new-G (make-graph locals))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
                ((send this build-interference live-after new-G) inst)))
	    `(define (,f) ,n (,locals ,max-stack ,new-G) ,@new-ss)]
           [`(program (,locals ,max-stack ,lives) (type ,ty) (defines ,ds ...) ,ss ...)
	    (define new-G (make-graph locals))
	    (define new-ds
              (for/list ([d ds])
                ((send this build-interference (void) (void)) d)))
	    (define new-ss 
	      (for/list ([inst ss] [live-after lives])
                ((send this build-interference live-after new-G) inst)))
	    `(program (,locals ,max-stack ,new-G) (type ,ty) (defines ,@new-ds) ,@new-ss)]
	   [else ((super build-interference live-after G) ast)]
	   )))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-move-graph : pseudo-x86* -> pseudo-x86*
    ;; *annotate program with move graph
    
    (define/override (build-move-graph G)
      (lambda (ast)
	(match ast
           [`(program (,locals ,max-stack ,IG) (type ,ty) (defines ,ds ...) ,ss ...)
	    (define new-ds (for/list ([d ds])
                             ((send this build-move-graph (void)) d)))
            (define MG (make-graph locals))
            (define new-ss
              (for/list ([inst ss])
                ((send this build-move-graph MG) inst)))
            (print-dot MG "./move.dot")
            `(program (,locals ,max-stack ,IG ,MG) (type ,ty) (defines ,@new-ds) ,@new-ss)]
	   [`(define (,f) ,n (,locals ,max-stack ,IG) ,ss ...)
            (define MG (make-graph locals))
            (define new-ss
              (for/list ([inst ss])
                ((send this build-move-graph MG) inst)))
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
	   [`(stack ,i) `(stack ,i)]
	   [`(stack-arg ,i) `(stack-arg ,i)]
	   [`(indirect-callq ,f)
	    `(indirect-callq ,((send this assign-homes homes) f))]
	   [`(function-ref ,f) `(function-ref ,f) ]
	   [else ((super assign-homes homes) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; allocate-registers : pseudo-x86 -> pseudo-x86

    (define/override (allocate-registers)
      (lambda (ast)
	(match ast
	   [`(define (,f) ,n (,xs ,max-stack ,IG ,MG) ,ss ...)
	    (define-values (homes stk-size)
	      (send this allocate-homes IG MG xs ss))
	    (define new-ss (map (send this assign-homes homes) ss))
	    `(define (,f) ,n ,(align (+ stk-size (* 8 max-stack)) 16) ,@new-ss)]
           [`(program (,locals ,max-stack ,IG ,MG) (type ,ty) (defines ,ds ...)
		      ,ss ...)
	    (define new-ds (map (send this allocate-registers) ds)) 
	    (define-values (homes stk-size) 
	      (send this allocate-homes IG MG locals ss))
	    (define new-ss (map (send this assign-homes homes) ss))
	    `(program ,(+ stk-size (* 8 max-stack)) (type ,ty)
		      (defines ,@new-ds) ,@new-ss)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; patch-instructions : psuedo-x86 -> x86

    (define/override (on-stack? a)
      (match a
	 [`(function-ref ,f) #t]
	 [`(stack-arg ,i) #t]
	 [else (super on-stack? a)]))

    (define/override (patch-instructions)
      (lambda (e)
	(match e
	   [`(define (,f) ,n ,stack-space ,ss ...)
	    (define sss (for/list ([s ss]) ((send this patch-instructions) s)))
	    `(define (,f) ,n ,stack-space ,@(append* sss))]
	   [`(indirect-callq ,f)
	    `((indirect-callq ,f))]
	   [`(program ,stack-space (type ,ty) (defines ,ds ...) ,ss ...)
	    (define new-ds (for/list ([d ds])
				     ((send this patch-instructions) d)))
	    (define sss (for/list ([s ss]) ((send this patch-instructions) s)))
	    `(program ,stack-space (type ,ty) (defines ,@new-ds) ,@(append* sss))]
	   [`(leaq ,s ,d)
	    (cond [(on-stack? d)
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
	       ,@(append* (map (send this lower-conditionals) ss)))]

	   [`(program ,stack-space (type ,ty) (defines ,ds ...) ,ss ...)
	    (define new-ds (for/list ([d ds])
				     ((send this lower-conditionals) d)))
	    (define new-ss (for/list ([s ss])
				     ((send this lower-conditionals) s)))
	    `(program ,stack-space (type ,ty) (defines ,@new-ds) ,@(append* new-ss))]
	   [else ((super lower-conditionals) e)]
	   )))

    ;; 
    (define/override (first-offset) 48)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(function-ref ,f)
	    (format "~a(%rip)" f)]
	   [`(indirect-callq ,f)
	    (format "\tcallq\t*~a\n" ((send this print-x86) f))]
	   [`(stack-arg ,i)
	    (format "~a(%rsp)" i)]
           [`(define (,f) ,n ,spill-space ,ss ...)
	    (define callee-reg (set->list callee-save))
	    (define save-callee-reg
	      (for/list ([r callee-reg])
			(format "\tpushq\t%~a\n" r)))
	    (define restore-callee-reg
	      (for/list ([r (reverse callee-reg)])
			(format "\tpopq\t%~a\n" r)))
	    (define callee-space (* (length (set->list callee-save))
				    (send this variable-size)))

            ;; This adjustment needs to be befor
	    (define stack-adj (- (align (+ callee-space spill-space) 16)
                                 callee-space))
	    (string-append
	     (format "\t.globl ~a\n" f)
	     (format "~a:\n" f)
	     (format "\tpushq\t%rbp\n")
             (format "\tmovq\t%rsp, %rbp\n")
             (string-append* save-callee-reg)
             (format "\tsubq\t$~a, %rsp\n" stack-adj)
             ;; Push callee saves at the bottom of the stack
             ;; frame because the current code for stack nodes
             ;; doesn't reason about them. -andre
	     "\n"
	     (string-append* (map (send this print-x86) ss))
	     "\n"
             (format "\taddq\t$~a, %rsp\n" stack-adj)	     
             (string-append* restore-callee-reg)
             (format "\tpopq\t%rbp\n")
	     (format "\tretq\n")
	     )]
	   [`(program ,stack-space (type ,ty) (defines ,ds ...) ,ss ...)
	    (string-append
	     (string-append* (for/list ([d ds]) ((send this print-x86) d)))
	     "\n"
	     ((super print-x86) `(program ,stack-space (type ,ty) ,@ss)))]
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
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-C '()))
      ("uncover call live roots"
       ,(send compiler uncover-call-live-roots)
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
