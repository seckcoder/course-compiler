#lang racket
(require "register_allocator.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-R1 conditionals-passes conditionals-typechecker)

(define challenge #t)

(define compile-R1
  (class compile-reg-R0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'eq? 'and 'or 'not)))

    (define/public (insert-type-node node ty)
      (match node
        [`(program ,e) `(program (type ,ty) ,e)]
        [`(program ,info ,rest ...)
         `(program ,info (type ,ty) ,@rest)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S1 -> S1 (new pass)
    (define/public (type-check env)
      (lambda (e)
        (vomit "conditionals/type-check" e env)
        (match e
	   [(? symbol?) (lookup e env)]
	   [(? integer?) 'Integer]
	   [`(let ([,x ,e]) ,body)
	    (let ([T ((send this type-check env) e)])
	      ((send this type-check (cons (cons x T) env)) body))]
	   [`(program ,body)
	    (define ty ((send this type-check '()) body))
	    `(program (type ,ty) ,body)]
	   [#t 'Boolean]
	   [#f 'Boolean]
	   [`(if ,cnd ,thn ,els)
	    (let ([T-cnd ((send this type-check env) cnd)]
		  [T-thn ((send this type-check env) thn)]
		  [T-els ((send this type-check env) els)])
	      (unless (equal? T-cnd 'Boolean)
		  (error "expected conditional to have type Boolean, not" T-cnd))
	      (unless (equal? T-thn T-els)
		  (error "expected branches of if to have same type"
			 (list T-thn T-els)))
	      T-thn)]
	   [`(,op ,es ...) #:when (set-member? (send this primitives) op)
	    (let ([ts (map (send this type-check env) es)])
	      (define binary-ops
		'((+ . ((Integer Integer) . Integer))
		  (- . ((Integer Integer) . Integer))
		  (* . ((Integer Integer) . Integer))
		  (and . ((Boolean Boolean) . Boolean))
		  (or . ((Boolean Boolean) . Boolean))
		  (eq? . ((Integer Integer) . Boolean))
		  ))
	      (define unary-ops
		'((- . ((Integer) . Integer))
		  (not . ((Boolean) . Boolean))))
	      (define nullary-ops
		'((read . (() . Integer))))
	      (define (check op ts table)
		(let ([pts (car (cdr (assq op table)))]
		      [ret (cdr (cdr (assq op table)))])
		  (unless (equal? ts pts)
			  (error "argument type does not match parameter type"
				 (list ts pts)))
		  ret))
	      (cond [(eq? 2 (length ts)) (check op ts binary-ops)]
		    [(eq? 1 (length ts)) (check op ts unary-ops)]
		    [else (check op ts nullary-ops)]))]
	   [else
	    (error "type-check couldn't match" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S1 -> S1
    (define/override (uniquify env)
      (lambda (e)
	(match e
	   [#t #t]
	   [#f #f]
	   [`(if ,cnd ,thn ,els)
	    (let ([cnd ((send this uniquify env) cnd)]
		  [thn ((send this uniquify env) thn)]
		  [els ((send this uniquify env) els)])
	      `(if ,cnd ,thn ,els))]
           [`(program (type ,ty) ,e)
            `(program (type ,ty) ,((send this uniquify env) e))]
	   [else ((super uniquify env) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S1 -> C1-expr x (C1-stmt list)

    (define/override (collect-locals)
      (lambda (ast)
	(match ast
	   [`(if ,cnd ,thn ,els)
	    (append (append* (map (send this collect-locals) thn))
		    (append* (map (send this collect-locals) els)))]
	   [else ((super collect-locals) ast)]
	   )))

    (define optimize-if #t)

    (define/public (flatten-if new-thn thn-ss new-els els-ss)
      (lambda (cnd)
	(match cnd
	   [#t #:when optimize-if
	    (values new-thn thn-ss)]
	   [#f #:when optimize-if
	    (values new-els els-ss)]
	   [`(let ([,x ,e]) ,body) #:when optimize-if
	    (define-values (new-e e-ss) ((send this flatten #f) e))
	    (define-values (new-body body-ss)
	      ((send this flatten-if new-thn thn-ss new-els els-ss) body))
	    (values new-body
		    (append e-ss
			    `((assign ,x ,new-e))
			    body-ss))]
	   [`(not ,cnd) #:when optimize-if
	    ((send this flatten-if new-els els-ss new-thn thn-ss) cnd)]

	   [`(eq? ,e1 ,e2) #:when optimize-if
	    (define-values (new-e1 e1-ss) ((send this flatten #t) e1))
	    (define-values (new-e2 e2-ss) ((send this flatten #t) e2))
	    (define tmp (gensym 'if))
	    (define thn-ret `(assign ,tmp ,new-thn))
	    (define els-ret `(assign ,tmp ,new-els))
	    (values tmp
		    (append e1-ss e2-ss 
			    `((if (eq? ,new-e1 ,new-e2)
				  ,(append thn-ss (list thn-ret))
				  ,(append els-ss (list els-ret))))))]
	   [else
	    (let-values ([(new-cnd cnd-ss) ((send this flatten #t) cnd)])
	      (define tmp (gensym 'if))
	      (define thn-ret `(assign ,tmp ,new-thn))
	      (define els-ret `(assign ,tmp ,new-els))
	      (values tmp
		      (append cnd-ss
			      `((if (eq? #t ,new-cnd)
				    ,(append thn-ss (list thn-ret))
				    ,(append els-ss (list els-ret)))))))]
	   )))

    (define/override (flatten need-atomic)
      (lambda (e)
	(match e
	   [#t (values #t '())]
	   [#f (values #f '())]
	   [`(and ,e1 ,e2)
	    (define-values (new-e1 e1-ss) ((send this flatten #t) e1))
	    (define-values (new-e2 e2-ss) ((send this flatten #f) e2))
	    (define tmp (gensym 'and))
	    (values tmp (append e1-ss
				`((if (eq? #t ,new-e1)
				      ,(append e2-ss `((assign ,tmp ,new-e2)))
				      ((assign ,tmp #f))))))]
	   [`(if ,cnd ,thn ,els)
	    (let-values ([(new-thn thn-ss) ((send this flatten #t) thn)]
			 [(new-els els-ss) ((send this flatten #t) els)])
	      ((send this flatten-if new-thn thn-ss new-els els-ss) cnd))]
	   [`(program ,e)
	    (define-values (new-e ss) ((send this flatten #t) e))
	    (define xs (append* (map (send this collect-locals) ss)))
	    `(program ,(remove-duplicates xs) ,@(append ss `((return ,new-e))))]
	   [`(program (type ,ty) ,e)
	    (define-values (new-e ss) ((send this flatten #t) e))
	    (define xs (append* (map (send this collect-locals) ss)))
	    `(program ,(remove-duplicates xs) (type ,ty) ,@(append ss `((return ,new-e))))]
	   [else ((super flatten need-atomic) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S1 -> S1

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'cmpq 'sete 'andq 'orq 'xorq 'notq 'movzbq)))

    (define/override (binary-op->inst op)
      (match op
	 ['and 'andq]
	 ['or 'orq]
	 [else (super binary-op->inst op)]
	 ))

    (define/public (immediate? e)
      (match e
         [`(int ,n) #t]
	 [else #f]))

    (define/override (select-instructions)
      (lambda (e)
	(match e
	   [#t `(int 1)]
	   [#f `(int 0)]
	   [`(assign ,lhs ,b) #:when (boolean? b)
	    (let ([lhs ((send this select-instructions) lhs)]
		  [b ((send this select-instructions) b)])
	      `((movq ,b ,lhs)))]
           [`(assign ,lhs (not ,e))
	    (define new-lhs ((send this select-instructions) lhs))
	    (define new-e ((send this select-instructions) e))
	    (cond [(equal? new-e new-lhs)
		   `((xorq (int 1) ,new-lhs))]
		  [else `((movq ,new-e ,new-lhs) 
                          (xorq (int 1) ,new-lhs))])]
	   [`(assign ,lhs (eq? ,e1 ,e2))
	    (define new-lhs ((send this select-instructions) lhs))
	    (define new-e1 ((send this select-instructions) e1))
	    (define new-e2 ((send this select-instructions) e2))
	    ;; second operand of cmpq can't be an immediate
	    (define comparison
	      (cond [(and (immediate? new-e1) (immediate? new-e2))
		     `((movq ,new-e2 (reg rax))
		       (cmpq ,new-e1 (reg rax)))]
		    [(immediate? new-e2)
		     `((cmpq ,new-e2 ,new-e1))]
		    [else 
		     `((cmpq ,new-e1 ,new-e2))]))
	    (append comparison
              `((sete (byte-reg al))
		(movzbq (byte-reg al) ,new-lhs))
	      )]
	   ;; Keep the if statement to simplify register allocation
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((send this select-instructions) cnd)]
		  [thn-ss (append* (map (send this select-instructions) 
					thn-ss))]
		  [els-ss (append* (map (send this select-instructions)
					els-ss))])
	      `((if ,cnd ,thn-ss ,els-ss)))]
	   [`(eq? ,a1 ,a2)
	    `(eq? ,((send this select-instructions) a1)
		  ,((send this select-instructions) a2))]
	   [`(program ,locals (type ,ty) ,ss ...)
	    (let ([new-ss (map (send this select-instructions) ss)])
	      `(program ,locals (type ,ty) ,@(append* new-ss)))]
	   [else ((super select-instructions) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> S1 -> S1*

    (define/override (free-vars a)
      (match a
	 [`(byte-reg ,r) (set (byte-reg->full-reg r))]
	 [`(eq? ,e1 ,e2) (set-union (send this free-vars e1)
				    (send this free-vars e2))]
	 [else (super free-vars a)]
	 ))
    
    (define/override (read-vars instr)
      (match instr
        [`(movzbq ,s ,d) (send this free-vars s)]
        [`(cmpq ,s1 ,s2) (set-union (send this free-vars s1)
     				    (send this free-vars s2))]
        [(or `(andq ,s ,d) `(orq ,s ,d) `(xorq ,s ,d))
         (set-union (send this free-vars s) (send this free-vars d))]
        [`(sete ,d) (set)]
        [else (super read-vars instr)]))
    
    (define/override (write-vars instr)
      (match instr
        [`(movzbq ,s ,d) (send this free-vars d)]
        [`(cmpq ,s1 ,s2) (set '__flag)]
        [(or `(andq ,s ,d) `(orq ,s ,d) `(xorq ,s ,d)) 
         (send this free-vars d)]
        [`(sete ,d) (send this free-vars d)]
        [else (super write-vars instr)]))

    (define/override (uncover-live live-after)
      (lambda (ast)
	(match ast
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (define-values (new-thn-ss thn-lives)
	      ((send this liveness-ss live-after) thn-ss))
	    (define-values (new-els-ss els-lives)
	      ((send this liveness-ss live-after) els-ss))
	    ;; I doubt that thn-lives can be null -Jeremy
	    (define live-after-thn (cond [(null? thn-lives) live-after]
					 [else (car thn-lives)]))
	    (define live-after-els (cond [(null? els-lives) live-after]
					 [else (car els-lives)]))
	    (values `(if ,cnd ,new-thn-ss ,(cdr thn-lives) ,new-els-ss ,(cdr els-lives))
		    (set-union live-after-thn live-after-els
			       (send this free-vars cnd)))]
	   [else ((super uncover-live live-after) ast)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; build-interference : live-after x graph -> pseudo-x86* -> pseudo-x86*
    ;; *annotate program with interference graph, removes liveness

      (define/override (build-interference live-after G)
	(lambda (ast)
	  (match ast
             [`(movzbq ,s ,d)
              (for ([v live-after])
                   (for ([d (write-vars `(movq ,s ,d))]
                         #:when (not (or (equal? v s) (equal? v d))))
                        (add-edge G d v)))
              ast]
	     [`(if ,cnd ,thn-ss ,thn-lives ,els-ss ,els-lives)
	      (define (build-inter inst live-after)
		((send this build-interference live-after G) inst))
	      (define new-thn (map build-inter thn-ss thn-lives))
	      (define new-els (map build-inter els-ss els-lives))
	      `(if ,cnd ,new-thn ,new-els)]
	     [else ((super build-interference live-after G) ast)]
	     )))
      
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; assign-homes : homes -> pseudo-x86 -> pseudo-x86
    (define/override (assign-homes homes)
      (lambda (e)
	(match e
	   [`(byte-reg ,r) `(byte-reg ,r)]
	   [`(eq? ,e1 ,e2) `(eq? ,((send this assign-homes homes) e1)
				 ,((send this assign-homes homes) e2))]
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((send this assign-homes homes) cnd)]
		  [thn-ss (map (send this assign-homes homes) thn-ss)]
		  [els-ss (map (send this assign-homes homes) els-ss)])
	      `(if ,cnd ,thn-ss ,els-ss))]
	   [`(program (,xs ...) (type ,ty) ,ss ...)
	    ;; create mapping of variables to stack locations
	    (define (make-stack-loc n)
	      `(stack ,(+ (send this first-offset)
			  (* (send this variable-size) n))))
	    (define new-homes
	      (make-hash (map cons xs
			      (map make-stack-loc
				   (stream->list (in-range 0 (length xs)))))))
	    (define stack-space (align 
				 (* (length xs)
				    (send this variable-size))
				 16))
	    `(program ,stack-space (type ,ty)
		      ,@(map (send this assign-homes new-homes) ss))]
	   [else ((super assign-homes homes) e)]
	   )))
      
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lower-conditionals : psuedo-x86 -> x86
    (define/public (lower-conditionals)
      (lambda (e)
	(match e
	   [`(byte-reg ,r) `(byte-reg ,r) ]
	   [`(stack ,n) `(stack ,n)] 
	   [`(int ,n) `(int ,n)]
	   [`(reg ,r) `(reg ,r)]
           [`(if (eq? ,a1 ,a2) ,thn-ss ,els-ss)
	    (let ([thn-ss (append* (map (send this lower-conditionals) thn-ss))]
		  [els-ss (append* (map (send this lower-conditionals) els-ss))]
		  [thn-label (gensym 'then)]
		  [end-label (gensym 'if_end)])
	      (append `((cmpq ,a1 ,a2)) 
		      `((je ,thn-label)) els-ss `((jmp ,end-label))
		      `((label ,thn-label)) thn-ss `((label ,end-label))
	       ))]
	   [`(callq ,f) `((callq ,f))]
	   [`(program ,stack-space (type ,ty) ,ss ...)
	    (let ([new-ss (append* (map (send this lower-conditionals) ss))])
	      `(program ,stack-space (type ,ty) ,@new-ss))]
	   [`(,instr ,args ...)
	    `((,instr ,@args))]
	   [else
	    (error 'lower-conditionals "unmatched " e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    (define/override (patch-instructions)
      (define (mem? x) (send this on-stack? x))
      (lambda (e)
	(match e
	   [`(je ,label) `((je ,label))]
	   [`(jmp ,label) `((jmp ,label))]
	   [`(label ,label) `((label ,label))]
	   [`(cmpq ,a1 ,a2)
	    (match* (a1 a2)
	       [(`(int ,n1) `(int ,n2))
		`((movq (int ,n2) (reg rax))
		  (cmpq (int ,n1) (reg rax)))]
	       [(a1 `(int ,n2))
		`((cmpq (int ,n2) ,a1))]
               [((? mem? n1) (? mem? n2))
                `((movq ,n2 (reg rax))
		  (cmpq ,n1 (reg rax)))]
               [(_ _)
		`((cmpq ,a1 ,a2))])]
           ;; destination must be a register -andre
           [`(movzbq ,s ,(? mem? d))
            `((movzbq ,s (reg rax))
              (movq (reg rax) ,d))]
	   [`(program ,stack-space (type ,ty) ,ss ...)
	    `(program ,stack-space (type ,ty)
		      ,@(append* (map (send this patch-instructions) ss)))]
	   [else ((super patch-instructions) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(byte-reg ,r) (format "%~a" r)]
	   [`(sete ,d) (format "\tsete\t~a\n" ((send this print-x86) d))]
           [`(cmpq ,s1 ,s2) 
	    (format "\tcmpq\t~a, ~a\n" ((send this print-x86) s1)
		    ((send this print-x86) s2))]
	   [`(je ,label) (format "\tje ~a\n" label)]
	   [`(jmp ,label) (format "\tjmp ~a\n" label)]
	   [`(label ,l) (format "~a:\n" l)]
	   [`(program ,spill-space (type ,ty) ,ss ...)
            (define print-fun
              (match ty
                ['Boolean "print_bool"]
                ['Integer "print_int"]
                [else (error (format "unknown type ~a" ty))]))
	    (define callee-reg (set->list callee-save))
	    (define save-callee-reg
	      (for/list ([r callee-reg])
			(format "\tpushq\t%~a\n" r)))
	    (define restore-callee-reg
	      (for/list ([r (reverse callee-reg)])
			(format "\tpopq\t%~a\n" r)))
	    (define callee-space (* (length (set->list callee-save))
				    (send this variable-size)))
	    (define stack-adj (- (align (+ callee-space spill-space) 16)
				  callee-space))
	    (string-append
	     (format "\t.globl ~a\n" (label-name "main"))
	     (format "~a:\n" (label-name "main"))
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (string-append* save-callee-reg)
	     (format "\tsubq\t$~a, %rsp\n" stack-adj)
	     "\n"
	     (string-append* (map (send this print-x86) ss))
	     "\n"
             (format "\tmovq\t%rax, %rdi\n")
             (format "\tcallq\t~a\n" (label-name print-fun))
	     (format "\tmovq\t$0, %rax\n")
	     (format "\taddq\t$~a, %rsp\n" stack-adj)
	     (string-append* restore-callee-reg)
	     (format "\tpopq\t%rbp\n")
	     (format "\tretq\n"))]
	   [else ((super print-x86) e)]
	   )))

    )) ;; compile-R1

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define conditionals-typechecker
  (let ([compiler (new compile-R1)])
    (send compiler type-check '())))
(define conditionals-passes
  (let ([compiler (new compile-R1)]
	[interp (new interp-R1)])
    `(
;    ("type-check" ,(send compiler type-check '())
;       ,(send interp interp-scheme '()))
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
