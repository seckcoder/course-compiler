#lang racket
(require "register_allocator.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-R1 conditionals-passes)

(define challenge #t)

(define compile-R1
  (class compile-reg-R0
    (super-new)

    (define/override (primitives)
      (set-union (super primitives) 
		 (set 'eq? 'and 'or 'not)))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S1 -> S1 (new pass)
    (define/public (type-check env)
      (lambda (e)
	(match e
	   [(? symbol?) (lookup e env)]
	   [(? integer?) 'Integer]
	   [`(let ([,x ,e]) ,body)
	    (let ([T ((send this type-check env) e)])
	      ((send this type-check (cons (cons x T) env)) body))]
	   [`(program ,body)
	    ((send this type-check '()) body)
	    `(program ,body)]
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

    (define/override (flatten need-atomic)
      (lambda (e)
	(match e
	   [#t (values #t '())]
	   [#f (values #f '())]
	   [`(and ,e1 ,e2)
	    (define-values (new-e1 e1-ss) ((send this flatten #t) e1))
	    (define-values (new-e2 e2-ss) ((send this flatten #t) e2))
	    (define tmp (gensym 'and))
	    (values tmp (append e1-ss
				`((if ,new-e1
				      ,(append e2-ss `((assign ,tmp ,new-e2)))
				      ((assign ,tmp #f))))))]
	   [`(if ,cnd ,thn ,els)
	    (let-values ([(new-cnd cnd-ss) ((send this flatten #t) cnd)]
			 [(new-thn thn-ss) ((send this flatten #t) thn)]
			 [(new-els els-ss) ((send this flatten #t) els)])
	      (define tmp (gensym 'if))
	      (define thn-ret `(assign ,tmp ,new-thn))
	      (define els-ret `(assign ,tmp ,new-els))
	      (values tmp
		      (append cnd-ss
			      `((if ,new-cnd
				    ,(append thn-ss (list thn-ret))
				    ,(append els-ss (list els-ret)))))))]
	   [else ((super flatten need-atomic) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S1 -> S1

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'cmpq 'sete 'andq 'orq 'notq 'movzbq)))

    (define/override (binary-op->inst op)
      (match op
	 ['and 'andq]
	 ['or 'orq]
	 [else (super binary-op->inst op)]
	 ))

    (define/override (unary-op->inst op)
      (match op
	 ['not 'notq]
	 [else (super unary-op->inst op)]
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
	   [else ((super select-instructions) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> S1 -> S1*

    (define/override (free-vars a)
      (match a
	 [`(byte-reg al) (set 'rax)]
	 [else (super free-vars a)]
	 ))
    
    (define/override (read-vars instr)
      (match instr
         [`(movzbq ,s ,d) (send this free-vars s)]
     	 [`(cmpq ,s1 ,s2) (set-union (send this free-vars s1)
     				    (send this free-vars s2))]
     	 [(or `(andq ,s ,d) `(orq ,s ,d))
	  (set-union (send this free-vars s) (send this free-vars d))]
     	 [`(sete ,d) (set)]
	 [`(notq ,d) (send this free-vars d)]
     	 [else (super read-vars instr)]))

    (define/override (write-vars instr)
      (match instr
         [`(movzbq ,s ,d) (send this free-vars d)]
     	 [`(cmpq ,s1 ,s2) (set '__flag)]
     	 [(or `(andq ,s ,d) `(orq ,s ,d)) (send this free-vars d)]
	 [`(notq ,d) (send this free-vars d)]
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
	    (define live-after-thn (cond [(null? thn-lives) live-after]
					 [else (car thn-lives)]))
	    (define live-after-els (cond [(null? els-lives) live-after]
					 [else (car els-lives)]))
	    (values `(if ,cnd ,new-thn-ss ,thn-lives ,new-els-ss ,els-lives)
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
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((send this assign-homes homes) cnd)]
		  [thn-ss (map (send this assign-homes homes) thn-ss)]
		  [els-ss (map (send this assign-homes homes) els-ss)])
	      `(if ,cnd ,thn-ss ,els-ss))]
	   [else ((super assign-homes homes) e)]
	   )))
      
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    (define/override (patch-instructions)
      (lambda (e)
	(match e
           [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([thn-ss (append* (map (send this patch-instructions) thn-ss))]
		  [els-ss (append* (map (send this patch-instructions) els-ss))])
	      `((if ,cnd ,thn-ss ,els-ss)))]
	   [else ((super patch-instructions) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lower-conditionals : psuedo-x86 -> x86
    (define/public (lower-conditionals)
      (lambda (e)
	(match e
	   [`(byte-reg ,r) `(byte-reg ,r) ]
	   [`(stack ,n) `(stack ,n)] 
	   [`(int ,n) `(int ,n)]
	   [`(reg ,r) `(reg ,r)]

           [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([thn-ss (append* (map (send this lower-conditionals) thn-ss))]
		  [els-ss (append* (map (send this lower-conditionals) els-ss))]
		  [else-label (gensym 'else)]
		  [end-label (gensym 'if_end)]
		  [cnd-inst ;; cmp's second operand can't be immediate
		   (match cnd
		      [`(int ,n)
		       `((movq (int ,n) (reg rax))
			 (cmpq (int 0) (reg rax)))]
		      [else `((cmpq (int 0) ,cnd))])])
	      (append cnd-inst `((je ,else-label)) thn-ss `((jmp ,end-label))
	       `((label ,else-label)) els-ss `((label ,end-label))
	       ))]
	   [`(callq ,f) `((callq ,f))]
	   [`(program ,stack-space ,ss ...)
	    (let ([new-ss (append* (map (send this lower-conditionals) ss))])
	      `(program ,stack-space ,@new-ss))]
	   [`(,instr ,args ...)
	    `((,instr ,@args))]
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
	   [else ((super print-x86) e)]
	   )))

    )) ;; compile-R1

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define conditionals-passes
  (let ([compiler (new compile-R1)]
	[interp (new interp-R1)])
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
      ("patch instructions" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ("lower conditionals" ,(send compiler lower-conditionals)
       ,(send interp interp-x86 '()))
      ("print x86" ,(send compiler print-x86) #f)
      )))
