#lang racket
(require "register_allocator.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-R1 conditionals-passes conditionals-typechecker)

(define challenge #t)

(define compile-R1
  (class compile-reg-R0
    (super-new)

    (inherit liveness-ss first-offset variable-size in-memory?)

    (define/public (comparison-ops)
      (set 'eq? '< '<= '> '>=))

    (define/override (primitives)
      (set-union (super primitives) 
		 (comparison-ops)
		 (set 'and 'or 'not)))

    (define/public (insert-type-node node ty)
      (match node
        [`(program ,e) `(program (type ,ty) ,e)]
        [`(program ,info ,rest ...)
         `(program ,info (type ,ty) ,@rest)]))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S1 -> S1 (new pass)

    (define/public (binary-op-types)
      '((+ . ((Integer Integer) . Integer))
	(- . ((Integer Integer) . Integer))
	(* . ((Integer Integer) . Integer))
	(and . ((Boolean Boolean) . Boolean))
	(or . ((Boolean Boolean) . Boolean))
	(< . ((Integer Integer) . Boolean))
	(<= . ((Integer Integer) . Boolean))
	(> . ((Integer Integer) . Boolean))
	(>= . ((Integer Integer) . Boolean))
	))

    (define/public (unary-op-types)
      '((- . ((Integer) . Integer))
	(not . ((Boolean) . Boolean))))

    (define/public (nullary-op-types)
      '((read . (() . Integer))))

    (define/public (type-check-op op ts)
      (define table
	(cond
	 [(eq? 2 (length ts)) (binary-op-types)]
	 [(eq? 1 (length ts)) (unary-op-types)]
	 [else (nullary-op-types)]))
      (let ([pts (car (cdr (assq op table)))]
	    [ret (cdr (cdr (assq op table)))])
	(unless (equal? ts pts)
		(error "argument type does not match parameter type"
		       (list ts pts)))
	ret))
    
    (define/public (type-check env)
      (lambda (e)
        (vomit "conditionals/type-check" e env)
        (match e
          [(? symbol? v)
           (let ([t (lookup e env)])
             (values `(has-type ,v ,t) t))]
          [(? integer? n) (values `(has-type ,n Integer) 'Integer)]
          [(? boolean? b) (values `(has-type ,b Boolean) 'Boolean)]
          [`(let ([,x ,e]) ,body)
	    (define-values (e^ Te) ((type-check env) e))
	    (define-values (b Tb) ((type-check (cons (cons x Te) env)) body))
	    (values `(has-type (let ([,x ,e^]) ,b) ,Tb) Tb)]
          [`(program ,body)
           (define-values (b Tb) ((type-check '()) body))
	   `(program (type ,Tb) ,b)]
          [`(if ,cnd ,thn ,els)
           (define-values (c Tc) ((type-check env) cnd))
	   (define-values (t Tt) ((type-check env) thn))
	   (define-values (e Te) ((type-check env) els))
	   (unless (equal? Tc 'Boolean)
             (error "expected conditional to have type Boolean, not" Tc))
	   (unless (equal? Tt Te)
             (error "expected branches of if to have same type"
		    (list Tt Te)))
	   (values `(has-type (if ,c ,t ,e) ,Te) Te)]
          [`(eq? ,e1 ,e2)
           (define-values (e1^ T1) ((type-check env) e1))
	   (define-values (e2^ T2) ((type-check env) e2))
	   (unless (equal? T1 T2)
               (error "checking equality between different-typed values"))
	   (values `(has-type (eq? ,e1^ ,e2^) Boolean) 'Boolean)]
	  [`(,op ,es ...) #:when (set-member? (primitives) op)
            (define-values (new-es ts)
              (for/lists (exprs types) ([e es]) ((type-check env) e)))
	    (define t-ret (type-check-op op ts))
            (values `(has-type (,op ,@new-es) ,t-ret) t-ret)]
          [else
	    (error "type-check couldn't match" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S1 -> S1
    (define/override (uniquify env)
      (lambda (e)
	(match e
          [`(has-type ,e ,t) `(has-type ,((uniquify env) e) ,t)]
          [(? boolean? b) b]
          [`(if ,cnd ,thn ,els)
           (let ([cnd ((uniquify env) cnd)]
                 [thn ((uniquify env) thn)]
                 [els ((uniquify env) els)])
             `(if ,cnd ,thn ,els))]
          [`(program (type ,ty) ,e)
           `(program (type ,ty) ,((uniquify env) e))]
          [else ((super uniquify env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; flatten : S1 -> C1-expr x (C1-stmt list)

    (define/override (collect-locals)
      (lambda (ast)
	(match ast
          [`(if ,cnd ,thn ,els)
           (append (append* (map (collect-locals) thn))
                   (append* (map (collect-locals) els)))]
          [else ((super collect-locals) ast)])))

    (define optimize-if #f)

    (define/public (flatten-if new-thn thn-ss new-els els-ss)
      (lambda (cnd)
        (vomit "flatten-if" cnd)
	(match cnd
          [`(has-type ,cnd ,t)
           (match cnd
             [#t #:when optimize-if
                 (values new-thn thn-ss)]
             [#f #:when optimize-if
                 (values new-els els-ss)]
             [`(let ([,x ,e]) ,body) #:when optimize-if
              (define-values (new-e e-ss) ((flatten #f) e))
              (define-values (new-body body-ss)
                ((flatten-if new-thn thn-ss new-els els-ss) body))
              (values new-body
                      (append e-ss
                              `((assign ,x ,new-e))
                              body-ss))]
             [`(not ,cnd) #:when optimize-if
              ((flatten-if new-els els-ss new-thn thn-ss) cnd)]
             [`(,cmp ,e1 ,e2) 
	      #:when (and optimize-if (set-member? (comparison-ops) cmp))
              (define-values (new-e1 e1-ss) ((flatten #t) e1))
              (define-values (new-e2 e2-ss) ((flatten #t) e2))
              (define tmp (gensym 'if))
              (define thn-ret `(assign ,tmp ,new-thn))
              (define els-ret `(assign ,tmp ,new-els))
              (values `(has-type ,tmp ,t)
                      (append e1-ss e2-ss 
                              `((if (,cmp ,new-e1 ,new-e2)
                                    ,(append thn-ss (list thn-ret))
                                    ,(append els-ss (list els-ret))))))]
             [else
              (define-values (new-cnd cnd-ss) ((flatten #t)
					       `(has-type ,cnd ,t)))
	      (define tmp (gensym 'if))
	      (define thn-ret `(assign ,tmp ,new-thn))
	      (define els-ret `(assign ,tmp ,new-els))
	      (values `(has-type ,tmp ,t)
		      (append cnd-ss
			      `((if (eq? (has-type #t Boolean) ,new-cnd)
				    ,(append thn-ss (list thn-ret))
				    ,(append els-ss (list els-ret))))))])]
          [other (error 'flatten-if "unmatched ~a" other)])))
    
    (define/override (flatten need-atomic)
      (lambda (e)
        (verbose "flatten" e)
	(match e
	  ;; For atomic stuff, we keep the has-type annotation. -Jeremy
	  [`(has-type (void) ,t)
	   (values `(has-type (void) ,t) '())]
	  [`(has-type ,e ,t) #:when (or (symbol? e) (integer? e) (boolean? e))
	   (values `(has-type ,e ,t) '())]

	  ;; We override 'and' to place has-type's around the #t and #f
	  ;; in the generated code. -Jeremy
	  [`(has-type (and ,e1 ,e2) ,t)
	   (define-values (new-e1 e1-ss) ((flatten #t) e1))
	   (define-values (new-e2 e2-ss) ((flatten #f) e2))
	   (define tmp (gensym 'and))
	   (values `(has-type ,tmp ,t)
		   (append e1-ss
			   `((if (eq? (has-type #t Boolean) ,new-e1)
				 ,(append e2-ss `((assign ,tmp ,new-e2)))
				 ((assign ,tmp (has-type #f Boolean)))))))]

          ;; We override flattening for op's because we
	  ;; need to put a has-type on the LHS of the assign. -Jeremy
          [`(has-type (,op ,es ...) ,t)
	   #:when (set-member? (primitives) op)
	   (define-values (new-es sss) (map2 (flatten #t) es))
	   (define ss (append* sss))
	   (define prim-apply `(,op ,@new-es))
	   (cond
	    [need-atomic
	     (define tmp (gensym 'tmp))
	     (values `(has-type ,tmp ,t)
		     (append ss `((assign ,tmp (has-type ,prim-apply ,t)))))]
	    [else (values `(has-type ,prim-apply ,t) ss)])]

	  ;; For 'let' we just need to strip the enclosing has-type. -Jeremy
          [`(has-type (let ([,x ,e]) ,body) ,t)
	   ((flatten need-atomic) `(let ([,x ,e]) ,body))]

	  [`(has-type (if ,cnd ,thn ,els) ,t)
	   (define-values (new-thn thn-ss) ((flatten #t) thn))
	   (define-values (new-els els-ss) ((flatten #t) els))
	   ((flatten-if new-thn thn-ss new-els els-ss) cnd)]

          [`(program ,e)
              (define-values (new-e ss) ((flatten #t) e))
              (define xs (append* (map (collect-locals) ss)))
              `(program ,(remove-duplicates xs)
			,@(append ss `((return ,new-e))))]
          [`(program (type ,ty) ,e)
           (define-values (new-e ss) ((flatten #t) e))
           (define xs (append* (map (collect-locals) ss)))
           `(program ,(remove-duplicates xs) (type ,ty)
		     ,@(append ss `((return ,new-e))))]
          [else ((super flatten need-atomic) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; select-instructions : env -> S1 -> S1

    (define/override (instructions)
      (set-union (super instructions)
		 (set 'cmpq 'set 'andq 'orq 'xorq 'notq 'movzbq)))

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

    (define/public (compare->cc cmp)
      (match cmp
	 ['eq? 'e]
	 ['< 'l]
	 ['<= 'le]
	 ['> 'g]
	 ['>= 'ge]
	 [else (error 'compare->cc "unmatched ~a" cmp)]
	 ))
	 

    (define/override (select-instructions)
      (lambda (e)
	(match e
          [`(has-type ,e ,t) ((select-instructions) e)]
          [#t `(int 1)]
          [#f `(int 0)]
          [`(assign ,lhs (has-type ,rhs ,t))
           ((select-instructions) `(assign ,lhs ,rhs))]
          [`(assign ,lhs ,b) #:when (boolean? b)
           (let ([lhs ((select-instructions) lhs)]
                 [b ((select-instructions) b)])
             `((movq ,b ,lhs)))]
          [`(assign ,lhs (not ,e))
           (define new-lhs ((select-instructions) lhs))
           (define new-e ((select-instructions) e))
           (cond [(equal? new-e new-lhs)
                  `((xorq (int 1) ,new-lhs))]
                 [else `((movq ,new-e ,new-lhs) 
                         (xorq (int 1) ,new-lhs))])]
          [`(assign ,lhs (,cmp ,e1 ,e2))
	   #:when (set-member? (comparison-ops) cmp)
           (define new-lhs ((select-instructions) lhs))
           (define new-e1 ((select-instructions) e1))
           (define new-e2 ((select-instructions) e2))
           ;; second operand of cmpq can't be an immediate
           (define comparison
             (cond [(and (immediate? new-e1) (immediate? new-e2))
                    `((movq ,new-e2 (reg rax))
                      (cmpq ,new-e1 (reg rax)))]
                   [(immediate? new-e2)
                    `((cmpq ,new-e2 ,new-e1))]
                   [else 
                    `((cmpq ,new-e1 ,new-e2))]))
            ;; This works because movzbq %al, %rax is a valid instruction
           (append comparison
                   `((set ,(compare->cc cmp) (byte-reg al))
                     (movzbq (byte-reg al) ,new-lhs))
                   )]
          ;; Keep the if statement to simplify register allocation
          [`(if ,cnd ,thn-ss ,els-ss)
           (let ([cnd ((select-instructions) cnd)]
                 [thn-ss (append* (map (select-instructions) 
                                       thn-ss))]
                 [els-ss (append* (map (select-instructions)
                                       els-ss))])
             `((if ,cnd ,thn-ss ,els-ss)))]
          [`(eq? ,a1 ,a2)
           `(eq? ,((select-instructions) a1)
                 ,((select-instructions) a2))]
          [`(program ,locals (type ,ty) ,ss ...)
	    (let ([new-ss (map (select-instructions) ss)])
	      `(program ,locals (type ,ty) ,@(append* new-ss)))]
          [else ((super select-instructions) e)]
          )))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live : live-after -> S1 -> S1*

    (define/override (free-vars a)
      (match a
	 [`(byte-reg ,r) (set (byte-reg->full-reg r))]
	 [`(eq? ,e1 ,e2) (set-union (free-vars e1)
				    (free-vars e2))]
	 [else (super free-vars a)]
	 ))
    
    (define/override (read-vars instr)
      (match instr
        [`(movzbq ,s ,d) (free-vars s)]
        [`(cmpq ,s1 ,s2) (set-union (free-vars s1)
     				    (free-vars s2))]
        [(or `(andq ,s ,d) `(orq ,s ,d) `(xorq ,s ,d))
         (set-union (free-vars s) (free-vars d))]
	[`(notq ,d) (free-vars d)]
        [`(set ,cc ,d) (set)]
        [else (super read-vars instr)]))
    
    (define/override (write-vars instr)
      (match instr
        [`(movzbq ,s ,d) (free-vars d)]
        [`(cmpq ,s1 ,s2) (set '__flag)]
        [(or `(andq ,s ,d) `(orq ,s ,d) `(xorq ,s ,d)) 
         (free-vars d)]
	[`(notq ,d) (free-vars d)]
        [`(set ,cc ,d) (free-vars d)]
        [else (super write-vars instr)]))

    (define/override (uncover-live live-after)
      (lambda (ast)
	(match ast
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (define-values (new-thn-ss thn-lives)
	      ((liveness-ss live-after) thn-ss))
	    (define-values (new-els-ss els-lives)
	      ((liveness-ss live-after) els-ss))
	    ;; I doubt that thn-lives can be null -Jeremy
	    (define live-after-thn (cond [(null? thn-lives) live-after]
					 [else (car thn-lives)]))
	    (define live-after-els (cond [(null? els-lives) live-after]
					 [else (car els-lives)]))
	    (values `(if ,cnd ,new-thn-ss ,(cdr thn-lives) 
			 ,new-els-ss ,(cdr els-lives))
		    (set-union live-after-thn live-after-els
			       (free-vars cnd)))]
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
		((build-interference live-after G) inst))
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
           ;; condition codes, bit of a hack here.
	   ['e 'e] ['l 'l] ['le 'le] ['g 'g] ['ge 'ge]
	   [`(byte-reg ,r) `(byte-reg ,r)]
	   [`(,cmp ,e1 ,e2) #:when (set-member? (comparison-ops) cmp)
	    `(,cmp ,((assign-homes homes) e1)
		   ,((assign-homes homes) e2))]
	   [`(if ,cnd ,thn-ss ,els-ss)
	    (let ([cnd ((assign-homes homes) cnd)]
		  [thn-ss (map (assign-homes homes) thn-ss)]
		  [els-ss (map (assign-homes homes) els-ss)])
	      `(if ,cnd ,thn-ss ,els-ss))]
	   [`(program (,xs ...) (type ,ty) ,ss ...)
	    ;; create mapping of variables to stack locations
	    (define (make-stack-loc n)
	      `(deref rbp ,(- (+ (first-offset)
				 (* (variable-size) n)))))
	    (define new-homes
	      (make-hash (map cons xs
			      (map make-stack-loc
				   (stream->list (in-range 0 (length xs)))))))
	    (define stack-space (align 
				 (* (length xs)
				    (variable-size))
				 16))
	    `(program ,stack-space (type ,ty)
		      ,@(map (assign-homes new-homes) ss))]
	   [else ((super assign-homes homes) e)]
	   )))
      
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; lower-conditionals : psuedo-x86 -> x86
    (define/public (lower-conditionals)
      (lambda (e)
	(match e
	   [`(byte-reg ,r) `(byte-reg ,r) ]
	   [`(deref ,r ,n) `(deref ,r ,n)] 
	   [`(int ,n) `(int ,n)]
	   [`(reg ,r) `(reg ,r)]
           [`(if (,cmp ,a1 ,a2) ,thn-ss ,els-ss)
	    (let ([thn-ss (append* (map (lower-conditionals) thn-ss))]
		  [els-ss (append* (map (lower-conditionals) els-ss))]
		  [thn-label (gensym 'then)]
		  [end-label (gensym 'if_end)])
	      (append `((cmpq ,a1 ,a2)) 
		      `((jmp-if ,(compare->cc cmp) ,thn-label)) 
		      els-ss `((jmp ,end-label))
		      `((label ,thn-label)) thn-ss `((label ,end-label))
	       ))]
	   [`(callq ,f) `((callq ,f))]
	   [`(program ,stack-space (type ,ty) ,ss ...)
	    (let ([new-ss (append* (map (lower-conditionals) ss))])
	      `(program ,stack-space (type ,ty) ,@new-ss))]
	   [`(,instr ,args ...)
	    `((,instr ,@args))]
	   [else
	    (error 'lower-conditionals "unmatched " e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    (define/override (patch-instructions)
      (define (mem? x) (in-memory? x))
      (lambda (e)
	(match e
	   [`(jmp-if ,cc ,label) `((jmp-if ,cc ,label))]
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
		      ,@(append* (map (patch-instructions) ss)))]
	   [else ((super patch-instructions) e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(byte-reg ,r) (format "%~a" r)]
	   [`(set ,cc ,d) (format "\tset~a\t~a\n" cc ((print-x86) d))]
           [`(cmpq ,s1 ,s2) 
	    (format "\tcmpq\t~a, ~a\n" ((print-x86) s1)
		    ((print-x86) s2))]
	   [`(jmp-if ,cc ,label) (format "\tj~a ~a\n" cc label)]
	   [`(jmp ,label) (format "\tjmp ~a\n" label)]
	   [`(label ,l) (format "~a:\n" l)]
	   [`(program ,spill-space (type ,ty) ,ss ...)
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
	    (string-append
	     (format "\t.globl ~a\n" (label-name "main"))
	     (format "~a:\n" (label-name "main"))
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (string-append* save-callee-reg)
	     (format "\tsubq\t$~a, %rsp\n" stack-adj)
	     "\n"
	     (string-append* (map (print-x86) ss))
	     "\n"
             (print-by-type ty)
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
