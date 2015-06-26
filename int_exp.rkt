#lang racket
(require racket/set racket/stream)
(require "utilities.rkt")
(require "interp.rkt")

(provide int-exp-passes compile-S0)

(define compile-S0
  (class object%

    (super-new)

    (define/public (primitives)
      (set '+ '- '*))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Uniquify, S0 => S0
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (uniquify env)
      (lambda (e)
	(match e
	   [(? symbol?)
	    (cdr (assq e env))]
	   [(? integer?)
	    e]
	   [`(,op ,es ...)
	    #:when (or (set-member? (send this primitives) op) (eq? op 'read))
	    (let ([new-es (map (send this uniquify env) es)])
	      `(,op ,@new-es))]
	   [`(let ([,x ,e]) ,body)
	    (let ([new-x (gensym x)]
		  [new-e ((send this uniquify env) e)])
	      `(let ([,new-x ,new-e])
		 ,((send this uniquify (cons (cons x new-x) env)) body)))]
	   [`(program ,extra ,body)
	    `(program ,extra ,((send this uniquify env) body))]
	   [else
	    (error "uniquify couldn't match" e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Flatten, S0 => C0
    ;;
    ;; flatten : expr -> atomic x (stmt list)
    ;;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (collect-locals)
      (lambda (ast)
	(match ast
	   [`(assign ,x ,e) (list x)]
	   [`(return ,e) '()]
	   [else
	    (error "unmatched in collect-locals S0" ast)]
	   )))

    (define/public (flatten need-atomic)
      (lambda (e)
        (match e
           [(? symbol?)
	    (values e '())]
	   [(? integer?)
	    (values e '())]
	   [`(let ([,x ,e]) ,body)
	    (define-values (new-e e-ss) ((send this flatten #f) e))
	    (define-values (new-body body-ss) ((send this flatten #f) body))
	    (values new-body
		    (append e-ss (list `(assign ,x ,new-e)) body-ss))]
	   [`(program ,extra ,e)
	    (define-values (new-e ss) ((send this flatten #f) e))
	    (define xs 
	      (list->set (append* (map (send this collect-locals) ss))))
	    `(program ,(set->list xs) ,(append ss (list `(return ,new-e))))]
	   [`(,op ,es ...)
	    #:when (or (set-member? (send this primitives) op) (eq? op 'read))
	    ;; flatten the argument expressions 'es'
	    (define-values (new-es sss) (map2 (send this flatten #t) es))
	    (define ss (append* sss))
	    ;; recreate the prim with the new arguments
	    (define prim-apply `(,op ,@new-es))
	    (cond [need-atomic
		   ;; create a temporary and assign the prim to it
		   (let* ([tmp (gensym 'tmp)]
			  [stmt `(assign ,tmp ,prim-apply)])
		     (values tmp (append ss (list stmt))))]
		  [else ;; return the recreated prim, pass along ss and xs
		   (values prim-apply ss)])]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Instruction Selection, C0 => psuedo-x86
    ;;
    ;; This changes instructions to the funny two-operand format of x86.
    ;; 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (binary-op->inst op)
      (match op
         ['+ 'add]
	 ['- 'sub]
	 ['* 'imul]
	 [else (error "in binary-op->inst unmatched" op)]
	 ))

    (define/public (unary-op->inst op)
      (match op
	 ['- 'neg]
	 [else (error "in unary-op->inst unmatched" op)]
	 ))

    (define/public (instruction-selection)
      (lambda (e)
	(match e
           [(? symbol?)
	    `(var ,e)]
	   [(? integer?)
	    `(int ,e)]
	   [`(register ,r)
	    `(register ,r)]
	   [`(return ,e)
	    ((send this instruction-selection) `(assign (register rax) ,e))]
	   [`(assign ,lhs (read))
	    (let ([lhs ((send this instruction-selection) lhs)])
	      (list `(call _read_int)
		    `(mov (register rax) ,lhs)))]
	   [`(assign ,lhs (,op ,e1 ,e2))
	    #:when (set-member? (send this primitives) op)
	    (let ([lhs ((send this instruction-selection) lhs)]
		  [e1 ((send this instruction-selection) e1)]
		  [e2 ((send this instruction-selection) e2)]
		  [inst (binary-op->inst op)])
	      (cond [(equal? e1 lhs)
		     (list `(,inst ,e2 ,lhs))]
		    [(equal? e2 lhs)
		     (list `(,inst ,e1 ,lhs))]
		    [else
		     (list `(mov ,e1 ,lhs)
			   `(,inst ,e2 ,lhs))]))]
	   [`(assign ,lhs (,op ,e1))	
	    #:when (set-member? (send this primitives) op)
	    (let ([lhs ((send this instruction-selection) lhs)]
		  [e1 ((send this instruction-selection) e1)]
		  [inst (unary-op->inst op)])
	      (cond [(equal? e1 lhs)
		     (list `(,inst ,lhs))]
		    [else
		     (list `(mov ,e1 ,lhs)
			   `(,inst ,lhs))]))]
	   [`(assign ,lhs ,x)
	    #:when (symbol? x)
	    (let ([lhs ((send this instruction-selection) lhs)])
	      (cond [(equal? `(var ,x) lhs)
		     '()]
		    [else
		     (list `(mov (var ,x) ,lhs))]))]
	   [`(assign ,lhs ,n)
	    #:when (integer? n)
	    (let ([lhs ((send this instruction-selection) lhs)])
	      (list `(mov (int ,n) ,lhs)))]
	   [`(program ,xs ,ss)
	    `(program ,xs
		      ,(append* (map (send this instruction-selection) ss)))]
	   [else
	    (error "instruction selection, unmatched " e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;
    ;; Assign Variables to Locations
    ;;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (variable-size) 8)
    (define/public (first-offset) 16)

    (define/public (assign-locations homes)
      (lambda (e)
	(match e
	   [`(var ,x)
	    (hash-ref homes x)]
	   [`(int ,n)
	    `(int ,n)]
	   [`(register ,r)
	    `(register ,r)]
	   [`(call ,f)
	    `(call ,f)]
	   [(or `(mov ,as ...) `(add ,as ...) `(sub ,as ...) `(neg ,as ...))
	    (let ([instr-name (car e)])
	      `(,instr-name ,@(map (send this assign-locations homes) as)))]
	   [`(program ,xs ,ss)
	    ;; map variables to stack locations
	    (let* ([make-stack-loc
		    (lambda (n)
		      `(stack-loc ,(+ (send this first-offset)
				      (* (send this variable-size) 
					 n))))]
		   [new-homes
		    (make-hash
		     (map cons xs
			  (map make-stack-loc
			       (stream->list (in-range 0 (length xs))))))]
		  [stack-space (+ (send this first-offset)
				  (* (length xs) (send this variable-size)))])
	      `(program ,stack-space
			,(map (send this assign-locations new-homes) ss)))]
	   [else
	    (error "in assign-locations S0, unmatched" e)]
	   )))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Insert Spill Code, psuedo-x86 => x86
    ;;
    ;; Uses register rax to patch things up
    ;;
    ;; s,d ::= (register r) | (stack-loc n) | (int n)
    ;; i   ::= (mov s d) | (add s d) | (sub s d) | (neg d) | (call f)
    ;; x86 ::= (program stack-space (i ...))
    ;; 
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (on-stack? a)
      (match a
         [`(stack-loc ,n) #t]
	 [else #f]))

    (define/public (insert-spill-code)
      (lambda (e)
	(match e
           [`(mov ,s ,d)
	    (cond [(equal? s d) ;; trivial move, delete it
		   '()]
		  [(and (on-stack? s) (on-stack? d))
		   (list `(mov ,s (register rax))
			 `(mov (register rax) ,d))]
		  [else
		   (list `(mov ,s ,d))])]
	   [`(call ,f) (list `(call ,f))]
	   [`(program ,stack-space ,ss)
	    `(program ,stack-space 
		      ,(append* (map (send this insert-spill-code) ss)))]
	   [`(,instr-name ,s ,d)
	    (cond [(and (on-stack? s) (on-stack? d))	
		   (list `(mov ,s (register rax))
			 `(,instr-name (register rax) ,d))]
		  [else
		   (list `(,instr-name ,s ,d))])]
	   [`(,instr-name ,d)
	    (list `(,instr-name ,d))]
	   )))
  
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Print x86
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (define/public (print-x86)
      (lambda (e)
	(match e
           [`(stack-loc ,n) 
	    (format "-~a(%rbp)" n)]
	   [`(int ,n) (format "$~a" n)]
	   [`(register ,r) (format "%~a" r)]
	   [`(call ,f) (format "\tcallq\t~a\n" f)]
	   [`(program ,stack-space ,ss)
	    (string-append
	     (format "\t.globl _main\n")
	     (format "_main:\n")
	     (format "\tpushq\t%rbp\n")
	     (format "\tmovq\t%rsp, %rbp\n")
	     (format "\tsubq\t$~a, %rsp\n" stack-space)
	     "\n"
	     (string-append* (map (send this print-x86) ss))
	     "\n"
	     (format "\taddq\t$~a, %rsp\n" stack-space)
	     (format "\tpopq\t%rbp\n")
	     (format "\tretq\n")
	     )]
	   [`(,instr-name ,s ,d)
	    (format "\t~aq\t~a, ~a\n" instr-name
		    ((send this print-x86) s) 
		    ((send this print-x86) d))]
	   [`(,instr-name ,d)
	    (format "\t~aq\t~a\n" instr-name ((send this print-x86) d))]
	   [else
	    (error "print-x86, unmatched" e)]
	   )))

    )) ;; class compile-S0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-exp-passes
  (let ([compiler (new compile-S0)]
	[interp (new interp-S0)])
    (list `("uniquify" ,(lambda (ast) ((send compiler uniquify '())
				       `(program () ,ast)))
	    ,(send interp interp-scheme '()))
	  `("flatten" ,(send compiler flatten #f)
	    ,(send interp interp-C '()))
	  `("instruction selection" ,(send compiler instruction-selection)
	    ,(send interp interp-x86 '()))
	  `("assign locations" ,(send compiler assign-locations (void))
	    ,(send interp interp-x86 '()))
	  `("insert spill code" ,(send compiler insert-spill-code)
	    ,(send interp interp-x86 '()))
	  `("print x86" ,(send compiler print-x86) #f)
	  )))

