#lang racket
(require racket/set)
(require "utilities.rkt")

(provide int-exp-passes sexp->ast interp 
	 uniquify-mt flatten-mt instruction-selection-mt)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Convert S0 sexp to an explicitly tagged AST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (sexp->ast sexp)
  (match sexp
     [(? symbol?) `(var ,sexp)]
     [(? integer?) `(int ,sexp)]
     [`(read) `(prim read ,read)]
     [`(+ ,e1 ,e2) `(prim add ,+ ,(sexp->ast e1) ,(sexp->ast e2))]
     [`(- ,e1 ,e2) `(prim sub ,- ,(sexp->ast e1) ,(sexp->ast e2))]
     [`(- ,e) `(prim neg ,- ,(sexp->ast e))]
     [`(let ([,x ,e]) ,body)
      (let ([new-e (sexp->ast e)])
	`(let ([,x ,new-e]) ,(sexp->ast body)))]
     [else (error "sexp->ast, unhandled case in match for " sexp)]
     ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter for S0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (interp env ast)
  (match ast
     [`(var ,x)
      (cond [(equal? x 'input)
	     (read)]
	    [else
	     (cond [(assq x env) => (lambda (p) (cdr p))]
		   [else (error "undefined variable " x)])])]
     [`(int ,n) n]
     [`(prim ,name ,op ,args ...)
      (apply op (map (lambda (e) (interp env e)) args))]
     [`(let ([,x ,e]) ,body)
      (let ([v (interp env e)])
	(interp (cons (cons x v) env) body))]
     [`(program ,e) (interp env e)]
     [else
      (error interp "no match in interp for " ast)]
     ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Uniquify, S0 => S0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniquify-mt (make-hash))
(define uniquify (make-dispatcher uniquify-mt))
(hash-set!
 uniquify-mt 'var
 (lambda (env x) `(var ,(cdr (assq x env)))))
(hash-set!
 uniquify-mt 'int
 (lambda (env n) `(int ,n)))
(hash-set!
 uniquify-mt 'prim
 (lambda (env name op . es) 
   (let ([new-es (map (lambda (e) (uniquify e env)) es)])
     `(prim ,name ,op ,@new-es))))
(hash-set!
 uniquify-mt 'let
 (lambda (env b body)
   (match b
      [`([,x ,e])
       (let ([new-x (gensym x)]
	     [new-e (uniquify e env)])
	 `(let ([,new-x ,new-e])
	    ,(uniquify body (cons (cons x new-x) env))))]
      [else (error "unmatched in uniquify let" b)]
      )))
(hash-set!
 uniquify-mt 'program
 (lambda (env body)
   `(program ,(uniquify body env))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Flatten, S0 => C0
;;
;; input grammar:
;; e ::= n | x | (prim op e ...) | (let ([x e]) e)
;;
;; output grammar:
;; atomic   a  ::= n | x
;; expr     e  ::= a | (prim op a ...)
;; stmt     s  ::= (assign (var x) e) | (return a)
;; program  p  ::= (program (x ...) (s ...))
;;
;; flatten : expr -> atomic x (stmt list) x (var set)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flatten-mt (make-hash))
(define flatten (make-dispatcher flatten-mt))

(hash-set!
 flatten-mt 'var
 (lambda (need-atomic x) (values `(var ,x) '())))
(hash-set!
 flatten-mt 'int
 (lambda (need-atomic n) (values `(int ,n) '())))
(hash-set!
 flatten-mt 'prim
 (lambda (need-atomic nm op . es)
   ;; flatten the argument expressions 'es'
   (let-values ([(new-es sss) (map2 (lambda (e) (flatten e #t)) es)])
     (let ([ss (append* sss)]
	   ;; recreate the prim with the new arguments
	   [prim-apply `(prim ,nm ,op ,@new-es)])
       (cond [need-atomic
	      ;; create a temporary and assign the prim to it
	      (let* ([tmp (gensym 'tmp)]
		     [stmt `(assign (var ,tmp) ,prim-apply)])
		(values `(var ,tmp) (append ss (list stmt))))]
	     [else ;; return the recreated prim, pass along ss and xs
	      (values prim-apply ss)])))))
(hash-set! 
 flatten-mt 'let
 (lambda (need-atomic b body)
   (match b
      [`([,x ,e])
       (let-values ([(new-e e-ss) (flatten e #f)]
		    [(new-body body-ss) (flatten body #f)])
	 (values new-body
		 (append e-ss (list `(assign (var ,x) ,new-e)) body-ss)))]
      [else 
       (error "unmatched binding in flatten let" b)]
      )))
(hash-set! 
 flatten-mt 'program
 (lambda (e)
   (let-values ([(new-e ss) (flatten e #f)])
     (let ([xs (list->set (map (lambda (s) 
				 (match s [`(assign (var ,x) ,e) x])) ss))])
       `(program ,(set->list xs)
		 ,(append ss (list `(return ,new-e))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instruction Selection, C0 => psuedo-x86
;;
;; This changes instructions to the funny two-operand format of x86.
;;
;; s,d ::= (var x) | (int n) | (register r)
;; i   ::= (mov s d) | (add s d) | (sub s d) | (neg d) | (call f)
;; psuedo-x86 ::= (program (x ...) (i ...))
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define instruction-selection-mt (make-hash))
(define instruction-selection (make-dispatcher instruction-selection-mt))

(hash-set!
 instruction-selection-mt 'return
 (lambda (e) (instruction-selection `(assign (register rax) ,e))))
(hash-set!
 instruction-selection-mt 'assign
 (lambda (lhs e)
   (match e
      [`(prim ,op-name ,op ,as ...)
       (match op-name
          ['read (list `(call _read_int)
		       `(mov (register rax) ,lhs))]
	  [(or 'add 'sub)
	   (cond [(equal? (first as) lhs)
		  (list `(,op-name ,(second as) ,lhs))]
		 [(equal? (second as) lhs)
		  (list `(,op-name ,(first as) ,lhs))]
		 [else
		  (list `(mov ,(first as) ,lhs)
			`(,op-name ,(second as) ,lhs))])]
	  ['neg
	   (cond [(equal? (first as) lhs)
		  (list `(neg ,lhs))]
		 [else
		  (list `(mov ,(first as) ,lhs)
			`(neg ,lhs))])]
	  )]
      [`(var ,x)
       (cond [(equal? `(var ,x) lhs)
	      '()]
	     [else
	      (list `(mov (var ,x) ,lhs))])]
      [`(int ,n)
       (list `(mov (int ,n) ,lhs))])))

(hash-set!
 instruction-selection-mt 'program
 (lambda (xs ss)
   `(program ,xs ,(append* (map instruction-selection ss)))
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Assign Variables to Stack Locations
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define variable-size 8)
(define first-offset 16)

(define (assign-stack-loc e env)
  (match e
    [`(var ,x)
     (cond [(assq x env) => (lambda (p) `(stack-loc ,(cdr p)))]
	   [else
	    (error "in atomic->x86, undefined variable " x)])]
    [`(int ,n)
     `(int ,n)]
    [`(register ,r)
     `(register ,r)]
    [(or `(mov ,as ...) `(add ,as ...) `(sub ,as ...) `(neg ,as ...))
     (let ([instr-name (car e)])
       `(,instr-name ,@(map (lambda (a) (assign-stack-loc a env)) as)))]
    [`(call ,f)
     `(call ,f)]
    [`(program ,xs ,ss)
     ;; map variables to stack locations
     (let ([env
	    (let loop ([xs xs] [env '()] [next-offset first-offset])
	      (cond [(null? xs) env]
		    [else (loop (cdr xs)
				(cons (cons (car xs) next-offset) env)
				(+ next-offset variable-size))]))]
	   [stack-space (+ 16 (* (length xs) variable-size))])
       `(program ,stack-space ,(map (lambda (s) (assign-stack-loc s env)) ss)))]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Insert Spill Code, psuedo-x86 => x86
;;
;; Uses register rax to patch things up
;;
;; s,d ::= (register r) | (stack-loc n) | (int n)
;; i   ::= (mov s d) | (add s d) | (sub s d) | (neg d) | (call f)
;; x86 ::= (program stack-space (i ...))
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (on-stack? a)
  (match a
     [`(stack-loc ,n) #t]
     [else #f]))

(define (insert-spill-code e)
  (match e
     [`(mov ,s ,d)
      (cond [(and (on-stack? s) (on-stack? d))
	     (list `(mov ,s (register rax))
		   `(mov (register rax) ,d))]
	    [else
	     (list `(mov ,s ,d))])]
     [(or `(add ,s ,d) `(sub ,s ,d))
      (let ([instr-name (car e)])
	(cond [(and (on-stack? s) (on-stack? d))	
	       (list `(mov ,s (register rax))
		     `(,instr-name (register rax) ,d))]
	      [else
	       (list `(,instr-name ,s ,d))]))]
     [`(neg ,d) (list `(neg ,d))]
     [`(call ,f) (list `(call ,f))]
     [`(program ,stack-space ,ss)
      `(program ,stack-space ,(append* (map insert-spill-code ss)))]
     ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Print x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (print-x86 e)
  (match e
    [`(stack-loc ,n) 
     (format "-~a(%rbp)" n)]
    [`(int ,n) (format "$~a" n)]
    [`(register ,r) (format "%~a" r)]
    [`(call ,f) (format "\tcallq\t~a\n" f)]
    [`(mov ,s ,d)
     (format "\tmovq\t~a,~a\n" (print-x86 s) (print-x86 d))]
    [`(add ,s ,d)
     (format "\taddq\t~a,~a\n" (print-x86 s) (print-x86 d))]
    [`(sub ,s ,d)
     (format "\tsubq\t~a,~a\n" (print-x86 s) (print-x86 d))]
    [`(neg ,d)
     (format "\tnegq\t~a\n" (print-x86 d))]
    [`(program ,stack-space ,ss)
     (string-append
      (format "\t.globl _main\n")
      (format "_main:\n")
      (format "\tpushq\t%rbp\n")
      (format "\tmovq\t%rsp, %rbp\n")
      (format "\tsubq\t$~a, %rsp\n" stack-space)
      "\n"
      (string-append* (map print-x86 ss))
      "\n"
      (format "\taddq\t$~a, %rsp\n" stack-space)
      (format "\tpopq\t%rbp\n")
      (format "\tretq\n")
      )]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-exp-passes
  (list (cons "sexp->ast" (lambda (sexp) `(program ,(sexp->ast sexp))))
	(cons "uniquify" (lambda (ast) (uniquify ast '())))
	(cons "flatten" flatten)
	(cons "instruction selection" instruction-selection)
	(cons "assign locations" (lambda (ast) (assign-stack-loc ast '())))
	(cons "insert spill code" insert-spill-code)
	(cons "print x86" print-x86)
	))
