#lang racket
(require racket/set)
(require "utilities.rkt")

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
;; stmt     s  ::= (assign x e) | (return a)
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
		     [stmt `(assign ,tmp ,prim-apply)])
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
		 (append e-ss (list `(assign ,x ,new-e)) body-ss)))]
      [else 
       (error "unmatched binding in flatten let" b)]
      )))
(hash-set! 
 flatten-mt 'program
 (lambda (e)
   (let-values ([(new-e ss) (flatten e #f)])
     (let ([xs (list->set (map (lambda (s) 
				 (match s [`(assign ,x ,e) x])) ss))])
       `(program ,(set->list xs)
		 ,(append ss (list `(return ,new-e))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instruction Selection, C0 => x86
;;
;; This version of instruction selection is non-optimal in that it
;; always puts the RHS of an assignment into register rax before
;; moving it to the destination.
;; 
;; We introduce a smarter algorithm later as part of register allocation.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define instruction-selection-mt (make-hash))
(define instruction-selection (make-dispatcher instruction-selection-mt))

(define (atomic->x86 env a)
  (match a
    [`(var ,x) 
     (cond [(assq x env) => 
	    (lambda (p)
	      (format "-~a(%rbp)" (cdr p)))]
	   [else
	    (error "in atomic->x86, undefined variable " x)])]
    [`(int ,n) (format "$~a" n)]
    ))

(hash-set!
 instruction-selection-mt 'var
 (lambda (env x) 
   (format "\tmovq\t~a,%rax\n" (atomic->x86 env `(var ,x)))))
(hash-set!
 instruction-selection-mt 'int
 (lambda (env n) 
   (format "\tmovq\t~a,%rax\n" (atomic->x86 env `(int ,n)))))
(hash-set!
 instruction-selection-mt 'return
 (lambda (env e) 
   (instruction-selection e env)))
(hash-set!
 instruction-selection-mt 'prim
 (lambda (env name op . as)
   (let ([as (map (lambda (a) (atomic->x86 env a)) as)])
     (match name
	['read
	 (format "\tcallq\t_read_int\n")]
        ['add 
	 (string-append
	  (format "\tmovq\t~a,%rax\n" (first as))
	  (format "\taddq\t~a,%rax\n" (second as)))]
	['sub 
	 (string-append
	  (format "\tmovq\t~a,%rax\n" (first as))
	  (format "\tsubq\t~a,%rax\n" (second as)))]
	['neg
	 (string-append
	  (format "\tmovq\t~a,%rax\n" (first as))
	  (format "\tnegq\t%rax\n"))]
	))))
(hash-set!
 instruction-selection-mt 'assign
 (lambda (env x e)
   (string-append
    (instruction-selection e env)
    (format "\tmovq\t%rax,~a\n\n" (atomic->x86 env `(var ,x))))))

(define variable-size 8)
(define first-offset 16)

(hash-set!
 instruction-selection-mt 'program
 (lambda (env xs ss)
   ;; map variables to stack locations
   (let ([env
	  (let loop ([xs xs] [env '()] [next-offset first-offset])
	    (cond [(null? xs) env]
		  [else
		   (loop (cdr xs)
			 (cons (cons (car xs) next-offset) env)
			 (+ next-offset variable-size))]))]
	 [stack-space (+ 16 (* (length xs) variable-size))])
    (string-append
     (format "\t.globl _main\n")
     (format "_main:\n")
     (format "\tpushq\t%rbp\n")
     (format "\tmovq\t%rsp, %rbp\n")
     (format "\tsubq\t$~a, %rsp\n" stack-space)
     "\n"
     (string-append* (map (lambda (s) (instruction-selection s env)) ss))
     "\n"
     (format "\taddq\t$~a, %rsp\n" stack-space)
     (format "\tpopq\t%rbp\n")
     (format "\tretq\n")
     )
   )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-exp-passes
  (list (cons "sexp->ast" (lambda (sexp) `(program ,(sexp->ast sexp))))
	(cons "uniquify" (lambda (ast) (uniquify ast '())))
	(cons "flatten" flatten)
	(cons "instruction selection" 
	      (lambda (flat-ast) (instruction-selection flat-ast '())))
	))
(compile int-exp-passes)

