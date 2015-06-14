#lang racket
(require racket/set)

(define assert
  (lambda (msg b)
    (if (not b)
	(begin
	  (display "ERROR: ")
	  (display msg)
	  (newline))
	(void))))

(define (gen-dispatcher mt)
  (lambda (e . rest)
    (match e
       [`(,tag ,args ...)
	(apply (hash-ref mt tag) (append rest args))]
       [else
	(error "no match in dispatcher for " e)]
       )))

(define (sexp->ast sexp)
  (match sexp
     [(? symbol?) `(var ,sexp)]
     [(? integer?) `(int ,sexp)]
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
(define uniquify (gen-dispatcher uniquify-mt))
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
;; program  p  ::= (program xs ss)
;;
;; flatten : expr -> atomic x (stmt list) x (var set)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flatten-mt (make-hash))
(define flatten (gen-dispatcher flatten-mt))

(hash-set!
 flatten-mt 'var
 (lambda (x) (values `(var ,x) '() (set))))
(hash-set!
 flatten-mt 'int
 (lambda (n) (values `(int ,n) '() (set))))
(hash-set!
 flatten-mt 'prim
 (lambda (nm op . es)
   (let loop ([es (reverse es)] [new-es '()] [ss '()] [xs (set)])
     (cond [(null? es)
	    (let* ([tmp (gensym 'tmp)]
		   [stmt `(assign ,tmp (prim ,nm ,op ,@new-es))])
	      (values `(var ,tmp) (append ss (list stmt)) 
		      (set-add xs tmp)))]
	   [else
	    (let-values ([(new-e e-ss e-xs) (flatten (car es))])
	      (loop (cdr es) (cons new-e new-es) (append e-ss ss) 
		    (set-union e-xs xs)))]))))
(hash-set! 
 flatten-mt 'let
 (lambda (b body)
   (match b
      [`([,x ,e])
       (let-values ([(new-e e-ss e-xs) (flatten e)]
		    [(new-body body-ss body-xs) (flatten body)])
	 (values new-body
		 (append e-ss (list `(assign ,x ,new-e)) body-ss)
		 (set-union e-xs body-xs (set x))))]
      [else 
       (error "unmatched binding in flatten let" b)]
      )))
(hash-set! 
 flatten-mt 'program
 (lambda (e)
   (let-values ([(new-e ss xs) (flatten e)])
     `(program ,(set->list xs) ,(append ss (list `(return ,new-e)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instruction Selection, C0 => x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define instruction-selection-mt (make-hash))
(define instruction-selection (gen-dispatcher instruction-selection-mt))

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
 (lambda (env a) 
   (format "\tmovq\t~a, %rax\n" (atomic->x86 env a))))
(hash-set!
 instruction-selection-mt 'prim
 (lambda (env name op . as)
   (let ([as (map (lambda (a) (atomic->x86 env a)) as)])
     (match name
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
    (format "\tmovq\t%rax,~a\n" (atomic->x86 env `(var ,x)))
    )))

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
			 (+ next-offset variable-size))]))])
    (string-append
     (format "\t.globl _main\n")
     (format "_main:\n")
     (format "\tpushq\t%rbp\n")
     (format "\tmovq\t%rsp, %rbp\n")
     (string-append* (map (lambda (s) (instruction-selection s env)) ss))
     (format "\tpopq\t%rbp\n")
     (format "\tretq\n")
     )
   )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test prog)
  (let* ([ast0 (sexp->ast prog)]
	 [result (interp '() ast0)]
	 [ast1 (uniquify ast0 '())]
	 [ast2 (flatten ast1)]
	 )
    (assert "uniquified program produced incorrect result"
	    (equal? result (interp '() ast1)))
    (assert "flattened program produced incorrect result"
	    (equal? result (interp '() ast2)))
    ))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define debug-state #f)
(define (debug label val)
  (if debug-state
      (begin
	(printf "~a:\n" label)
	(display val)
	(newline))
      (void)))

(let* ([in-file-name (vector-ref (current-command-line-arguments) 0)]
       [file-base (string-trim in-file-name ".scm")]
       [in-file (open-input-file in-file-name)]
       [out-file-name (string-append file-base ".s")]
       [out-file (open-output-file #:exists 'replace out-file-name)]
       [sexp (read in-file)])
  (define ast `(program ,(sexp->ast sexp)))
  (debug "ast" ast)

  (define uniq-ast (uniquify ast '()))
  (debug "uniq-ast" uniq-ast)

  (define flat-ast (flatten uniq-ast))
  (debug "flat-ast" flat-ast)

  (define x86 (instruction-selection flat-ast '()))
  (debug "x86" x86)

  (write-string x86 out-file)
  (newline out-file)
  )

