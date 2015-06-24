#lang racket
(require racket/set racket/stream)
(require "utilities.rkt")
(require "interp.rkt")

(provide int-exp-passes
	 uniquify
	 flatten
	 instruction-selection
	 assign-locations
	 insert-spill-code
	 print-x86)

(define primitives (set '+ '- '*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Uniquify, S0 => S0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify recur)
  (lambda (env)
    (lambda (e)
      (match e
	 [(? symbol?)
	  (cdr (assq e env))]
	 [(? integer?)
	  e]
	 [`(,op ,es ...)
	  #:when (or (set-member? primitives op) (eq? op 'read))
	  (let ([new-es (map (recur env) es)])
	    `(,op ,@new-es))]
	 [`(let ([,x ,e]) ,body)
	  (let ([new-x (gensym x)]
		[new-e ((recur env) e)])
	    `(let ([,new-x ,new-e])
	       ,((recur (cons (cons x new-x) env)) body)))]
	 [`(program ,extra ,body)
	  `(program ,extra ,((recur env) body))]
	 [else
	  (error "uniquify couldn't match" e)]))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Flatten, S0 => C0
;;
;; flatten : expr -> atomic x (stmt list)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (flatten recur)
  (lambda (need-atomic)
    (lambda (e)
      (match e
         [(? symbol?)
	  (values e '())]
	 [(? integer?)
	  (values e '())]
	 [`(let ([,x ,e]) ,body)
	  (let-values ([(new-e e-ss) ((recur #f) e)]
		       [(new-body body-ss) ((recur #f) body)])
	    (values new-body
		    (append e-ss (list `(assign ,x ,new-e)) body-ss)))]
	 [`(program ,extra ,e)
	  (let-values ([(new-e ss) ((recur #f) e)])
	    (let ([xs (list->set (map (lambda (s) 
				 (match s [`(assign ,x ,e) x])) ss))])
	      `(program ,(set->list xs)
			,(append ss (list `(return ,new-e))))))]
	 [`(,op ,es ...)
	  #:when (or (set-member? primitives op) (eq? op 'read))
	  ;; flatten the argument expressions 'es'
	  (let-values ([(new-es sss) (map2 (recur #t) es)])
	    (let ([ss (append* sss)]
		  ;; recreate the prim with the new arguments
		  [prim-apply `(,op ,@new-es)])
	      (cond [need-atomic
		     ;; create a temporary and assign the prim to it
		     (let* ([tmp (gensym 'tmp)]
			    [stmt `(assign ,tmp ,prim-apply)])
		       (values tmp (append ss (list stmt))))]
		    [else ;; return the recreated prim, pass along ss and xs
		     (values prim-apply ss)])))]
	 ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instruction Selection, C0 => psuedo-x86
;;
;; This changes instructions to the funny two-operand format of x86.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-op->inst
  (lambda (op)
    (match op
       ['+ 'add]
       ['- 'sub]
       ['* 'mul]
       )))

(define unary-op->inst
  (lambda (op)
    (match op
       ['- 'neg]
       )))

(define (instruction-selection recur)
  (lambda (e)
    (debug "selecting instruction for" e)
    (match e
       [(? symbol?)
        `(var ,e)]
       [(? integer?)
        `(int ,e)]
       [`(register ,r)
	`(register ,r)]
       [`(return ,e)
	(recur `(assign (register rax) ,e))]
       [`(assign ,lhs (read))
	(let ([lhs (recur lhs)])
	  (list `(call _read_int)
		`(mov (register rax) ,lhs)))]
       [`(assign ,lhs (,op ,e1 ,e2))
	#:when (set-member? primitives op)
	(let ([lhs (recur lhs)]
	      [e1 (recur e1)]
	      [e2 (recur e2)]
	      [inst (binary-op->inst op)])
	  (cond [(equal? e1 lhs)
		 (list `(,inst ,e2 ,lhs))]
		[(equal? e2 lhs)
		 (list `(,inst ,e1 ,lhs))]
		[else
		 (list `(mov ,e1 ,lhs)
		       `(,inst ,e2 ,lhs))]))]
       [`(assign ,lhs (,op ,e1))	
	#:when (set-member? primitives op)
	(let ([lhs (recur lhs)]
	      [e1 (recur e1)]
	      [inst (unary-op->inst op)])
	  (cond [(equal? e1 lhs)
		 (list `(,inst ,lhs))]
		[else
		 (list `(mov ,e1 ,lhs)
		       `(,inst ,lhs))]))]
       [`(assign ,lhs ,x)
	#:when (symbol? x)
	(let ([lhs (recur lhs)])
	  (cond [(equal? `(var ,x) lhs)
		 '()]
		[else
		 (list `(mov (var ,x) ,lhs))]))]
       [`(assign ,lhs ,n)
	#:when (integer? n)
	(let ([lhs (recur lhs)])
	  (list `(mov (int ,n) ,lhs)))]
       [`(program ,xs ,ss)
	`(program ,xs ,(append* (map recur ss)))]
       [else
	(error "instruction selection, unmatched " e)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Assign Variables to Locations
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define variable-size 8)
(define first-offset 16)

(define	(assign-locations recur)
  (lambda (homes)
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
	    `(,instr-name ,@(map (recur homes) as)))]
	 [`(program ,xs ,ss)
	  ;; map variables to stack locations
	  (let ([new-homes
		 (make-hash
		  (map cons xs
		       (map (lambda (n)
			      `(stack-loc ,(+ first-offset
					      (* variable-size n))))
			    (stream->list (in-range 0 (length xs))))))]
		[stack-space (+ first-offset (* (length xs) variable-size))])
	    `(program ,stack-space ,(map (recur new-homes) ss)))]
	 ))))

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

(define (insert-spill-code recur)
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
	`(program ,stack-space ,(append* (map recur ss)))]
       )))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Print x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (print-x86 recur)
  (lambda (e)
    (match e
       [`(stack-loc ,n) 
	(format "-~a(%rbp)" n)]
       [`(int ,n) (format "$~a" n)]
       [`(register ,r) (format "%~a" r)]
       [`(call ,f) (format "\tcallq\t~a\n" f)]
       [`(mov ,s ,d)
	(format "\tmovq\t~a,~a\n" (recur s) (recur d))]
       [`(add ,s ,d)
	(format "\taddq\t~a,~a\n" (recur s) (recur d))]
       [`(sub ,s ,d)
	(format "\tsubq\t~a,~a\n" (recur s) (recur d))]
       [`(neg ,d)
	(format "\tnegq\t~a\n" (recur d))]
       [`(program ,stack-space ,ss)
	(string-append
	 (format "\t.globl _main\n")
	 (format "_main:\n")
	 (format "\tpushq\t%rbp\n")
	 (format "\tmovq\t%rsp, %rbp\n")
	 (format "\tsubq\t$~a, %rsp\n" stack-space)
	 "\n"
	 (string-append* (map recur ss))
	 "\n"
	 (format "\taddq\t$~a, %rsp\n" stack-space)
	 (format "\tpopq\t%rbp\n")
	 (format "\tretq\n")
	 )]
       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-exp-passes
  (list `("uniquify" ,(lambda (ast) (((fix uniquify) '())
				     `(program () ,ast)))
	  ,((fix interp-S0) '()))
	`("flatten" ,((fix flatten) #f)
	  ,((fix interp-C0) '()))
	`("instruction selection" ,(fix instruction-selection)
	  ,((fix interp-x86) '()))
	`("assign locations" ,((fix assign-locations) (void))
	  ,((fix interp-x86) '()))
	`("insert spill code" ,(fix insert-spill-code)
	  ,((fix interp-x86) '()))
	`("print x86" ,(fix print-x86) #f)
	))
