#lang racket

(define print-x86-0
  (class object%
    (super-new)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; print-x86 : x86 -> string
    (define/public (print-x86)
      (lambda (e)
	(match e
           [`(stack-loc ,n) 
	    (format "~a(%rbp)" (- n))]
	   [`(int ,n) (format "$~a" n)]
	   [`(reg ,r) (format "%~a" r)]
	   [`(call ,f) (format "\tcallq\t~a\n" f)]
	   [`(program ,stack-space ,ss ...)
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
	    #:when (set-member? (send this instructions) instr-name)
	    (format "\t~a\t~a, ~a\n" instr-name
		    ((send this print-x86) s) 
		    ((send this print-x86) d))]
	   [`(,instr-name ,d)
	    #:when (set-member? (send this instructions) instr-name)
	    (format "\t~a\t~a\n" instr-name ((send this print-x86) d))]
	   [else (error "print-x86, unmatched" e)]
	   )))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define print-x86-1
  (class print-x86-0
    (super-new)

    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(byte-register ,r) (format "%~a" r)]
	   [`(sete ,d) (format "\tsete\t~a\n" ((send this print-x86) d))]
           [`(cmpq ,s1 ,s2) 
	    (format "\tcmpq\t~a, ~a\n" ((send this print-x86) s1)
		    ((send this print-x86) s2))]
	   [`(je ,label) (format "\tje ~a\n" label)]
	   [`(jmp ,label) (format "\tjmp ~a\n" label)]
	   [`(label ,l) (format "~a:\n" l)]
	   [else ((super print-x86) e)]
	   )))
    ))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define print-x86-2
  (class print-x86-1
    (super-new)
    ;; print-x86 : x86 -> string
    (define/override (print-x86)
      (lambda (e)
	(match e
	   [`(offset (stack-loc ,n) ,i)
	    (format "~a(%rbp)" (- i n))]
	   [`(offset ,e ,i)
	    (format "~a(~a)" i ((send this print-x86) e))]
	   [else ((super print-x86) e)]
	   )))
    ))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
