#lang racket
(require racket/pretty)
(provide debug map2 lookup make-dispatcher assert 
	 compile compile-file check-passes fix while 
	 make-graph add-edge adjacent
	 general-registers caller-save callee-save arg-registers
	 register->color registers align)

(define debug-state #f)

(define (debug label val)
  (if debug-state
      (begin
	(printf "~a:\n" label)
	(pretty-print val)
	(newline))
      (void)))

(define-syntax-rule (while condition body ...)
  (let loop ()
    (when condition
      body ...
      (loop))))

(define fix (lambda (f) (lambda (x) ((f (fix f)) x))))

(define (map2 f ls)
  (cond [(null? ls)
         (values '() '())]
        [else
         (let-values ([(x1 x2) (f (car ls))]
                      [(ls1 ls2) (map2 f (cdr ls))])
           (values (cons x1 ls1) (cons x2 ls2)))]))

(define lookup
  (lambda (x ls)
    (cond [(assq x ls) => cdr]
	  [else
	   (error "lookup failed for " x)])))

(define (make-dispatcher mt)
  (lambda (e . rest)
    (match e
       [`(,tag ,args ...)
	(apply (hash-ref mt tag) (append rest args))]
       [else
	(error "no match in dispatcher for " e)]
       )))

(define (check-passes name passes)
  (lambda (test-name)
    (debug "** compiler " name)
    (debug "** checking passes for test " test-name)
    (define input-file-name (format "tests/~a.in" test-name))
    (define program-name (format "tests/~a.scm" test-name))
    (define program-file (open-input-file program-name))
    (define sexp (read program-file))
    (close-input-port program-file)
    (debug "program:" sexp)

    (let loop ([passes passes] [p sexp] [result #f])
      (cond [(null? passes) result]
	    [else
	     (match (car passes)
		[`(,pass-name ,pass ,interp)
		 (debug "running pass" pass-name)
		 (define new-p (pass p))
		 (debug pass-name new-p)
		 (cond [interp
			(let ([new-result 
			       (if (file-exists? input-file-name)
				   (begin
				     (with-input-from-file input-file-name
				       (lambda () (interp new-p))))
				   (interp new-p))])
			  (cond [result
				 (cond [(equal? result new-result)
					(loop (cdr passes) new-p new-result)]
				       [else
					(display "in program")(newline)
					(pretty-print new-p)(newline)
					(error (format "differing results in compiler '~a' pass '~a', expected ~a, not" name pass-name result )
					       new-result)])]
				[else ;; no result to check yet
				 (loop (cdr passes) new-p new-result)]))]
		       [else
			(loop (cdr passes) new-p result)])])]))
    ))

(define (compile passes)
  (let ([prog-file-name (vector-ref (current-command-line-arguments) 0)])
    ((compile-file passes) prog-file-name)))

(define (compile-file passes)
  (lambda (prog-file-name)
    (define file-base (string-trim prog-file-name ".scm"))
    (define prog-file (open-input-file prog-file-name))
    (define out-file-name (string-append file-base ".s"))
    (define out-file (open-output-file #:exists 'replace out-file-name))
    (define sexp (read prog-file))
    (close-input-port prog-file)
    (let ([x86 (let loop ([passes passes] [p sexp])
		 (cond [(null? passes) p]
		       [else
			(match (car passes)
			   [`(,name ,pass ,interp)
			    (let* ([new-p (pass p)])
			      (debug name new-p)
			      (loop (cdr passes) new-p)
			      )])]))])
      (cond [(string? x86)
	     (write-string x86 out-file)
	     (newline out-file)]
	    [else
	     (error "compiler did not produce x86 output")])
      )
    (close-output-port out-file)
    ))

(define assert
  (lambda (msg b)
    (if (not b)
	(begin
	  (display "ERROR: ")
	  (display msg)
	  (newline))
	(void))))


;; System V Application Binary Interface
;; AMD64 Architecture Processor Supplement
;; Edited by Jan Hubicˇka, Andreas Jaeger, Mark Mitchell
;; December 2, 2003

(define arg-registers (vector 'rdi 'rsi 'rdx 'rcx 'r8 'r9))

(define caller-save (set 'rdx 'rcx 'rsi 'rdi 'r8 'r9 'r10 'r11 ))
(define callee-save (set 'rbx 'r12 'r13 'r14 'r15))

;; there are 13 general registers:
(define general-registers (vector 'rbx 'rcx 'rdx 'rsi 'rdi
    				  'r8 'r9 'r10 'r11 'r12 
				  'r13 'r14 'r15))
(define reg-colors
  '((rax . -1) (__flag . -1)
    (rbx . 0) (rcx . 1) (rdx . 2) (rsi . 3) (rdi . 4)
    (r8 . 5) (r9 . 6) (r10 . 7) (r11 . 8) (r12 . 9) (r13 . 10)
    (r14 . 11) (r15 . 12)))

(define (register->color r)
  (cdr (assq r reg-colors)))

(define registers (set-union (list->set (vector->list general-registers))
			     (set 'rax 'rsp 'rbp '__flag)))

(define (align n alignment)
  (cond [(eq? 0 (modulo n alignment))
	 n]
	[else
	 (+ n (- alignment (modulo n alignment)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Graph ADT

(define (make-graph vertices)
  (make-hash (map (lambda (v) (cons v (set))) vertices)))

(define (add-edge graph u v)
  (hash-set! graph u (set-add (hash-ref graph u (set)) v))
  (hash-set! graph v (set-add (hash-ref graph v (set)) u)))

(define (adjacent graph u)
  (hash-ref graph u))


