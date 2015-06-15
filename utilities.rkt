#lang racket
(provide map2 make-dispatcher assert compile)

(define (map2 f ls)
  (cond [(null? ls)
         (values '() '())]
        [else
         (let-values ([(x1 x2) (f (car ls))]
                      [(ls1 ls2) (map2 f (cdr ls))])
           (values (cons x1 ls1) (cons x2 ls2)))]))

(define (make-dispatcher mt)
  (lambda (e . rest)
    (match e
       [`(,tag ,args ...)
	(apply (hash-ref mt tag) (append rest args))]
       [else
	(error "no match in dispatcher for " e)]
       )))

(define debug-state #f)
(define (debug label val)
  (if debug-state
      (begin
	(printf "~a:\n" label)
	(display val)
	(newline))
      (void)))

(define (compile passes)
  (let* ([in-file-name (vector-ref (current-command-line-arguments) 0)]
	 [file-base (string-trim in-file-name ".scm")]
	 [in-file (open-input-file in-file-name)]
	 [out-file-name (string-append file-base ".s")]
	 [out-file (open-output-file #:exists 'replace out-file-name)]
	 [sexp (read in-file)])
    (let ([x86 (let loop ([passes passes] [p sexp])
		 (cond [(null? passes) p]
		       [else (let* ([new-p ((cdr (car passes)) p)])
			       (debug (car (car passes)) new-p)
			       (loop (cdr passes) new-p))]))])
      (write-string x86 out-file)
      (newline out-file)
      )))

(define assert
  (lambda (msg b)
    (if (not b)
	(begin
	  (display "ERROR: ")
	  (display msg)
	  (newline))
	(void))))