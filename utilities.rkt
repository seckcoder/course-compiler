#lang racket
(require racket/pretty)
(provide debug map2 make-dispatcher assert 
	 compile compile-file check-passes fix while)

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
	(pretty-print val)
	(newline))
      (void)))

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
		[`(,name ,pass ,interp)
		 (debug "running pass" name)
		 (let* ([new-p (pass p)])
		   (debug name new-p)
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
					  (error (format "differing results in pass ~a, expected ~a, not" name result)
						 new-result)])]
				  [else ;; no result to check yet
				   (loop (cdr passes) new-p new-result)]))]
			 [else
			  (loop (cdr passes) new-p result)]))])]))
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
