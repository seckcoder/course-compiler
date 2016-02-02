#lang racket
(require racket/pretty)
(require (for-syntax racket))
(provide debug-level debug vomit
         map2 label-name lookup  make-dispatcher assert
         read-fixnum read-program 
	 compile compile-file check-passes interp-tests compiler-tests fix while 
	 make-graph add-edge adjacent vertices print-dot
	 general-registers registers-for-alloc caller-save callee-save
	 arg-registers register->color registers align)

;; debug state is a possitive integer range.
;; The higher the setting the more information is reported.
(define debug-level
  (make-parameter
   0
   (lambda (d)
     (unless (exact-nonnegative-integer? d) 
       (error 'debug-state "expected nonnegative-integer in ~a" d))
     d)))

;; Check to see if debug state is at least some level
(define (at-debug-level n)
  (unless (exact-nonnegative-integer? n)
    (error 'at-debug-state "expected non-negative integer ~a" n))
  (>= (debug-level) n))

;; print-label-and-values prints out the label followed the values
;; and the expression that generated those values
;; The label is formated with the file and line number of the
;; debubing expression for easier location.
(define-syntax (print-label-and-values stx)
  (syntax-case stx ()
    [(_ label value ...)
     (let* ([src (syntax-source stx)]
            [src (if (path? src)
                     (find-relative-path (current-directory) src)
                     src)]
            [lno (syntax-line stx)])
       #`(begin
           (printf "~a @ ~a:~a\n" label #,src #,lno)
        (begin
          (printf "~a:\n" 'value)
          (pretty-print value)
          (newline))
        ...
        (newline))
)]))

;; print label followed by values when debug-state is greater than 1.
(define-syntax (debug stx)
  (syntax-case stx ()
    [(_ label value ...)
     #`(when (at-debug-level 1)
         #,(syntax/loc stx
             (print-label-and-values label value ...)))]))

;; print label followed by values when debug-state is greater than 2.
(define-syntax (vomit stx)
  (syntax-case stx ()
    [(_ label value ...)
     #`(when (at-debug-level 2)
         #,(syntax/loc stx
             (print-label-and-values label value ...)))]))


(define-syntax-rule (while condition body ...)
  (let loop ()
    (when condition
      body ...
      (loop))))

(define fix (lambda (f) (lambda (x) ((f (fix f)) x))))

;; This function is like map but the function f returns
;; two values using the ``values'' form. Thus, the result
;; of map2 is two lists.
(define (map2 f ls)
  (cond [(null? ls)
         (values '() '())]
        [else
         (let-values ([(x1 x2) (f (car ls))]
                      [(ls1 ls2) (map2 f (cdr ls))])
           (values (cons x1 ls1) (cons x2 ls2)))]))

;; label-name prepends an underscore to a label (symbol or string)
;; if the current system is Mac OS and leaves it alone otherwise.
;; label-name : (U String Symbol) -> String
(define (label-name name)
  (unless (or (symbol? name) (string? name))
    (error 'label-name "expected string or symbol got ~s" name))
  (cond
    [(symbol? name) (label-name (symbol->string name))]
    [(eqv? (system-type 'os) 'macosx) (string-append "_" name)]
    [else name]))

;; The lookup function takes a key and an association list
;; and returns the corresponding value. It triggers an
;; error if the key is not present in the association list.
;;   
;; The association list may be constructed of either
;; immutable or mutable pairs.
;;
(define no-default (gensym))

(define (lookup x ls [default no-default])
  (let recur ([xs ls])
    (cond
      [(null? xs)
       (if (eq? default no-default)
           (error 'lookup "didn't find ~a in ~a" x ls)
           default)]
      [(pair? xs)
       (define fst (car xs))
       (cond
         [(and (pair?  fst) (equal? x (car  fst))) (cdr  fst)]
         [(and (mpair? fst) (equal? x (mcar fst))) (mcdr fst)]
         [(or (pair? fst) (mpair? fst)) (recur (cdr xs))]
         [else (error 'lookup "expected pair for ~a in ~a" fst ls)])]
      [else (error 'lookup "expected an association list in ~a" ls)])))

(define (read-fixnum)
  (define r (read))
  (cond [(fixnum? r) r]
	[else (error 'read "expected an integer")]))

;; Read an entire .rkt file wrapping the s-expressions in
;; a list whose head is 'program.
(define (read-program path)
  (unless (or (string? path) (path? path))
    (error 'read-program "expected a string in ~s" path))
  (unless (file-exists? path)
    (error 'read-program "file doesn't exist in ~s" path))
  (debug "utilities/read-program" path)
  (define input-prog
    (call-with-input-file path
      (lambda (f)
        `(program . ,(for/list ([e (in-port read f)]) e)))))
  (debug "utilities/read-program" input-prog)
  input-prog)

(define (make-dispatcher mt)
  (lambda (e . rest)
    (match e
       [`(,tag ,args ...)
	(apply (hash-ref mt tag) (append rest args))]
       [else
	(error "no match in dispatcher for " e)]
       )))

;; The check-passes function takes a compiler name (a string) and a description of
;; the passes (see below) and returns a function that takes a test name and
;; runs the passes and the appropriate interpreters to test the
;; correctness of all the passes. This function assumes there is a "tests"
;; subdirectory and a file in that directory whose name is the test name
;; followed by ".rkt". Also, there should be a matching file with the
;; ending ".in" that provides the input for the Scheme program.
;;
;; The description of the passes is a list with one entry per pass.
;; An entry is a list with three things: a string giving the name of
;; the pass, the function that implements the pass (a translator from
;; AST to AST), and a function that implements the interpreter (a
;; function from AST to result value).
;;

(define (check-passes name passes initial-interp)
  (lambda (test-name)
    (debug "** compiler " name)
    (debug "** checking passes for test " test-name)
    (define input-file-name (format "tests/~a.in" test-name))
    (define program-name (format "tests/~a.rkt" test-name))
    (define sexp (read-program program-name))
    (debug "program:" sexp)

    (let loop ([passes passes] [p sexp]
	       [result (if (file-exists? input-file-name)
			   (with-input-from-file input-file-name
			     (lambda () (initial-interp sexp)))
			   (initial-interp sexp))])
      (cond [(null? passes) result]
	    [else
	     (match (car passes)
		[`(,pass-name ,pass ,interp)
		 (debug "running pass" pass-name)
		 (define new-p (pass p))
		 (debug pass-name new-p)
		 (cond [interp
			(let ([new-result
                               ;; if there is an input file with the same name
                               ;; as this test bing current-input-port to that
                               ;; file's input port so that the interpreters
                               ;; can use it as test input.
			       (if (file-exists? input-file-name) 
                                   (with-input-from-file input-file-name
                                     (lambda () (interp new-p)))
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

;; The compile-file function takes a description of the compiler
;; passes (see the comment for check-passes) and returns a function
;; that, given a program file name (a string ending in ".rkt"),
;; applies all of the passes and writes the output to a file whose
;; name is the same as the proram file name but with ".rkt" replaced
;; with ".s".
(define (compile-file passes)
  (lambda (prog-file-name)
    (define file-base (string-trim prog-file-name ".rkt"))
    (define out-file-name (string-append file-base ".s"))
    (call-with-output-file
      out-file-name
      #:exists 'replace
      (lambda (out-file)
        (define sexp (read-program prog-file-name))
        (let ([x86 (let loop ([passes passes] [p sexp])
                     (cond [(null? passes) p]
                           [else
                            (match (car passes)
                              [`(,name ,pass ,interp)
                               (let* ([new-p (pass p)])
                                 (loop (cdr passes) new-p)
                                 )])]))])
          (cond [(string? x86)
                 (write-string x86 out-file)
                 (newline out-file)]
                [else
                 (error "compiler did not produce x86 output")])
          )))))

;; The interp-tests function takes a compiler name (a string)
;; a description of the passes (see the comment for check-passes)
;; a test family name (a string), and a list of test numbers,
;; and runs the compiler passes and the interpreters to check
;; whether the passes correct. 
;; 
;; This function assumes that the subdirectory "tests" has a bunch of
;; Scheme programs whose names all start with the family name,
;; followed by an underscore and then the test number, ending in
;; ".rkt". Also, for each Scheme program there is a file with the
;; same number except that it ends with ".in" that provides the
;; input for the Scheme program.

(define (interp-tests name passes initial-interp test-family test-nums)
  (define checker (check-passes name passes initial-interp))
  (for ([test-number (in-list test-nums)])
    (let ([test-name (format "~a_~a" test-family test-number)])
      (debug "utilities/interp-test" test-name)
      (checker test-name))))

;; The compiler-tests function takes a compiler name (a string) a
;; description of the passes (see the comment for check-passes) a test
;; family name (a string), and a list of test numbers (see the comment
;; for interp-tests), and runs the compiler to generate x86 (a ".s"
;; file) and then runs gcc to generate machine code.  It runs the
;; machine code and stores the result. If the test file has a
;; corresponding .res file, the result is compared against its contents;
;; otherwise, the result is compared against 42.

(define (compiler-tests name passes test-family test-nums)
  (define compiler (compile-file passes))
  (for ([test-number (in-list test-nums)])
    (let ([test-name (format "~a_~a" test-family test-number)])
      (compiler (format "tests/~a.rkt" test-name))
      (unless (system (format "gcc -g -std=c99 runtime.o tests/~a.s" test-name))
        (exit))
      (let* ([input (if (file-exists? (format "tests/~a.in" test-name))
                        (format " < tests/~a.in" test-name)
                        "")]
             [output (if (file-exists? (format "tests/~a.res" test-name))
                         (call-with-input-file (format "tests/~a.res" test-name)
                           (lambda (f) (string->number (read-line f))))
                         42)]
             [progout (process (format "./a.out~a" input))] ; List, first element is stdout
             [result (string->number (read-line (car progout)))])
        (match progout
          [`(,in1 ,out ,_ ,in2 ,_)
           (close-input-port in1)
           (close-input-port in2)
           (close-output-port out)])
        (if (eq? result output)
            (begin (display test-name)(display " ")(flush-output))
            (error (format "test ~a failed, output: ~a" 
                           test-name result)))))
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

;; registers-for-alloc should always inlcude the arg-registers. -Jeremy 
(define registers-for-alloc general-registers)


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

(define (vertices graph)
  (hash-keys graph))

(define (print-dot graph file-name)
  (if (at-debug-level 1)
      (call-with-output-file file-name #:exists 'replace
	(lambda (out-file)
	  (write-string "strict graph {" out-file) (newline out-file)
	  
	  (for ([v (vertices graph)])
	       (write-string (format "~a;\n" v) out-file))
	  
	  (for ([v (vertices graph)])
	       (for ([u (adjacent graph v)])
		    (write-string (format "~a -- ~a;\n" u v) out-file)))
	  
	  (write-string "}" out-file)
	  (newline out-file)))
      '()))
      
