#lang racket
(require "conditionals.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide compile-opt-R1 optimize-control-passes)

(define challenge #t)

(define compile-opt-R1
  (class compile-R1
    (super-new)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; basic-blocks : psuedo-x86 -> x86
    
    (define/public (basic-blocks-stms es)
      )

    (define/public (basic-blocks)
      (lambda (e)
	(match e
	   [`(if ,cnd ,thn-ss ,els-ss)
	  
	    ]
	   )))

    (define/public (basic-blocks-cnd true-label false-label)
      (lambda (e)
	(match e
	   []
	   )))
    
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; optimize-jumps

    ;; UNDER CONSTRUCTION

    
    ));; compile-opt-R1

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define optimize-control-passes
  (let ([compiler (new compile-opt-R1)]
	[interp (new interp-R1)])
    `(("type-check" ,(send compiler type-check '())
       ,(send interp interp-scheme '()))
      ("uniquify" ,(send compiler uniquify '())
       ,(send interp interp-scheme '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler build-interference
                                   (void) (void))
       ,(send interp interp-x86 '()))
      ("allocate registers" ,(send compiler allocate-registers)
       ,(send interp interp-x86 '()))
      ("patch instructions" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ;; expose-basic-blocks
      ("print x86" ,(send compiler print-x86) #f)
      )))
