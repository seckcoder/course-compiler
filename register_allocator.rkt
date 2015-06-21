#lang racket
(require racket/set)
(require "utilities.rkt")

(define caller-save (set 'rdx 'rcx 'rsi 'rdi 'r8 'r9 'r12))

(define registers (set 'rbx 'rcx 'rdx 'rsi 'rdi
		       'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Liveness Analysis
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; record live-after in each instruction

(define free-vars
  (lambda (a)
    (match a
       [`(var ,x) (set x)]
       [else (set)])))

(define read-vars
  (lambda (instr)
    (match instr
       [`(mov ,s ,d) (free-vars s)]
       [(or `(add ,s ,d) `(sub ,s ,d)) 
	(set-union (free-vars s) (free-vars d))]
       [`(neg ,d) (free-vars d)]
       [`(call ,f) (set)]
       )))

(define write-vars
  (lambda (instr)
    (match instr
       [`(mov ,s ,d) (free-vars d)]
       [(or `(add ,s ,d) `(sub ,s ,d)) (free-vars d)]
       [`(neg ,d) (free-vars d)]
       [`(call ,f) caller-save]
       )))

(define (liveness-analysis ast)
  (match ast
     [`(program ,xs ,ss)
      (let loop ([ss (reverse ss)] [live-after (set)] [new-ss '()])
	(cond [(null? ss)
	       `(program ,xs ,new-ss)]
	      [else
	       (let* ([s (car ss)]
		      [live-before (set-union (set-subtract live-after
							    (write-vars s))
					      (read-vars s))])
		 (loop (cdr ss)
		       live-before
		       (cons (cons s live-after) new-ss)))]))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Build Interference Graph
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (make-graph)
  (hash))

(define (add-edge graph u v)
  (hash-set! graph u (set-add v (hash-ref graph u (set))))
  (hash-set! graph v (set-add u (hash-ref graph v (set)))))

(define (build-interference ast)
  (match ast
    [(program ,xs ,ss-lv)
     (let ([graph (make-graph)])
       (let loop ([ss-lv (reverse ss-lv)] [ss '()])
	 (cond [(null? ss-lv)
		`(program ,xs ,graph ,ss)]
	       [else
		(match (car ss-lv)
		   [`((mov ,s ,d) . ,live-after)
		    ;; d interferes with everything in live-after
		    ;;   except s and d
		    (for ([v live-after]
			  #:when (not (or (eq? v s) (eq? v d))))
			 (add-edge graph d v))
		    (loop (cdr ss-lv) 
			  (cons `(mov ,s ,d) ss))]
		   [`(,inst . ,live-after)
		    (for ([v live-after])
			 (for ([d (write-vars inst)]
			       #when (not (eq? v d)))
			      (add-edge graph d v)))
		    (loop (cdr ss-lv)
			  (cons inst ss))]
		   )])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Allocate Registers and Stack Locations (Graph Coloring) 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (allocate-registers ast)
  (match ast
     [`(program ,xs ,graph ,ss)
      
      
      ]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Insert Spill Code and Remove Trivial Moves
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
