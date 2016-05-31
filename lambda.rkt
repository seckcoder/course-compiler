#lang racket
(require racket/set)
(require "utilities.rkt")
(require "functions.rkt")
(require "interp.rkt")
(provide compile-R4 lambda-passes lambda-typechecker)

(define compile-R4
  (class compile-R3
    (super-new)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; type-check : env -> S4 -> S4
    
    (define/override (type-check env)
      (lambda (e)
        (match e
          [`(lambda: ,(and bnd `([,xs : ,Ts] ...)) : ,rT ,body)
           (define-values (new-body bodyT) 
	     ((type-check (append (map cons xs Ts) env)) body))
	   (define ty `(,@Ts -> ,rT))
	   (cond
	    [(equal? rT bodyT)
	     (values `(has-type (lambda: ,bnd : ,rT ,new-body) ,ty) ty)]
	    [else
	     (error "function body's type does not match return type" bodyT rT)])]
          [else ((super type-check env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uniquify : env -> S0 -> S0
    (define/override (uniquify env)
      (lambda (e)
	(match e
          [`(lambda: ([,xs : ,Ts] ...) : ,rT ,body)
	   (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
	   (define new-env (append (map cons xs new-xs) env))
           (define (annotate x t) `[,x : ,t])
           `(lambda: ,(map annotate new-xs Ts) : ,rT 
                     ,((uniquify new-env) body))]
	  [else ((super uniquify env) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; reveal-functions
    (define/override (reveal-functions funs)
      (lambda (e)
	(define recur (reveal-functions funs))
	(match e
          [`(lambda: ,params : ,rT ,body)
           `(lambda: ,params : ,rT ,(recur body))]
          [else ((super reveal-functions funs) e)])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; convert-to-closures : env -> S4 -> S3

    ;; The returned hash table maps variable x to (has-type x t). -Jeremy

    ;; free-variable : expr -> (immutable-hash id expr)
    (define/public (free-variables e)
      (define (recur e) (free-variables e))
      (match e
        [`(has-type ,x? ,t)
         (if (symbol? x?)
             (hash x? e)
             (recur x?))]	
        [(or (? integer?) (? boolean?)) (hash)]
        [`(function-ref ,f) (hash)]
        [`(let ([,x ,e]) ,body)
	 (hash-union (recur e) (hash-remove (recur body) x))]
        [`(if ,cnd ,thn, els)
         (hash-union (recur cnd) (recur thn) (recur els))]
	[`(lambda: ([,xs : ,Ts] ...) : ,rT ,body)
         (define (rm x h) (hash-remove h x))
         (foldl rm (recur body) xs)]
	[`(app ,es ...)
	 (apply hash-union (map recur es))]
	[`(,op ,es ...)
	 (apply hash-union (map recur es))]
        [else (error 'free-variables "unmatched ~a" e)]))

    (define (convert-fun-body fvs-id free-vars body rt)
      (let loop ([xs free-vars] [i 1])
        (match xs
          ['() body]
          [`((has-type ,x ,t) . ,xs^)
           `(has-type
             (let ([,x (has-type (vector-ref (has-type ,fvs-id _)
                                             (has-type ,i Integer))
                                 ,t)])
               ,(loop xs^ (add1 i)))
             ,rt)]
          [else (error 'convert-fun-body "unmatched ~a" xs)])))

    (define/public (convert-to-closures)
      (lambda (e)
        (define (recur e) ((convert-to-closures) e))
        (match e
          [`(has-type (app ,e ,es ...) ,t)
           (define-values (new-e e-fs) (recur e))
           (define tmp (gensym 'app))
           (define-values (new-es es-fss) (map2 recur es))
           (match new-e
             [`(has-type ,e^ ,t^)
              (values
               `(has-type
                 (let ([,tmp ,new-e])
                   (has-type (app (has-type (vector-ref (has-type ,tmp ,t^) 
							(has-type 0 Integer)) _)
                                  (has-type ,tmp ,t^) ,@new-es) ,t))
                 ,t)
               (append e-fs (apply append es-fss)))]
             [else (error 'convert-to-closures
			  (format "I assume this shouldn't happen ~a" new-e))])]
          [`(has-type (lambda: ([,xs : ,Ts] ...) : ,rT ,body) ,t)
           (define-values (new-body body-fs) (recur body))
           (let* ([fun-name (gensym 'lambda)]
                  [params (map (lambda (x T) `[,x : ,T]) xs Ts)]
                  [ty      `(,@Ts ... -> ,rT)]
                  [rm (lambda (x h) (hash-remove h x))]
                  [fvs-table (hash->list (foldl rm (free-variables new-body) xs))]
                  [fvs-expr  (map cdr fvs-table)]                  
                  [fvT       (map caddr fvs-expr)]
                  [fvs-tmp   (gensym 'fvs)])
	     (debug "fvs: " (map car fvs-table))
             (values
              `(has-type (vector (has-type (function-ref ,fun-name) _) ,@fvs-expr)
                         (Vector _ ,@fvT))
              ;; create closure
              (cons `(define (,fun-name ,@(cons `[,fvs-tmp : _] params)) : ,rT
                       ,(convert-fun-body fvs-tmp fvs-expr new-body rT))
                    body-fs)))]
          [`(has-type (function-ref ,f) ,t)
           (values `(has-type (vector (has-type (function-ref ,f) _)) (Vector _)) '())]
          [`(has-type ,e ,t)
           (let-values ([(e b*) (recur e)])
             (values `(has-type ,e ,t) b*))]
          [(or (? symbol?) (? integer?) (? boolean?))
           (values e '())]
          [`(let ([,x ,e]) ,body)
           (define-values (new-e e-fs) (recur e))
           (define-values (new-body body-fs) (recur body))
           (values `(let ([,x ,new-e]) ,new-body)
                   (append e-fs body-fs))]
          [`(if ,cnd ,thn, els)
           (define-values (new-cnd cnd-fs) (recur cnd))
           (define-values (new-thn thn-fs) (recur thn))
           (define-values (new-els els-fs) (recur els))
           (values `(if ,new-cnd ,new-thn ,new-els)
                   (append cnd-fs thn-fs els-fs))]
          [`(define (,f [,xs : ,Ts] ...) : ,rt ,body)
           (define-values (new-body body-fs) (recur body))
           (define fvs-tmp (gensym 'fvs))
           (let ([params (map (lambda (x T) `[,x : ,T]) xs Ts)])
             (cons
              `(define (,f ,@(cons `[,fvs-tmp : _] params)) : ,rt 
                 ,(convert-fun-body fvs-tmp '() new-body rt))
              body-fs))]
          [`(program (type ,ty) ,ds ... ,body)
           (let-values ([(dss) (map recur ds)]
                        [(body body-fs) (recur body)])
             `(program (type ,ty)
                       ,@(append* dss)
                       ,@body-fs
                       ,body))]
          ;; Keep the below case last -Jeremy
          [`(,op ,(app recur new-es es-fss) ...)
           (values `(,op ,@new-es) (append* es-fss))])))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-call-live-roots

    (define/override (root-type? x)
      (or (and (list? x) (set-member? x '->))
          (super root-type? x)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passes
(define lambda-typechecker
  (let ([compiler (new compile-R4)])
    (send compiler type-check '())))
(define lambda-passes
  (let ([compiler (new compile-R4)]
        [interp (new interp-R4)])
    `(
      ;("type-check" ,(send compiler type-check '())
      ; ,(send interp interp-scheme '()))
      ("uniquify" ,(send compiler uniquify '())
       ,(send interp interp-scheme '()))
      ("reveal-functions" ,(send compiler reveal-functions '())
       ,(send interp interp-F '()))
      ("convert-to-closures" ,(send compiler convert-to-closures)
       ,(send interp interp-F '()))
      ("expose allocation"
       ,(send compiler expose-allocation)
       ,(send interp interp-F '()))
      ("flatten" ,(send compiler flatten #f)
       ,(send interp interp-C '()))
      ("instruction selection" ,(send compiler select-instructions)
       ,(send interp interp-x86 '()))
      ("liveness analysis" ,(send compiler uncover-live (void))
       ,(send interp interp-x86 '()))
      ("build interference" ,(send compiler build-interference
                                   (void) (void))
       ,(send interp interp-x86 '()))
      ("build move graph" ,(send compiler
                                 build-move-graph (void))
       ,(send interp interp-x86 '()))
      ("allocate registers" ,(send compiler allocate-registers)
       ,(send interp interp-x86 '()))
      ("lower conditionals" ,(send compiler lower-conditionals)
       ,(send interp interp-x86 '()))
      ("patch instructions" ,(send compiler patch-instructions)
       ,(send interp interp-x86 '()))
      ("print x86" ,(send compiler print-x86) #f)
      )))
    
    
    
