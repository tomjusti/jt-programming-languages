#lang eopl
(require test-engine/racket-tests)

;; 2.1

(define zero 0)

(define (succ n) (+ n 1))

(define isZero? zero?)

(define (pred n) (- n 1))

(define (nnint->decimal n) n)

(define plus
  (lambda (x y)
    (if (isZero? x) y (succ (plus (pred x) y)))))

(define multiply
  (lambda (x y)
    (if (isZero? y) zero
        (plus x (multiply x (pred y))))))

(define (factorial n)
  (if (eqv? (nnint->decimal n) 0) (succ (nnint->decimal n))
      (multiply (nnint->decimal n) (factorial (pred (nnint->decimal n))))))

;; 2.4

;; everything is an observer except push

;; 2.7

(define empty-env
  (lambda () (list 'empty-env)))

(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))

(define apply-env
  (lambda (env search-var)
    (cond
      ((eqv? (car env) 'empty-env)
       (report-no-binding-found search-var))
      ((eqv? (car env) 'extend-env)
       (let ((saved-var (cadr env))
             (saved-val (caddr env))
             (saved-env (cadddr env)))
         (if (eqv? search-var saved-var)
             saved-val
             (apply-env saved-env search-var))))
      (else
       (report-invalid-env env)))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define (empty-env? env)
  (null? env))

(define has-binding?
  (lambda (env var)
    (if (empty-env? env) #f
        (if (eqv? (car env) var) #t
            (has-binding? (cdr env) var)))))

(define e (extend-env 'x 2 (extend-env 'y 1 (empty-env))))

;; 2.12

(define empty-stack '())

(define empty-stack? null?)

(define push
  (lambda (val stack)
    (cons val stack)))

(define top
  (lambda (stack)
    (car stack)))

(define pop
  (lambda (stack)
    (cdr stack)))