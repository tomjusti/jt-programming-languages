#lang eopl
(require test-engine/racket-tests)

;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    
    (comment ("%" (arbno (not #\newline))) skip)
    
    (identifier
     (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    
    (number (digit (arbno digit)) number)
    
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)
    
    (expression("-" "(" expression "," expression ")")diff-exp)
    
    (expression ("zero?" "(" expression ")") zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression) if-exp)
    
    (expression (identifier) var-exp)
    
    (expression 
     ("let" identifier "=" expression "in" expression) let-exp)
    
    (expression
     ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
               "in" expression) letrec-exp)
    
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    
    (expression ("(" expression (arbno expression) ")") call-exp)

    (expression
     ("minus" "(" expression ")") minus-exp)

    (expression ("+" "(" expression "," expression ")") addition-exp)

    (expression ("*" "(" expression "," expression ")") multiplication-exp)

    (expression ("/" "(" expression "," expression ")") quotient-exp)

    (expression ("modulo" "(" expression "," expression ")") modulo-exp)

    (expression ("equal?" "(" expression "," expression ")") equal?-exp)

    (expression ("greater?" "(" expression "," expression ")") greater?-exp)

    (expression ("less?" "(" expression "," expression ")") less?-exp)

    (expression ("emptylist") emptylist-exp)
    
    (expression ("cons" "(" expression "," expression ")") cons-exp)

    (expression ("car" "(" expression ")") car-exp)

    (expression ("cdr" "(" expression ")") cdr-exp)

    (expression ("null?" "(" expression ")") null?-exp)

    (expression ("list" "(" (arbno expression) ")") list-exp)
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;    ENVIRONMENT

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval expval?)
   (saved-env environment?))
  (extend-env-rec
   (id (list-of symbol?))
   (bvar (list-of (list-of symbol?)))
   (body (list-of expression?))
   (saved-env environment?)))

(define (apply-env env search-sym)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "No binding for ~s" search-sym))
      (extend-env (var val saved-env)
                  (if (eqv? search-sym var)
                      val
                      (apply-env saved-env search-sym)))
      (extend-env-rec (p-name b-var p-body saved-env)
                      (extend-env-rec-aux p-name b-var p-body saved-env search-sym env))))

(define (extend-env-rec-aux p-name b-var p-body saved-env search-sym env)
  (if (null? p-body) (apply-env saved-env search-sym)
      (if (eqv? search-sym (car p-name))
          (proc-val (procedure (car b-var) (car p-body) env))
          (extend-env-rec-aux (cdr p-name) (cdr b-var) (cdr p-body) saved-env search-sym env))))

(define (init-env)
  (extend-env 
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10)
     (empty-env)))))

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val 
   (proc proc?))
  (list-val
   (list list?)))

;;; extractors:

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

;; expval->list : ExpVal -> List
(define expval->list
  (lambda (v)
    (cases expval v
      (list-val (list) list)
      (else (expval-extractor-error 'list v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (var (list-of symbol?))
   (body expression?)
   (env environment?)))


;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-env)))))

;; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    
    (const-exp (num) (num-val num))
    
    (var-exp (var) (apply-env env var))
    
    (diff-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val2)))
                  (num-val (- num1 num2)))))
    
    (zero?-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (let ((num1 (expval->num val1)))
                   (if (zero? num1)
                       (bool-val #t)
                       (bool-val #f)))))
    
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval->bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))
    
    (let-exp (var exp1 body)       
             (let ((val1 (value-of exp1 env)))
               (value-of body
                         (extend-env var val1 env))))
    
    (letrec-exp (p-name param p-body letrec-body)
                (value-of letrec-body (extend-env-rec p-name
                                                      param
                                                      p-body
                                                      env)))
    
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    
    (call-exp (rator rand)
              (let ((proc (expval->proc (value-of rator env)))
                    (arg (map (lambda (rand_) (value-of rand_ env)) rand)))
                (apply-procedure proc arg)))

    (minus-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (let ((num1 (expval->num val1)))
                   (num-val (* num1 -1)))))

    (addition-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (num-val (+ num1 num2)))))

    (multiplication-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (num-val (* num1 num2)))))


    (quotient-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (num-val (quotient num1 num2)))))

    (modulo-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                   (let ((num1 (expval->num val1))
                         (num2 (expval->num val2)))
                     (num-val (modulo num1 num2)))))

    (equal?-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                   (let ((num1 (expval->num val1))
                         (num2 (expval->num val2)))
                     (bool-val (= num1 num2)))))

    (greater?-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                       (val2 (value-of exp2 env)))
                   (let ((num1 (expval->num val1))
                         (num2 (expval->num val2)))
                     (bool-val (> num1 num2)))))

    (less?-exp (exp1 exp2)
               (let ((val1 (value-of exp1 env))
                     (val2 (value-of exp2 env)))
                 (let ((num1 (expval->num val1))
                       (num2 (expval->num val2)))
                   (bool-val (< num1 num2)))))

    (emptylist-exp () (list-val '()))
    
    (cons-exp (exp1 exp2)
              (let ((val1 (value-of exp1 env))
                    (val2 (value-of exp2 env)))
                (let ((lst (expval->list val2)))
                  (list-val (cons val1 lst)))))

    (car-exp (exp1)
             (let ((val1 (value-of exp1 env)))
               (let ((lst (expval->list val1)))
                 (car lst))))

    (cdr-exp (exp1)
             (let ((val1 (value-of exp1 env)))
               (let ((lst (expval->list val1)))
                 (list-val (cdr lst)))))

    (null?-exp (exp1)
               (let ((val1 (value-of exp1 env)))
                 (let ((lst (expval->list val1)))
                   (bool-val (null? lst)))))

    (list-exp (exp1)
              (let ((val1 (map (lambda (x) (value-of x env)) exp1)))
                (list-val val1)))
    
    ))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define (apply-procedure proc1 val)
  (cases proc proc1
    (procedure (var body saved-env)
               (apply-procedure-aux var body saved-env proc1 val))))

(define (apply-procedure-aux var body saved-env proc1 val)
  (if (null? var) (value-of body saved-env)
      (apply-procedure-aux (cdr var) body (extend-env (car var) (car val) saved-env) proc1 (cdr val))))

;;;;;;   EVALUATION WRAPPERS

;; parse: String -> a-program
(define (parse p) (scan&parse p))

;; eval : String -> ExpVal
(define (eval string)
  (value-of-program (parse string)))

;;;;; EXAMPLES OF EVALUATION

; 
; (eval "if zero?(1) then 1 else 2")
; (eval "-(x, v)")
; (eval "if zero?(-(x, x)) then x else 2")
; (eval "if zero?(-(x, v)) then x else 2")
; (eval "let decr = proc (a) -(a, 1) in (decr 30)")
; (eval "( proc (g) (g 30) proc (y) -(y, 1))")
; (eval "let x = 200 
;          in let f = proc (z) -(z, x) 
;               in let x = 100 
;                    in let g = proc (z) -(z, x) 
;                         in -((f 1), (g 1))")
; 
; (eval "let sum = proc (x) proc (y) -(x, -(0, y)) in ((sum 3) 4)")
; 
; (eval "let x = 200 
;          in let f = proc (z) -(z, x) 
;               in let x = 100 
;                    in let g = proc (z) -(z, x) 
;                         in -((f 1), (g 1))")
; (eval "let sum = proc (x) proc (y) -(x, -(0, y))
;        in letrec sigma (n) = if zero?(n)
;                              then 0
;                              else ((sum n) (sigma -(n, 1)))
;           in (sigma 5)")
; 
; ; needs times
; (eval "letrec fact(n) = if zero?(n) then 1 else *(n, (fact -(n, 1)))
;        in (fact 5)")
; 
; 


(check-expect (eval "letrec even(x) = if zero?(x) then 1 else (odd -(x, 1))
                            odd(x) = if zero?(x) then 0 else (even -(x, 1))
                    in (odd 13)") (num-val 1))

(check-expect (eval "letrec even(x, y, z) = if zero?(x) then y else (odd -(x, 1) y z)
                            odd(x, y, z) = if zero?(x) then z else (even -(x, 1) y z)
                     in (odd 1 2 3)")
              (num-val 2))

(check-expect (eval "if zero?(1) then 1 else 2")
              (num-val 2))
(check-expect (eval "-(x, v)")
              (num-val 5))
(check-expect (eval "if zero?(-(x, x)) then x else 2")
              (num-val 10))
(check-expect (eval "if zero?(-(x, v)) then x else 2")
              (num-val 2))
(check-expect (eval "let x = 2 in -(x, 2)")
              (num-val 0))
(check-expect (eval "minus(x)")
              (num-val -10))
(check-expect (eval "+(x, v)")
              (num-val 15))
(check-expect (eval "*(x, v)")
              (num-val 50))
(check-expect (eval "/(x, v)")
              (num-val 2))
(check-expect (eval "modulo(x, v)")
              (num-val 0))
(check-expect (eval "equal?(x, v)")
              (bool-val #f))
(check-expect (eval "greater?(x, v)")
              (bool-val #t))
(check-expect (eval "less?(x, v)")
              (bool-val #f))
(check-expect (eval "cons(x, emptylist)")
              (list-val (list (num-val 10))))
(check-expect (eval "cons(v, emptylist)")
              (list-val (list (num-val 5))))
(check-expect (eval "cons(x, emptylist)")
              (list-val (list (num-val 10))))
(check-expect (eval "car(cons(x, emptylist))")
              (num-val 10))
(check-expect (eval "cdr(cons(x, emptylist))")
              (list-val '()))
(check-expect (eval "null?(emptylist)")
              (bool-val #t))
(check-expect (eval "null?(cons(x, emptylist))")
              (bool-val #f))
(check-expect (eval "list(x v)")
              (list-val (list (num-val 10) (num-val 5))))
(check-expect (eval "list(x)")
              (list-val (list (num-val 10))))

(test)