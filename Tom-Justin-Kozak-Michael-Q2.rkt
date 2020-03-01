;; Justin Tom & Michael Kozak

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
    
    (expression ("-" "(" expression "," expression ")") diff-exp)
    
    (expression ("zero?" "(" expression ")") zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression) if-exp)
    
    (expression (identifier) var-exp)
    
    (expression 
     ("let" identifier "=" expression "in" expression) let-exp)

    (expression
     ("minus" "(" expression ")") minus-exp)

    (expression ("+" "(" expression "," expression ")") addition-exp)

    (expression ("*" "(" expression "," expression ")") multiplication-exp)

    (expression ("/" "(" expression "," expression ")") quotient-exp)

    (expression ("modulo" "(" expression "," expression ")") modulo-exp)

    (expression ("equal?" "(" expression "," expression ")") equal?-exp)

    (expression ("greater?" "(" expression "," expression ")") greater?-exp)

    (expression ("less?" "(" expression "," expression ")") less?-exp)
    
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

;; example of a data type built without using define-datatype

(define (empty-env-record) '())

(define (extended-env-record sym val old-env)
    (cons (list sym val) old-env))

(define empty-env-record? null?)

(define (environment? x)
    (or (empty-env-record? x)
        (and (pair? x)
             (symbol? (car (car x)))
             (expval? (cadr (car x)))
             (environment? (cdr x)))))

(define (extended-env-record->sym r) (car (car r)))

(define (extended-env-record->val r) (cadr (car r)))

(define (extended-env-record->old-env r) (cdr r))

;; end of example of a data type built without define-datatype

;;;;; Implementation of environment interface
(define empty-env
  (lambda ()
    (empty-env-record)))

(define empty-env? 
  (lambda (x)
    (empty-env-record? x)))

(define extend-env
  (lambda (sym val old-env)
    (extended-env-record sym val old-env)))

(define apply-env
  (lambda (env search-sym)
    (if (empty-env? env)
        (eopl:error 'apply-env "No binding for ~s" search-sym)
        (let ((sym (extended-env-record->sym env))
              (val (extended-env-record->val env))
              (old-env (extended-env-record->old-env env)))
          (if (eqv? search-sym sym)
              val
              (apply-env old-env search-sym))))))

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
   (boolean boolean?)))

;;; observers:

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

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-observers "Looking for a ~s, found ~s"
                variant value)))

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
    
    ))

;;;;;;   EVALUATION WRAPPERS

;; eval : String -> ExpVal
(define (eval string)
  (value-of-program (scan&parse string)))

;;;;; EXAMPLES OF EVALUATION

; (eval "if zero?(1) then 1 else 2")
; (eval "-(x, v)")
; (eval "if zero?(-(x, x)) then x else 2")
; (eval "if zero?(-(x, v)) then x else 2")
; (eval "let x = 2 in -(x, 2)")
; (eval "minus(x)")
; (eval "+(x, v)")
; (eval "*(x, v)")
; (eval "/(x, v)")
; (eval "modulo(x, v)")
; (eval "equal?(x, v)")
; (eval "greater?(x, v)")
; (eval "less?(x, v)")

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


(test)