#lang eopl

(require test-engine/racket-tests)

; ; Below is the implementation of the LETREC language implemented
; ; in class extended with true and false expressions.
; ; 
; ; As you may have already realized, adding expressions to a programming
; ; language requires a great deal more than adding rules to the grammar.
; ; It also requires that the impementation of the language (e.g., value-of,
; ; value-of program, etc.) be changed. This is an undesirable feature,
; ; because it may lead to constantly making changes to make the language
; ; more palatable for programmers and it may lead to bugs in the
; ; implementation of the language.
; ; 
; ; For this reason, programming languages implementators strive to implement
; ; new grammatical features in terms of existing grammatical features. This
; ; process in called desugaring. In essence, desugaring translates some
; ; expression into other expressions to avoid having to change the language
; ; implementation. For example, adding cond-expressions to the LETREC
; ; language can be done without changing value-of program and value-of if
; ; we desugar them. Here is an example:
; ; 
; ; (desugar-expr cond zero?(x) ==> 9
; ;                   zero?(-(x, 1)) ==> 0
; ;                   true 10)
; ;                   
; ;                    
; ; =
; ; if zero?(x) then 9 else if zero?(-(x, 1)) then 0 else 10
; ; 
; ; As you can see, by desugaring we can add cond-expressions to the LETREC
; ; language without changing value-of, because evaluating a cond-expression
; ; is the same as evaluating an if-expression.
; ; 
; ; This exam askes you to write a desugaring function for the following
; ; new expressions:
; ;  1. cond-expression
; ;  2. or-expression
; ;  3. and-expression
; ;  4. add-expression
; ; 
; ; The grammar for these expressions is as follows:
; ; 
; ; expression --> +(expression, expression)
; ;            --> cond (expresion ==> expression)* end
; ;            -->  and (expression {, expression}*)
; ;            -->   or (expression {, expression}*)
; ; 
; ; You need to add these expressions to the grammar, but such expressions
; ; should never be evaluated given that they are to always be desugared.
; ; 
; ; Update value-of-program to be:
; ; 
; ; ;; value-of-program : Program -> ExpVal
; ; (define (value-of-program pgm)
; ;   (cases program pgm
; ;     (a-program (exp1)
; ;                (value-of (desugar-expr exp1) (init-env)))))
; ; 
; ; The function desugar-expr is the function that you need to write. It needs
; ; to translate the expressions listed above to existing expressions in the
; ; LETREC language.
; ;                      
; 



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
     ("letrec" identifier "(" identifier ")" "=" expression 
               "in" expression) letrec-exp)
    
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    
    (expression ("(" expression expression ")") call-exp)

    (expression ("true") true-exp)

    (expression ("false") false-exp)

    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    
    (expression ("+" "(" expression "," expression ")") add-exp)

    (expression ("and" "(" expression (arbno "," expression) ")") and-exp)

    (expression ("or" "(" expression (arbno "," expression) ")") or-exp)
    
    ))

;; desugar-expr: exp -> exp
;; Purpose: to implement new grammatical features in terms of existing grammatical features
(define (desugar-expr exp)
  (cases expression exp
    (diff-exp (exp1 exp2) (diff-exp (desugar-expr exp1) (desugar-expr exp2)))
    (zero?-exp (exp1) (zero?-exp (desugar-expr exp1)))
    (if-exp (exp1 exp2 exp3) (if-exp (desugar-expr exp1) (desugar-expr exp2) (desugar-expr exp3)))
    (let-exp (var exp1 exp2) (let-exp var (desugar-expr exp1) (desugar-expr exp2)))
    (letrec-exp (var1 var2 exp1 exp2) (letrec-exp var1 var2 (desugar-expr exp1) (desugar-expr exp2)))
    (proc-exp (var exp1) (proc-exp var (desugar-expr exp1)))
    (call-exp (exp1 exp2) (call-exp (desugar-expr exp1) (desugar-expr exp2)))
    (cond-exp (exp1 exp2) (desugar-expr (cond-auxilary exp1 exp2)))
    (add-exp (exp1 exp2) (diff-exp (desugar-expr exp1) (diff-exp (const-exp 0) (desugar-expr exp2))))
    (and-exp (exp1 exp2) (desugar-expr (and-auxilary exp1 exp2)))
    (or-exp (exp1 exp2) (desugar-expr (or-auxilary exp1 exp2)))
    (else exp)))

;; cond-auxilary: exp, exp -> exp
;; Purpose: auxilary function to desugar cond-exp
; (desugar-expr cond zero?(x) ==> 9
;                   zero?(-(x, 1)) ==> 0
;                   true 10)
; 
; =
; 
; if zero?(x) then 9 else if zero?(-(x, 1)) then 0 else 10

(define (cond-auxilary exp1 exp2)
  (if (null? (cddr exp1)) (if-exp (car exp1) (car exp2) (cadr exp2))
      (if-exp (car exp1) (car exp2) (cond-auxilary (cdr exp1) (cdr exp2)))))

;; and-auxilary: exp, exp -> exp
;; Purpose: auxilary function to desugar and-exp
;; only true if both are true
(define (and-auxilary exp1 exp2)
  (if (null? exp2) (if-exp exp1 (true-exp) (false-exp))
      (if-exp exp1 (and-auxilary (car exp2) (cdr exp2)) (false-exp))))

;; or-auxilary: exp, exp -> exp
;; Purpose: auxilary function to desugar or-exp
;; only false if both are false
(define (or-auxilary exp1 exp2)
  (if (null? exp2) (if-exp exp1 (true-exp) (false-exp))
      (if-exp exp1 (true-exp) (or-auxilary (car exp2) (cdr exp2)))))


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
   (id symbol?)
   (bvar symbol?)
   (body expression?)
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
                      (if (eqv? search-sym p-name)
                          (proc-val (procedure b-var p-body env))          
                          (apply-env saved-env search-sym)))))



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
   (proc proc?)))

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

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (env environment?)))


;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of (desugar-expr exp1) (init-env)))))

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
                    (arg (value-of rand env)))
                (apply-procedure proc arg)))

    (true-exp () (bool-val #t))

    (false-exp () (bool-val #f))

    (else (eopl:error "You are evaluating an invalid expression somewhere!"))
    
    ))

;; apply-procedure : Proc * ExpVal -> ExpVal
(define (apply-procedure proc1 val)
  (cases proc proc1
    (procedure (var body saved-env)
               (value-of body (extend-env var val saved-env)))))

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


(check-expect (eval "cond zero?(x) ==> 9
                          zero?(-(x, 1)) ==> 0
                          true ==> 10
                          end") (num-val 10))

(check-expect (eval "cond zero?(x) ==> 9
                          zero?(+(x, 1)) ==> 0
                          true ==> 10
                          end") (num-val 10))

(check-expect (eval "+(3, 3)") (num-val 6))
(check-expect (eval "-(+(1,2), +(3, 4))") (num-val -4))

(check-expect (eval "if zero?(+(x, x)) then x else 2") (num-val 2))

(check-expect (eval "and(true, true)") (bool-val #t))
(check-expect (eval "and(true, false)") (bool-val #f))
(check-expect (eval "and(true, and(true, true))") (bool-val #t))

(check-expect (eval "or(true, true)") (bool-val #t))
(check-expect (eval "or(true, false)") (bool-val #t))
(check-expect (eval "or(false, false)") (bool-val #f))
(check-expect (eval "or(true, or(true, true))") (bool-val #t))

(check-expect (eval "let sum = proc (x) proc (y) -(x, -(0, y))
                               in letrec sigma (n) = if zero?(n)
                               then 0
                               else ((sum n) (sigma -(n, 1)))
                               in (sigma 5)") (num-val 15))

(check-expect (eval "let sum = proc (x) proc (y) +(x, +(0, y))
                               in letrec sigma (n) = if zero?(n)
                               then 0
                               else ((sum n) (sigma -(n, 1)))
                               in (sigma 5)") (num-val 15))

(test)
