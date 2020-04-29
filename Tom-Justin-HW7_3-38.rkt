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
    
    (expression ("if" expression "then" expression "else" expression) if-exp)
    
    (expression (identifier) var-exp)
    
    (expression ("let" identifier "=" expression "in" expression) let-exp)   
    
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    
    (expression ("(" expression expression ")") call-exp)
    
    (expression ("%nameless-var" number) nameless-var-exp)
    
    (expression ("%let" expression "in" expression) nameless-let-exp)
    
    (expression ("%lexproc" expression) nameless-proc-exp)

    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp) ;; Exercise 3.38
    
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define (show-the-datatypes) 
  (sllgen:list-define-datatypes the-lexical-spec the-grammar))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))


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
(define (expval->num v)
  (cases expval v
    (num-val (num) num)
    (else (expval-extractor-error 'num v))))

;; expval->bool : ExpVal -> Bool
(define (expval->bool v)
  (cases expval v
    (bool-val (bool) bool)
    (else (expval-extractor-error 'bool v))))

;; expval->proc : ExpVal -> Proc
(define (expval->proc v)
  (cases expval v
    (proc-val (proc) proc)
    (else (expval-extractor-error 'proc v))))

(define (expval-extractor-error variant value)
  (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
              variant value))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

;; proc? : SchemeVal -> Bool
;; procedure : Exp * Nameless-env -> Proc
(define-datatype proc proc?
  (procedure
   ;; in LEXADDR, bound variables are replaced by %nameless-vars, so
   ;; there is no need to declare bound variables.
   ;; (bvar symbol?)
   (body expression?)
   ;; and the closure contains a nameless environment
   (env nameless-environment?)))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

;; nameless-environment? : SchemeVal -> Bool
(define (nameless-environment? x) ((list-of expval?) x))

;; empty-nameless-env : () -> Nameless-env
(define (empty-nameless-env) '())

;; empty-nameless-env? : Nameless-env -> Bool
(define (empty-nameless-env? x) (null? x))

;; extend-nameless-env : ExpVal * Nameless-env -> Nameless-env
(define (extend-nameless-env val nameless-env) (cons val nameless-env))

;; apply-nameless-env : Nameless-env * Lexaddr -> ExpVal
(define (apply-nameless-env nameless-env n) (list-ref nameless-env n))

(define (init-nameless-env)
      (extend-nameless-env 
       (num-val 1)			; was i
       (extend-nameless-env
        (num-val 5)			; was v
        (extend-nameless-env
         (num-val 10)			; was x
         (empty-nameless-env)))))


;;;;;;;;;;;;;;;; lexical address calculator ;;;;;;;;;;;;;;;;

;; translation-of-program : Program -> Nameless-program
(define (translation-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (a-program                    
                (translation-of exp1 (init-senv))))))

;; translation-of : Exp * Senv -> Nameless-exp
(define (translation-of exp senv)
  (cases expression exp
    
    (const-exp (num) exp)
    
    (diff-exp (exp1 exp2)
              (diff-exp
               (translation-of exp1 senv)
               (translation-of exp2 senv)))

    (zero?-exp (exp1)
               (zero?-exp
                (translation-of exp1 senv)))

    (if-exp (exp1 exp2 exp3)
            (if-exp
             (translation-of exp1 senv)
             (translation-of exp2 senv)
             (translation-of exp3 senv)))

    (var-exp (var)
             (nameless-var-exp
              (apply-senv senv var)))

    (let-exp (var exp1 body)
             (nameless-let-exp
              (translation-of exp1 senv)            
              (translation-of body
                              (extend-senv var senv))))

    (proc-exp (var body)
              (nameless-proc-exp
               (translation-of body
                               (extend-senv var senv))))

    (call-exp (rator rand)
              (call-exp
               (translation-of rator senv)
               (translation-of rand senv)))

    ;; Exercise 3.38
    (cond-exp (exp1 exp2)
              (cond-exp
               (map (lambda (x) (translation-of x senv)) exp1)
               (map (lambda (x) (translation-of x senv)) exp2)))

    (else (report-invalid-source-expression exp))))

(define (report-invalid-source-expression exp)
  (eopl:error 'value-of 
              "Illegal expression in source code: ~s" exp))

;;;;;;;;;;;;;;;; static environments ;;;;;;;;;;;;;;;;

;;; Senv = Listof(Sym)
;;; Lexaddr = N

;; empty-senv : () -> Senv
(define (empty-senv) '())

;; extend-senv : Var * Senv -> Senv
(define (extend-senv var senv)
  (cons var senv))

;; apply-senv : Senv * Var -> Lexaddr
(define (apply-senv senv var)
  (cond
    ((null? senv) (report-unbound-var var))
    ((eqv? var (car senv))
     0)
    (else
     (+ 1 (apply-senv (cdr senv) var)))))

(define (report-unbound-var var)
  (eopl:error 'translation-of "unbound variable in code: ~s" var))

;; init-senv : () -> Senv
(define (init-senv)
  (extend-senv 'i
               (extend-senv 'v
                            (extend-senv 'x
                                         (empty-senv)))))


;;; INTERPRETER

;; value-of-translation : Nameless-program -> ExpVal
(define (value-of-program pgm)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (init-nameless-env)))))

;; value-of : Nameless-exp * Nameless-env -> ExpVal
(define (value-of exp nameless-env)
    (cases expression exp
      (const-exp (num) (num-val num))
      
      (diff-exp (exp1 exp2)
                (let ((val1
                       (expval->num
                        (value-of exp1 nameless-env)))
                      (val2
                       (expval->num
                        (value-of exp2 nameless-env))))
                  (num-val
                   (- val1 val2))))
      
      (zero?-exp (exp1)
                 (let ((val1 (expval->num (value-of exp1 nameless-env))))
                   (if (zero? val1)
                       (bool-val #t)
                       (bool-val #f))))
      
      (if-exp (exp0 exp1 exp2) 
              (if (expval->bool (value-of exp0 nameless-env))
                  (value-of exp1 nameless-env)
                  (value-of exp2 nameless-env)))
      
      (call-exp (rator rand)          
                (let ((proc (expval->proc (value-of rator nameless-env)))
                      (arg (value-of rand nameless-env)))
                  (apply-procedure proc arg)))
      
      (nameless-var-exp (n)
                        (apply-nameless-env nameless-env n))
      
      (nameless-let-exp (exp1 body)
                        (let ((val (value-of exp1 nameless-env)))
                          (value-of body
                                    (extend-nameless-env val nameless-env))))
      
      (nameless-proc-exp (body)
                         (proc-val
                          (procedure body nameless-env)))

      ;; Exercise 3.38
      (cond-exp (exp1 exp2) (cond-exp-aux exp1 exp2 nameless-env))
      
      (else
       (eopl:error 'value-of 
                   "Illegal expression in translated code: ~s" exp))
      
      ))

;; Exercise 3.38
(define cond-exp-aux
  (lambda (exp1 exp2 nameless-env)
    (if (null? exp1) (eopl:error 'value-of "NOOB")
        (if (expval->bool (value-of (car exp1) nameless-env)) (value-of (car exp2) nameless-env)
            (cond-exp-aux (cdr exp1) (cdr exp2) nameless-env)))))


;; apply-procedure : Proc * ExpVal -> ExpVal

(define (apply-procedure proc1 arg)
    (cases proc proc1
      (procedure (body saved-env)
                 (value-of body (extend-nameless-env arg saved-env)))))


;;; TOP LEVEL ;;;

;; eval : String -> ExpVal

(define (eval string)
  (value-of-program
   (translation-of-program
    (scan&parse string))))

;;; EXAMPLES

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
; 


;; Exercise 3.38
(check-expect (eval "let a = 0
                     in let b = 1
                        in let c = 1
                           in cond zero?(0) ==> b
                                   zero?(1) ==> c
                           end") (num-val 1))

;; Exercise 3.38
(check-expect (eval "let a = proc (x)
                         cond zero?(x) ==> 1
                              zero?(-(x, 1)) ==> 0
                         end in (a 1)") (num-val 0))

(test)
