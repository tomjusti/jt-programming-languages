#lang eopl
(require test-engine/racket-tests)

;; Exercise 2.21

(define-datatype env env?
  (empty-env)
  (extend-env
   (var symbol?)
   (val number?)
   (environment env?)))

(define (has-binding? envi searchVar)
  (cases env envi
    (empty-env () #f)
    (extend-env (var val envir)
                (if (eqv? var searchVar) #t
                (has-binding? envir searchVar)))))

;; Exercise 2.22

(define-datatype stack stack?
  (empty-stack)
  (push
   (val number?)
   (s stack?)))

(define (empty-stack? stk)
  (cases stack stk
    (empty-stack () #t)
    (push (val s) #f)))

(check-expect (empty-stack? (empty-stack)) #t)

(define (top stk)
  (cases stack stk
    (empty-stack () '())
    (push (val s)
          val)))

(define (pop stk)
  (cases stack stk
    (empty-stack () '())
    (push (val s)
          s)))

(define l (push 8 (push 7 (empty-stack))))
(check-expect (top l) 8)

;; Exercise 2.24

(define-datatype bintree bintree?
  (leaf-node (num number?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

(define (bintree-to-list tree)
  (cases bintree tree
    (leaf-node (n) (list 'leaf-node n))
    (interior-node (key left right)
                   (list 'interior-node key (bintree-to-list left) (bintree-to-list right)))))

(check-expect (bintree-to-list (interior-node 'a (leaf-node 1) (leaf-node 2))) '(interior-node a (leaf-node 1) (leaf-node 2)))

;; Exercise 2.25

(define tree-1 (interior-node 'foo (leaf-node 2) (leaf-node 3)))
(define tree-2 (interior-node 'bar (leaf-node -1) tree-1))
(define tree-3 (interior-node 'baz tree-2 (leaf-node 1)))

;; Purpose: returns the sum of the leaves of a tree
(define (sum-tree int-node)
  (cases bintree int-node
    (leaf-node (int-node) int-node)
    (interior-node (key left right)
                   (+ (if (bintree? left) (sum-tree left) left)
                      (if (bintree? right) (sum-tree right) right)))))

;; get-key: bintree -> symbol
;; Purpose: returns the key of a bintree
(define (get-key bt)
  (cases bintree bt
    (leaf-node (num) num)
    (interior-node (key left right) key)))

;; max-interior: bintree -> symbol
;; Purpose: returns the symbol of the bintree with the max leaf sum
;; bintree must contain one interior node for one branch
(define (max-interior bt)
  (cases bintree bt
    (leaf-node (bt) (get-key bt))
    (interior-node (key left right)
                   (cond
                     [(and (> (sum-tree bt) (sum-tree left)) (> (sum-tree bt) (sum-tree right))) (get-key bt)]
                     [(> (sum-tree left) (sum-tree right)) (get-key left)]
                     [else (get-key right)]))))
                  
(check-expect (max-interior tree-3) 'baz)

;; Exercise 2.28

(define-datatype expr expr?
  (var-expr
   (id symbol?))
  (lambda-expr 
   (id symbol?)
   (body expr?))
  (app-expr
   (op expr?)
   (arg expr?)))

(define (unparse e)
  (cases expr e
    (var-expr (id)  id)
    (lambda-expr (id body)
                 (list 'lambda (list id) (unparse body)))
    (app-expr (op arg)
              (list (unparse op) (unparse arg)))))

;; Exercise 2.29

(define-datatype lc-expr lc-expr?
  (va-expr
   (id symbol?))
  (lambd-expr 
   (id list?)
   (body expr?))
  (ap-expr
   (op expr?)
   (arg expr?)))

(test)