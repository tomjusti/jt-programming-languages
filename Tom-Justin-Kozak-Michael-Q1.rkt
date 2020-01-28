;; Programming Languages
;; Quiz 1
;; Justin Tom & Michael Kozak

#lang eopl
(require test-engine/racket-tests)

;; Exercise 1.34

;; path: int, bst -> list-of-symbols
;; Purpose: to return a list of directions (left or right) to the node containing n
;; Assumption: n is in the BST and all values in the BST are unique
(define path
  (lambda (n bst)
    (if (eqv? n (car bst)) '()
        (if (< n (car bst)) (cons 'L (path n (cadr bst)))
            (cons 'R (path n (caddr bst)))))))

(check-expect (path 17 '(14 (7 () (12 () ())) (26 (20 (17 () ()) ()) (31 () ())))) '(R L L)) ;; example from the book
(check-expect (path 20 '(14 (7 () (12 () ())) (26 (20 (17 () ()) ()) (31 () ())))) '(R L))
(check-expect (path 31 '(14 (7 () (12 () ())) (26 (20 (17 () ()) ()) (31 () ())))) '(R R))
(check-expect (path 12 '(14 (7 () (12 () ())) (26 (20 (17 () ()) ()) (31 () ())))) '(L R))
(check-expect (path 11 '(10 (9 () ()) (11 () ()))) '(R))
(check-expect (path 9 '(10 (9 () ()) (11 () ()))) '(L))
(check-expect (path 10 '(10 (9 () ()) (11 () ()))) '())
(check-expect (path 1 '(1 () ())) '())

;; Exercise 1.35

;; leaf: int -> int
;; Purpose:  builds a leaf for a bintree
(define leaf (lambda (n) n))

(check-expect (leaf 2) 2)
(check-expect (leaf 1) 1)
(check-expect (leaf 0) 0)

;; <leaf> ::== <integer>
;; <interior-node> ::== <bintree>
;; <bintree> ::== <interior-node> | <leaf>
;; interior-node: symbol, bintree, bintree -> bintree
;; Purpose: builds an interior-node for a bintree
(define interior-node
  (lambda (name left right) (list name left right)))

(check-expect
 (interior-node 'foo (interior-node 'bar (leaf 26) (leaf 12)) (interior-node 'baz (leaf 11) (interior-node 'quux (leaf 117) (leaf 14))))
 '(foo (bar 26 12) (baz 11 (quux 117 14)))) ;; example from the book
(check-expect (interior-node 'a (interior-node 'b (leaf 3) (leaf 2)) (leaf 3)) '(a (b 3 2) 3))
(check-expect (interior-node 'cest (interior-node 'la (leaf 5) (leaf 4)) (interior-node 'vie (leaf 6) (leaf 3))) '(cest (la 5 4) (vie 6 3)))

;; contents-of: bintree -> bintree
;; Purpose: to return the root
(define contents-of
  (lambda (bintree)
    (if (number? bintree) bintree (car bintree))))

(check-expect
 (contents-of
  (interior-node 'foo
                 (interior-node 'bar (leaf 26) (leaf 12))
                 (interior-node 'baz (leaf 11) (interior-node 'quux (leaf 117) (leaf 14))))) 'foo) ;; example from the book
(check-expect (contents-of (interior-node 'a (interior-node 'b (leaf 3) (leaf 2)) (leaf 3))) 'a)
(check-expect
 (contents-of
  (interior-node 'cest (interior-node 'la (leaf 5) (leaf 4)) (interior-node 'vie (leaf 6) (leaf 3)))) 'cest)

;; number-leaves: bintree -> bintree
;; Purpose: to produce a bintree like the argument, except the contents of the leaves are numbered starting from 0
(define (number-leaves bintree)
  (car (pre-order-traverse bintree 0)))

;; pre-order-traverse: bintree, int -> b-list
;; <b-list> ::== <bintree> & <int>
;; Purpose: to traverse a bintree using pre-order traversal (root, left, right)
;; Accumulative Invariant: count is the number of leaves processed
(define pre-order-traverse
  (lambda (bintree count)
    (if (number? bintree) (cons (leaf count) (+ count 1))
        (letrec ([left (pre-order-traverse (cadr bintree) count)]
                 [right (pre-order-traverse (caddr bintree) (cdr left))])
          (cons
           (interior-node (contents-of bintree) (car left) (car right))
           (cdr right))))))

(check-expect (pre-order-traverse
               (interior-node 'foo
                 (interior-node 'bar (leaf 26) (leaf 12))
                 (interior-node 'baz (leaf 11) (interior-node 'quux (leaf 117) (leaf 14)))) 0)
              '((foo (bar 0 1) (baz 2 (quux 3 4))) . 5)) ;; example from the book
(check-expect (pre-order-traverse (interior-node 'a (interior-node 'b (leaf 3) (leaf 2)) (leaf 3)) 0) '((a (b 0 1) 2) . 3))
(check-expect (pre-order-traverse (leaf 3) 0) '(0 . 1))

(check-expect (number-leaves (interior-node 'foo
                 (interior-node 'bar (leaf 26) (leaf 12))
                 (interior-node 'baz (leaf 11) (interior-node 'quux (leaf 117) (leaf 14)))))
              '(foo (bar 0 1) (baz 2 (quux 3 4)))) ;; example from the book
(check-expect (number-leaves (interior-node 'cest (interior-node 'la-vie (leaf 3) (leaf 2)) (leaf 3))) '(cest (la-vie 0 1) 2))
(check-expect (number-leaves (leaf 3)) 0)


(test)