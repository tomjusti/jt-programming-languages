#lang eopl

(require test-engine/racket-tests)

(define n-to-zero 'uninitialized)
(define res 'uninitialized)

;; fact-iter: int -> int
;; Purpose: to return the factorial of n by assigning n-to-zero and res
;;          and then calling fact-iter-acc
(define fact-iter
  (lambda (n) (begin
                (set! res 1) ;; BASE CASE: 0! = 1
                             ;; 'uninitialized -> 1
                (cond
                  [(or (< n 0) (not (integer? n))) (eopl:error "n has to be a non-negative integer!")] 
                  [else (set! n-to-zero n)]) ;; 'uninitialized -> n
                (fact-iter-acc))))

;; fact-iter-acc: void -> int
;; Purpose: to return the factorial using assignment and recursion
(define (fact-iter-acc)
  (cond
    [(= n-to-zero 0) res]
    [else (begin
                (set! res (* res n-to-zero)) ;; res -> (res * n-to-zero)
                (set! n-to-zero (- n-to-zero 1)) ;; n-to-zero -> (n-to-zero - 1)
                (fact-iter-acc))]))

(check-expect (fact-iter 0) 1)
(check-expect (fact-iter 1) 1)
(check-expect (fact-iter 2) 2)
(check-expect (fact-iter 3) 6)
(check-expect (fact-iter 4) 24)
(check-expect (fact-iter 5) 120)

(test)