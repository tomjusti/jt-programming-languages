#lang racket

(require test-engine/racket-tests)

; ; Q1. Transform the following functions to CPS
; ; 
; ; (define (f a b) (+ a b))
; ; 
; ; (define (g x) (* 2 x))
; ; 
; ; (check-expect (f 1 2) 3)
; ; (check-expect (g 10) 20)
; 

; Write your answers to Q1 here:

;; f: num, num -> num
;; Purpose: to return the sum of the two arguments
(define (f a b) (+ a b))

;; CPS
(define (f/k a b k)
  (k (+ a b)))

;; g: num -> num
;; Purpose: to return the product of 2 and x
(define (g x) (* 2 x))

;; CPS
(define (g/k x k)
  (k (* 2 x)))

(check-expect (f 1 2) (f/k 1 2 (lambda (v) v)))
(check-expect (g 10) (g/k 10 (lambda (v) v)))

; ; Q2. Transform the following functions to CPS
; ; 
; ; (define (greater= a b)
; ;   (if (>= a b) a b))
; ; 
; ; (define (find-max L)
; ;   (if (= (length L) 1)
; ;       (car L)
; ;       (greater= (car L) (find-max (rest L)))))
; ; 
; ; (check-expect (greater= 10 12) 12)
; ; (check-expect (greater= 98 4) 98)
; ; (check-expect (find-max '(1967)) 1967)
; ; (check-expect (find-max '(2 87 34 68 1)) 87)
; 

; Write your answers to Q2 here:

;; greater=: num, num ->  num
;; Purpose: to return a if it is greater or equal to b or b if it's not
(define (greater= a b)
  (if (>= a b) a b))

;; CPS
(define (greater=/k a b k)
  (if (>= a b) (k a) (k b)))

;; find-max: num -> num
(define (find-max L)
  (if (= (length L) 1)
      (car L)
      (greater= (car L) (find-max (rest L)))))

;; CPS
(define (find-max/k L k)
  (if (= (length L) 1)
      (k (car L))
      (find-max/k (rest L) (lambda (v) (greater=/k (car L) v k)))))

(check-expect (greater= 10 12) (greater=/k 10 12 (lambda (v) v)))
(check-expect (greater= 98 4) (greater=/k 98 4 (lambda (v) v)))
(check-expect (find-max '(1967)) (find-max/k '(1967) (lambda (v) v)))
(check-expect (find-max '(2 87 34 68 1)) (find-max/k '(2 87 34 68 1) (lambda (v) v)))

; ; Q3. Transform the following functions to CPS
; ; 
; ; (define (tri n) (/ (* n (add1 n)) 2))
; ; 
; ; (define (tetra n)
; ;   (if (= n 0)
; ;       0
; ;       (+ (tri n) (tetra (sub1 n)))))
; ; 
; ; (check-expect (tri 10) 55)
; ; (check-expect (tri 5) 15)
; ; (check-expect (tetra 1) 1)
; ; (check-expect (tetra 10) 220)
; 

; Write your answers to Q3 here:

;; tri: num -> num
;; Purpose: to return (/ (* n (add1 n)) 2) 
(define (tri n) (/ (* n (add1 n)) 2))

;; CPS
(define (tri/k n k)
  (k (/ (* n (add1 n)) 2)))

;; tetra: num -> num
(define (tetra n)
  (if (= n 0)
      0
      (+ (tri n) (tetra (sub1 n)))))

;; CPS
(define (tetra/k n k)
  (if (= n 0) (k 0)
      (tri/k n (lambda (v) (tetra/k (sub1 n) (lambda (w) (k (+ v w))))))))

(check-expect (tri 10) (tri/k 10 (lambda (v) v)))
(check-expect (tri 5) (tri/k 5 (lambda (v) v)))
(check-expect (tetra 1) (tetra/k 1 (lambda (v) v)))
(check-expect (tetra 10) (tetra/k 10 (lambda (v) v)))

(test)
