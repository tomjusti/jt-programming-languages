#lang eopl
(require test-engine/racket-tests)


;; 1.12
(define subst-112
  (lambda (new old slist)
    (if (null? slist) '()
        (cons
         (if (symbol? (car slist))
             (if (eqv? (car slist) old) new (car slist))
             (subst-112 new old (car slist)))
         (subst-112 new old (cdr slist))))))

;; 1.13
(define subst
  (lambda (new old slist)
    (if (null? slist) '()
    (map (lambda (sexp) (subst-in-s-exp new old sexp))
         slist))))

(define subst-in-s-exp
  (lambda (new old sexp)
    (if (symbol? sexp)
        (if (eqv? sexp old) new sexp)
        (subst new old sexp))))

;; 1.15
;; duple: int int -> list-of-int
(define duple
  (lambda (n x)
    (if (zero? n) '()
        (cons x (duple (- n 1) x)))))

(check-expect (duple 2 3) (list 3 3))

;; 1.16
;; invert: list-of-list -> list-of-list
(define invert
  (lambda (lst)
    (if (null? lst) '()
        (cons (list (cadar lst) (caar lst)) (invert (cdr lst))))))

(check-expect (invert '((a 1) (a 2) (1 b) (2 b))) '((1 a) (2 a) (b 1) (b 2)))


;; 1.17
;; down: list-of-X -> list-of-list
(define down
  (lambda (lst)
    (map list lst)))

(check-expect (down '(1 2 3)) '((1) (2) (3)))

;; 1.24
;; every?: pred list-of-X -> boolean
(define every?
  (lambda (pred lst)
    (cond
      ((null? lst) #t)
      ((pred (car lst)) (every? pred (cdr lst))) (#t #f))))

(check-expect (every? number? '(1 2 3)) #t)

;; 1.25
;; exists?: pred list-of-X -> boolean
(define exists?
  (lambda (pred lst)
    (if (null? lst) #f
        (if (pred (car lst)) #t
            (exists? pred (cdr lst))))))

(check-expect (exists? number? '(a 2 b)) #t)

;; 1.27
;; flatten: list-of-X -> list-of-X
(define flatten
  (lambda (slist)
    (if (null? slist) '()
        (if (pair? slist) (append (flatten (car slist)) (flatten (cdr slist)))
            (list slist)))))
        
(check-expect (flatten '(a b c)) '(a b c))
(check-expect (flatten '((a) () (b ()) () (c))) '(a b c))

;; 1.28
;; merge: list-of-int list-of-int -> list-of-int
(define merge
  (lambda (loi1 loi2)
    (if (null? loi1) loi2
        (if (null? loi2) loi1
            (if (< (car loi1) (car loi2)) (cons (car loi1) (merge (cdr loi1) loi2))
                (cons (car loi2) (merge loi1 (cdr loi2))))))))

(check-expect (merge '(1 4) '(1 2 8)) '(1 1 2 4 8))
(check-expect (merge '(35 62 81 90 91) '(3 83 85 90)) '(3 35 62 81 83 85 90 90 91))

;; 1.29
;; insert: int list-of-int -> list-of-int
(define (insert n loi)
    (if (null? loi) (cons n loi)
        (if (<= n (car loi)) (cons n loi)
            (cons (car loi) (insert n (cdr loi))))))


;; insertion-sort: list-of-int -> list-of-int
(define insertion-sort
  (lambda (loi)
    (if (null? loi) '()
        (insert (car loi) (insertion-sort (cdr loi))))))

;; sort: list-of-int -> list-of-int
(define sort
  (lambda (loi)
    (insertion-sort loi)))

(check-expect (sort '(8 2 5 2 3)) '(2 2 3 5 8))

;; Slide 93
(define (partialVectorSum V n)
  (if (zero? n) 0
      (+ (vector-ref V (- n 1))
         (partialVectorSum V (- n 1)))))

(define (vectorSum V)
  (partialVectorSum V (vector-length V)))


;; partialVectorInterval: vector int int -> int
(define partialVectorSumVI
  (lambda (V low high)
    (if (eqv? low (+ high 1)) 0
        (+ (vector-ref V low) (partialVectorSumVI V (+ low 1) high)))))

;; vectorSumVI: vector -> int
(define (vectorSumVI V)
  (partialVectorSumVI V 0 (- (vector-length V) 1)))

(check-expect (vectorSumVI (vector 1 2 3)) 6)

(test)