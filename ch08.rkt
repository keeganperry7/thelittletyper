#lang pie

(claim step-+
  (-> Nat Nat Nat))
(define step-+
  (lambda (_ n-1) (add1 n-1)))

(claim +
  (-> Nat Nat Nat))
(define +
  (lambda (n m)
    (rec-Nat n
      m
      step-+)))

; Exercise 1
(claim zero+n=n
  (Pi ((n Nat)) (= Nat (+ 0 n) n)))
(define zero+n=n
  (lambda (n)
    (same n)))

; Exercise 2
(claim a=b->a+n=b+n
  (Pi ((a Nat) (b Nat) (n Nat))
    (-> 
      (= Nat a b)
      (= Nat (+ a n) (+ b n)))))
(define a=b->a+n=b+n
  (lambda (_ _ n a=b)
    (cong a=b (the (-> Nat Nat) (lambda (x) (+ x n))))))

; Exercise 3
(claim mot-plus-assoc
  (-> Nat Nat Nat U))
(define mot-plus-assoc
  (lambda (n m k)
    (= Nat (+ k (+ n m)) (+ (+ k n) m))))

(claim base-plus-assoc
  (Pi ((n Nat) (m Nat))
    (= Nat (+ zero (+ n m)) (+ (+ zero n) m))))
(define base-plus-assoc
  (lambda (n m)
    (same (+ n m))))

(claim step-plus-assoc
  (Pi ((n Nat) (m Nat) (k Nat))
    (-> 
      (= Nat (+ k (+ n m)) (+ (+ k n) m))
      (= Nat (+ (add1 k) (+ n m)) (+ (+ (add1 k) n) m)))))
(define step-plus-assoc
  (lambda (_ _ _ ih)
    (cong ih (+ 1))))

(claim plus-assoc
 (Pi ((n Nat) (m Nat) (k Nat))
   (= Nat (+ k (+ n m)) (+ (+ k n) m))))
(define plus-assoc
  (lambda (n m k)
    (ind-Nat k
      (lambda (k) (= Nat (+ k (+ n m)) (+ (+ k n) m)))
      (same (+ n m))
      (lambda (_ ih) 
        (cong ih (+ 1))))))