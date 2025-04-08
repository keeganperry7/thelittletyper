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

(claim n+zero=n
  (Pi ((n Nat)) (= Nat (+ n 0) n)))
(define n+zero=n
  (lambda (n)
    (ind-Nat n
      (lambda (n) (= Nat (+ n 0) n))
      (same zero)
      (lambda (_ ih)
        (cong ih (+ 1))))))

(claim add1-+=+-add1
  (Pi ((a Nat) (b Nat)) 
    (= Nat (add1 (+ a b)) (+ a (add1 b)) )))
(define add1-+=+-add1
  (lambda (a b)
    (ind-Nat a
      (lambda (a) (= Nat (add1 (+ a b)) (+ a (add1 b))))
      (same (add1 b))
      (lambda (_ ih)
        (cong ih (+ 1))))))

; Exercise 3
(claim a+b=b+a
  (Pi ((a Nat) (b Nat))
    (= Nat (+ a b) (+ b a))))
(define a+b=b+a
  (lambda (a b)
    (ind-Nat a
      (lambda (a) (= Nat (+ a b) (+ b a)))
      (symm (n+zero=n b))
      (lambda (a ih)
        (trans (cong ih (+ 1)) (add1-+=+-add1 b a))))))

