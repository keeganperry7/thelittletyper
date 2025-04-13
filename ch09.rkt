#lang pie

; Exercise 1
(claim same-cons
  (Pi ((t U) (x t) (as (List t)) (bs (List t)))
    (-> (= (List t) as bs)
        (= (List t) (:: x as) (:: x bs)))))
(define same-cons
  (lambda (t x as _bs as=bs)
    (replace as=bs
      (lambda (k) (= (List t) (:: x as) (:: x k)))
      (same (:: x as)))))

; Exercise 2
(claim same-lists
  (Pi ((t U) (e1 t) (e2 t) (l1 (List t)) (l2 (List t)))
    (-> (= (List t) l1 l2) (= t e1 e2)
        (= (List t) (:: e1 l1) (:: e2 l2)))))
(define same-lists
  (lambda (t e1 _e2 l1 l2 l1=l2 e1=e2)
    (replace (cong e1=e2 (the (-> t (List t)) (lambda (x) (:: x l2))))
      (lambda (k) (= (List t) (:: e1 l1) k))
      (cong l1=l2 (the (-> (List t) (List t)) (lambda (l) (:: e1 l)))))))

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
        (replace (add1-+=+-add1 b a)
          (lambda (k) (= Nat (add1 (+ a b)) k))
          (cong ih (+ 1)))))))

; (define a+b=b+a
;   (lambda (a b)
;     (ind-Nat a
;       (lambda (a) (= Nat (+ a b) (+ b a)))
;       (symm (n+zero=n b))
;       (lambda (a ih)
;         (trans (cong ih (+ 1)) (add1-+=+-add1 b a))))))