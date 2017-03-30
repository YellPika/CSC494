#lang untyped

; SKI combinators
(let id (λ (x) x))
(let const (λ (x y) x))
(let subst (λ (x y z) (x z (y z))))

; Booleans
(let true (λ (x y) x))
(let false (λ (x y) y))
(let if (λ (b t f) (b t f)))
(let not (λ (b) (if b false true)))
(let and (λ (b c) (if b c false)))
(let or (λ (b c) (if b true c)))

; Pairs
(let pair (λ (x y k) (k x y)))
(let fst (λ (p) (p true)))
(let snd (λ (p) (p false)))

; Choice
(let left (λ (x k) (k (λ (l r) (l x)))))
(let right (λ (x k) (k (λ (l r) (r x)))))
(let case (λ (l r c) (c l r)))

(let left? (case (const true) (const false)))
(let right? (case (const false) (const true)))

; Naturals
(let zero (λ (s z) z))
(let succ (λ (n s z) (s (n s z))))
(let pred (λ (n) (snd (n (λ (p) (pair (succ (fst p)) (fst p))) (pair zero zero)))))
(let rec (λ (s z n) (n s z)))

(let zero? (rec (const false) true))
(let succ? (rec (const true) false))

(let + (λ (n) (rec succ n)))
(let * (λ (n) (rec (+ n) zero)))
(let ^ (λ (n) (rec (* n) (succ zero))))
(let - (rec pred))

; Fixpoint combinators
(let Y (λ (f) ((λ (x) (f (x x))) (λ (x) (f (x x))))))
(let Z (λ (f) ((λ (x) (f (λ (v) (x x v)))) (λ (x) (f (λ (v) (x x v)))))))
