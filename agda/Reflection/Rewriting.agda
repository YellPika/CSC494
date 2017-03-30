module Reflection.Rewriting where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Reflection
open import Reflection.Patterns

Rule : Set
Rule = (Term → TC (Maybe Term)) → (Term → TC (Maybe Term))

fail : Rule
fail rec term = typeError []

infixr 5 _&_

_&_ : Rule → Rule → Rule
(f & g) rec term =
  bindTC (f rec term) λ where
    (just proof) → returnTC (just proof)
    nothing → g rec term

private
  infer-right : ∀ {a} {A : Set a} x {y : A} → x ≡ y → A
  infer-right x {y} p = y

  _⇒_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  A ⇒ B = A → B

  combine : ∀ {a} {A : Set a} {w x y z : A} → w ≡ x → z ≡ y → x ≡ y → w ≡ z
  combine p q r = trans p (trans r (sym q))

  fixFor : {A B : Set} → ℕ → ((A → TC B) → A → TC B) → A → TC B
  fixFor zero f x = typeError (strErr "Recursion limt exceeded!" ∷ [])
  fixFor (suc n) f x = f (fixFor n f) x

  apply : Rule → Term → TC Term
  apply rule = fixFor 10 go
     where
       rule′ = fixFor 10 rule

       go : (Term → TC Term) → Term → TC Term
       go rec term =
         bindTC (rule′ term) λ where
           nothing → returnTC (con (quote refl) [])
           (just proof) → bindTC (normalise (def₂ (quote infer-right) term proof)) λ term′ →
                          bindTC (rec term′) λ proof′ →
                            returnTC (def₂ (quote trans) proof proof′)

  blockOnMetas : Term → TC ⊤

  blockOnArgMetas : Arg Term → TC ⊤
  blockOnArgMetas (arg i x) = blockOnMetas x

  blockOnArgsMetas : List (Arg Term) → TC ⊤
  blockOnArgsMetas [] = returnTC _
  blockOnArgsMetas (x ∷ xs) =
    bindTC (blockOnArgMetas x) λ _ →
      blockOnArgsMetas xs

  blockOnAbsMetas : Abs Term → TC ⊤
  blockOnAbsMetas (abs s x) = blockOnMetas x

  blockOnClauseMetas : Clause → TC ⊤
  blockOnClauseMetas (clause ps t) = blockOnMetas t
  blockOnClauseMetas (absurd-clause ps) = returnTC _

  blockOnClausesMetas : List Clause → TC ⊤
  blockOnClausesMetas [] = returnTC _
  blockOnClausesMetas (x ∷ xs) =
    bindTC (blockOnClauseMetas x) λ _ →
      blockOnClausesMetas xs

  blockOnMetas (var x args) = blockOnArgsMetas args
  blockOnMetas (con c args) = blockOnArgsMetas args
  blockOnMetas (def f args) = blockOnArgsMetas args
  blockOnMetas (lam v t) = blockOnAbsMetas t
  blockOnMetas (pat-lam cs args) =
    bindTC (blockOnClausesMetas cs) λ _ →
      blockOnArgsMetas args
  blockOnMetas (pi a b) =
    bindTC (blockOnArgMetas a) λ _ →
      blockOnAbsMetas b
  blockOnMetas (meta m _) = blockOnMeta m
  blockOnMetas _ = returnTC _

macro
  reduce : Rule → Term → TC ⊤
  reduce rule goal =
    bindTC (inferType goal) λ goal-type →
    bindTC (newMeta unknown) λ ant-lhs →
    bindTC (newMeta unknown) λ ant-rhs →
    bindTC (newMeta unknown) λ cns-lhs →
    bindTC (newMeta unknown) λ cns-rhs →
    bindTC (unify goal-type (def₂ (quote _⇒_) (def₂ (quote _≡_) ant-lhs ant-rhs) (def₂ (quote _≡_) cns-lhs cns-rhs))) λ _ →
    bindTC (normalise cns-lhs) λ cns-lhs →
    bindTC (normalise cns-rhs) λ cns-rhs →
    bindTC (blockOnMetas cns-lhs) λ _ →
    bindTC (blockOnMetas cns-rhs) λ _ →
    bindTC (apply rule cns-lhs) λ proof-lhs →
    bindTC (apply rule cns-rhs) λ proof-rhs →
      unify goal (def₂ (quote combine) proof-lhs proof-rhs)
