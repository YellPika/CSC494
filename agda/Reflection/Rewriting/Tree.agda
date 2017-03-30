module Reflection.Rewriting.Tree where

open import Data.List using ([]; _∷_; _∷ʳ'_; initLast)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong-app; sym)

open import Reflection
open import Reflection.Rewriting
open import Reflection.Patterns
open import Reflection.Substitution

open import Binding.Tree
open import Binding.Tree.Properties

pattern bind-rule σ t = def (quote bind) (_ ∷ arg′ σ ∷ arg′ t ∷ [])
pattern map-rule σ t = def (quote map) (_ ∷ arg′ σ ∷ arg′ t ∷ [])
pattern var-rule x = con (quote Tree.var) (_ ∷ arg′ x ∷ [])
pattern ∺-rule x xs n = def (quote _∺_) (_ ∷ arg′ x ∷ arg′ xs ∷ arg′ n ∷ [])

bind-id-rule : Rule
bind-id-rule rec (bind-rule (con (quote Tree.var) _) t) = returnTC (just (def₁ (quote bind-id) t))
bind-id-rule rec (bind-rule (lam _ (abs _ (var-rule (var 0 [])))) t) = returnTC (just (def₁ (quote bind-id) t))
bind-id-rule rec term = returnTC nothing

bind-∘-rule : Rule
bind-∘-rule rec (bind-rule σ (bind-rule τ t)) = returnTC (just (def₁ (quote sym) (def₃ (quote bind-∘) σ τ t)))
bind-∘-rule rec term = returnTC nothing

bind≡map-rule : Rule
bind≡map-rule rec (map-rule σ t) = returnTC (just (def₁ (quote sym) (def₂ (quote bind≡map) σ t)))
bind≡map-rule rec term = returnTC nothing

∺-dist-rule : Rule
∺-dist-rule rec (def nm args) with initLast args
... | args′ ∷ʳ' arg′ (∺-rule t σ x) = returnTC (just (def₄ (quote ∺-dist) (def nm args′) t σ x))
... | _ = returnTC nothing
∺-dist-rule rec term = returnTC nothing

private
  apply-in-function : (Term → TC (Maybe Term)) → Term → TC (Maybe Term)
  apply-in-function rec term =
    extendContext (arg′ (quoteTerm ℕ))
      (rec (apply (rename suc term) (arg′ (var 0 [] , _) ∷ [])))

bind-cong-rule₁ : Rule
bind-cong-rule₁ rec (bind-rule σ t) =
  bindTC (apply-in-function rec σ) λ where
    nothing → returnTC nothing
    (just proof) →
      returnTC (just (def₂ (quote bind-cong) (lam visible (abs "x" proof)) t))
bind-cong-rule₁ rec term = returnTC nothing

bind-cong-rule₂ : Rule
bind-cong-rule₂ rec (bind-rule σ t) =
  bindTC (rec t) λ where
    nothing → returnTC nothing
    (just proof) →
      returnTC (just (def₂ (quote cong) (def₁ (quote bind) σ) proof))
bind-cong-rule₂ rec term = returnTC nothing

∺-cong-rule₁ : Rule
∺-cong-rule₁ rec (∺-rule t σ x) =
  bindTC (rec t) λ where
    nothing → returnTC nothing
    (just proof) →
      returnTC (just (def₂ (quote cong-app) (def₂ (quote cong-app) (def₂ (quote cong) (def₀ (quote _∺_)) proof) σ) x))
∺-cong-rule₁ rec term = returnTC nothing

∺-cong-rule₂ : Rule
∺-cong-rule₂ rec (∺-rule t σ x) =
  bindTC (apply-in-function rec σ) λ where
    nothing → returnTC nothing
    (just proof) →
      returnTC (just (def₃ (quote ∺-cong) t (lam visible (abs "x" proof)) x))
∺-cong-rule₂ rec term = returnTC nothing

var-cong-rule : Rule
var-cong-rule rec (var-rule x) =
  bindTC (rec x) λ where
    nothing → returnTC nothing
    (just proof) →
      returnTC (just (def₂ (quote cong) (con (quote Tree.var) []) proof))
var-cong-rule rec term = returnTC nothing

tree-rule : Rule
tree-rule = bind-id-rule
          & bind≡map-rule
          & bind-∘-rule
          & bind-cong-rule₁
          & bind-cong-rule₂
          & var-cong-rule
          & ∺-dist-rule
          & ∺-cong-rule₁
          & ∺-cong-rule₂
