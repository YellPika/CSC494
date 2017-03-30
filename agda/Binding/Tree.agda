module Binding.Tree where

open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_; id)
open import Relation.Unary using (_⊆_)

infixr 5 _∺_

_∺_ : {A : Set} → A → (ℕ → A) → (ℕ → A)
(x ∺ xs) zero = x
(x ∺ xs) (suc n) = xs n

data Tree (F : List ℕ → Set) : Set where
  var : ℕ → Tree F
  op  : ∀ {ns} → F ns → All (λ _ → Tree F) ns → Tree F

pattern _∷[_]_ t n u = _∷_ {x = n} t u

lift : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
lift zero σ = σ
lift (suc n) σ = zero ∺ suc ∘ lift n σ

mutual
  map : ∀ {F} → (ℕ → ℕ) → Tree F → Tree F
  map σ (var x) = var (σ x)
  map σ (op p ts) = op p (map* σ ts)

  map* : ∀ {F} → (ℕ → ℕ) → All (λ _ → Tree F) ⊆ All (λ _ → Tree F)
  map* σ [] = []
  map* σ (t ∷[ n ] ts) = map (lift n σ) t  ∷ map* σ ts

raise : ∀ {F} → ℕ → (ℕ → Tree F) → (ℕ → Tree F)
raise zero σ x = σ x
raise (suc n) σ = var zero ∺ map suc ∘ raise n σ

mutual
  bind : ∀ {F} → (ℕ → Tree F) → Tree F → Tree F
  bind σ (var x) = σ x
  bind σ (op p ts) = op p (bind* σ ts)

  bind* : ∀ {F} → (ℕ → Tree F) → All (λ _ → Tree F) ⊆ All (λ _ → Tree F)
  bind* σ [] = []
  bind* σ (t ∷[ n ] ts) = bind (raise n σ) t ∷ bind* σ ts
