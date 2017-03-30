module SimplyTyped.Typing where

open import Data.List using (List; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Star using (ε; _◅_)
open import Function using (_∘_; id)

open import Binding.Tree

open import SimplyTyped.Syntax
open import SimplyTyped.Reduction

data _[_]=_ : List Type → ℕ → Type → Set where
  here : ∀ {a Γ} → (a ∷ Γ) [ zero ]= a
  there : ∀ {a b Γ x} → Γ [ x ]= a → (b ∷ Γ) [ suc x ]= a
  
data _⊢_∶_ (Γ : List Type) : Term → Type → Set where
  ⊢/var : ∀ {a x} → Γ [ x ]= a → Γ ⊢ var x ∶ a
  ⊢/elim : ∀ {a t} → Γ ⊢ t ∶ bot → Γ ⊢ elim t ∶ a
  ⊢/tt : Γ ⊢ tt ∶ top
  ⊢/left : ∀ {a b t} → Γ ⊢ t ∶ a → Γ ⊢ left t ∶ choice a b
  ⊢/right : ∀ {a b t} → Γ ⊢ t ∶ b → Γ ⊢ right t ∶ choice a b
  ⊢/switch : ∀ {a b c t u v} → Γ ⊢ t ∶ arr a c → Γ ⊢ u ∶ arr b c → Γ ⊢ v ∶ choice a b → Γ ⊢ switch t u v ∶ c
  ⊢/fst : ∀ {a b t} → Γ ⊢ t ∶ pair a b → Γ ⊢ fst t ∶ a
  ⊢/snd : ∀ {a b t} → Γ ⊢ t ∶ pair a b → Γ ⊢ snd t ∶ b
  ⊢/cons : ∀ {a b t u} → Γ ⊢ t ∶ a → Γ ⊢ u ∶ b → Γ ⊢ cons t u ∶ pair a b
  ⊢/lam : ∀ {a b t} → (a ∷ Γ) ⊢ t ∶ b → Γ ⊢ lam a t ∶ arr a b
  ⊢/app : ∀ {a b t u} → Γ ⊢ t ∶ arr a b → Γ ⊢ u ∶ a → Γ ⊢ app t u ∶ b

⊢/map : ∀ {Γ Δ σ t a} → (∀ {x a} → Γ [ x ]= a → Δ [ σ x ]= a) → Γ ⊢ t ∶ a → Δ ⊢ map σ t ∶ a
⊢/map h (⊢/var x) = ⊢/var (h x)
⊢/map h (⊢/elim d) = ⊢/elim (⊢/map h d)
⊢/map h ⊢/tt = ⊢/tt
⊢/map h (⊢/left d) = ⊢/left (⊢/map h d)
⊢/map h (⊢/right d) = ⊢/right (⊢/map h d)
⊢/map h (⊢/switch d₁ d₂ d₃) = ⊢/switch (⊢/map h d₁) (⊢/map h d₂) (⊢/map h d₃)
⊢/map h (⊢/fst d) = ⊢/fst (⊢/map h d)
⊢/map h (⊢/snd d) = ⊢/snd (⊢/map h d)
⊢/map h (⊢/cons d₁ d₂) = ⊢/cons (⊢/map h d₁) (⊢/map h d₂)
⊢/map h (⊢/lam d) =
  ⊢/lam (⊢/map
    (λ where
      here → here
      (there p) → there (h p))
    d)
⊢/map h (⊢/app d₁ d₂) = ⊢/app (⊢/map h d₁) (⊢/map h d₂)

⊢/bind : ∀ {Γ Δ σ t a} → (∀ {x a} → Γ [ x ]= a → Δ ⊢ σ x ∶ a) → Γ ⊢ t ∶ a → Δ ⊢ bind σ t ∶ a
⊢/bind h (⊢/var x) = h x
⊢/bind h (⊢/elim d) = ⊢/elim (⊢/bind h d)
⊢/bind h ⊢/tt = ⊢/tt
⊢/bind h (⊢/left d) = ⊢/left (⊢/bind h d)
⊢/bind h (⊢/right d) = ⊢/right (⊢/bind h d)
⊢/bind h (⊢/switch d₁ d₂ d₃) = ⊢/switch (⊢/bind h d₁) (⊢/bind h d₂) (⊢/bind h d₃)
⊢/bind h (⊢/fst d) = ⊢/fst (⊢/bind h d)
⊢/bind h (⊢/snd d) = ⊢/snd (⊢/bind h d)
⊢/bind h (⊢/cons d₁ d₂) = ⊢/cons (⊢/bind h d₁) (⊢/bind h d₂)
⊢/bind h (⊢/lam d) =
  ⊢/lam (⊢/bind
    (λ where
      here → ⊢/var here
      (there p) → ⊢/map there (h p))
    d)
⊢/bind h (⊢/app d₁ d₂) = ⊢/app (⊢/bind h d₁) (⊢/bind h d₂)

⊢/→¹ : ∀ {Γ t t′ a} → t →¹ t′ → Γ ⊢ t ∶ a → Γ ⊢ t′ ∶ a
⊢/→¹ (→¹/elim s) (⊢/elim d) = ⊢/elim (⊢/→¹ s d)
⊢/→¹ (→¹/left s) (⊢/left d) = ⊢/left (⊢/→¹ s d)
⊢/→¹ (→¹/right s) (⊢/right d) = ⊢/right (⊢/→¹ s d)
⊢/→¹ (→¹/switch₁ s) (⊢/switch d₁ d₂ d₃) = ⊢/switch (⊢/→¹ s d₁) d₂ d₃
⊢/→¹ (→¹/switch₂ s) (⊢/switch d₁ d₂ d₃) = ⊢/switch d₁ (⊢/→¹ s d₂) d₃
⊢/→¹ (→¹/switch₃ s) (⊢/switch d₁ d₂ d₃) = ⊢/switch d₁ d₂ (⊢/→¹ s d₃)
⊢/→¹ (→¹/fst s) (⊢/fst d) = ⊢/fst (⊢/→¹ s d)
⊢/→¹ (→¹/snd s) (⊢/snd d) = ⊢/snd (⊢/→¹ s d)
⊢/→¹ (→¹/consₗ s) (⊢/cons d₁ d₂) = ⊢/cons (⊢/→¹ s d₁) d₂
⊢/→¹ (→¹/consᵣ s) (⊢/cons d₁ d₂) = ⊢/cons d₁ (⊢/→¹ s d₂)
⊢/→¹ (→¹/lam s) (⊢/lam d) = ⊢/lam (⊢/→¹ s d)
⊢/→¹ (→¹/appₗ s) (⊢/app d₁ d₂) = ⊢/app (⊢/→¹ s d₁) d₂
⊢/→¹ (→¹/appᵣ s) (⊢/app d₁ d₂) = ⊢/app d₁ (⊢/→¹ s d₂)
⊢/→¹ →¹/beta (⊢/app (⊢/lam d₁) d₂) = ⊢/bind (λ { here → d₂ ; (there x) → ⊢/var x }) d₁
⊢/→¹ →¹/fst-cons (⊢/fst (⊢/cons d₁ d₂)) = d₁
⊢/→¹ →¹/snd-cons (⊢/snd (⊢/cons d₁ d₂)) = d₂
⊢/→¹ →¹/switch-left (⊢/switch d₁ d₂ (⊢/left d₃)) = ⊢/app d₁ d₃
⊢/→¹ →¹/switch-right (⊢/switch d₁ d₂ (⊢/right d₃)) = ⊢/app d₂ d₃

⊢/→¹* : ∀ {Γ t t′ a} → t →¹* t′ → Γ ⊢ t ∶ a → Γ ⊢ t′ ∶ a
⊢/→¹* ε = id
⊢/→¹* (s ◅ ss) = ⊢/→¹* ss ∘ ⊢/→¹ s

⊢/⇉ : ∀ {Γ t t′ a} → t ⇉ t′ → Γ ⊢ t ∶ a → Γ ⊢ t′ ∶ a
⊢/⇉ s = ⊢/→¹* (⇉-to-→¹ s)
