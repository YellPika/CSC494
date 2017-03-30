module SimplyTyped.Reduction where

open import Data.Nat using (zero; suc)
open import Data.Product using (∃; _×_; _,_)
open import Data.Star as Star using (Star; ε; _◅_; _◅◅_; gmap; return; _>>=_)
open import Function using (_∘_; flip)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import Binding.Tree
open import Reflection.Rewriting
open import Reflection.Rewriting.Tree

open import SimplyTyped.Syntax

data _⇉_ : Term → Term → Set where
  ⇉/var : ∀ {x} → var x ⇉ var x
  ⇉/elim : ∀ {t t′} → t ⇉ t′ → elim t ⇉ elim t′
  ⇉/tt : tt ⇉ tt
  ⇉/left : ∀ {t t′} → t ⇉ t′ → left t ⇉ left t′
  ⇉/right : ∀ {t t′} → t ⇉ t′ → right t ⇉ right t′
  ⇉/switch : ∀ {t₁ t₁′ t₂ t₂′ t₃ t₃′} → t₁ ⇉ t₁′ → t₂ ⇉ t₂′ → t₃ ⇉ t₃′ → switch t₁ t₂ t₃ ⇉ switch t₁′ t₂′ t₃′
  ⇉/fst : ∀ {t t′} → t ⇉ t′ → fst t ⇉ fst t′
  ⇉/snd : ∀ {t t′} → t ⇉ t′ → snd t ⇉ snd t′
  ⇉/cons : ∀ {t₁ t₁′ t₂ t₂′} → t₁ ⇉ t₁′ → t₂ ⇉ t₂′ → cons t₁ t₂ ⇉ cons t₁′ t₂′
  ⇉/lam : ∀ {a t t′} → t ⇉ t′ → lam a t ⇉ lam a t′
  ⇉/app : ∀ {t₁ t₁′ t₂ t₂′} → t₁ ⇉ t₁′ → t₂ ⇉ t₂′ → app t₁ t₂ ⇉ app t₁′ t₂′
  ⇉/beta : ∀ {a t₁ t₁′ t₂ t₂′} → t₁ ⇉ t₁′ → t₂ ⇉ t₂′ → app (lam a t₁) t₂ ⇉ bind (t₂′ ∺ var) t₁′
  ⇉/fst-cons : ∀ {t₁ t₁′ t₂} → t₁ ⇉ t₁′ → fst (cons t₁ t₂) ⇉ t₁′
  ⇉/snd-cons : ∀ {t₁ t₂ t₂′} → t₂ ⇉ t₂′ → snd (cons t₁ t₂) ⇉ t₂′
  ⇉/switch-left : ∀ {t₁ t₂ t₃ t₁′ t₃′} → t₁ ⇉ t₁′ → t₃ ⇉ t₃′ → switch t₁ t₂ (left t₃) ⇉ app t₁′ t₃′
  ⇉/switch-right : ∀ {t₁ t₂ t₃ t₂′ t₃′} → t₂ ⇉ t₂′ → t₃ ⇉ t₃′ → switch t₁ t₂ (right t₃) ⇉ app t₂′ t₃′

⇉/refl : ∀ {t} → t ⇉ t
⇉/refl {var x} = ⇉/var
⇉/refl {elim t} = ⇉/elim ⇉/refl
⇉/refl {tt} = ⇉/tt
⇉/refl {left t} = ⇉/left ⇉/refl
⇉/refl {right t} = ⇉/right ⇉/refl
⇉/refl {switch t u v} = ⇉/switch ⇉/refl ⇉/refl ⇉/refl
⇉/refl {fst t} = ⇉/fst ⇉/refl
⇉/refl {snd t} = ⇉/snd ⇉/refl
⇉/refl {cons t u} = ⇉/cons ⇉/refl ⇉/refl
⇉/refl {lam a t} = ⇉/lam ⇉/refl
⇉/refl {app t u} = ⇉/app ⇉/refl ⇉/refl

⇉/map : ∀ σ {t t′} → t ⇉ t′ → map σ t ⇉ map σ t′
⇉/map σ ⇉/var = ⇉/var
⇉/map σ (⇉/elim s) = ⇉/elim (⇉/map σ s)
⇉/map σ ⇉/tt = ⇉/tt
⇉/map σ (⇉/left s) = ⇉/left (⇉/map σ s)
⇉/map σ (⇉/right s) = ⇉/right (⇉/map σ s)
⇉/map σ (⇉/switch s₁ s₂ s₃) = ⇉/switch (⇉/map σ s₁) (⇉/map σ s₂) (⇉/map σ s₃)
⇉/map σ (⇉/fst s) = ⇉/fst (⇉/map σ s)
⇉/map σ (⇉/snd s) = ⇉/snd (⇉/map σ s)
⇉/map σ (⇉/cons s₁ s₂) = ⇉/cons (⇉/map σ s₁) (⇉/map σ s₂)
⇉/map σ (⇉/lam s) = ⇉/lam (⇉/map (lift 1 σ) s)
⇉/map σ (⇉/app s₁ s₂) = ⇉/app (⇉/map σ s₁) (⇉/map σ s₂)
⇉/map σ (⇉/beta s₁ s₂) = subst (_ ⇉_)
  (reduce tree-rule refl)
  (⇉/beta (⇉/map (lift 1 σ) s₁) (⇉/map σ s₂))
⇉/map σ (⇉/fst-cons s) = ⇉/fst-cons (⇉/map σ s)
⇉/map σ (⇉/snd-cons s) = ⇉/snd-cons (⇉/map σ s)
⇉/map σ (⇉/switch-left s₁ s₂) = ⇉/switch-left (⇉/map σ s₁) (⇉/map σ s₂)
⇉/map σ (⇉/switch-right s₁ s₂) = ⇉/switch-right (⇉/map σ s₁) (⇉/map σ s₂)

⇉/raise : ∀ {σ σ′} → (∀ x → σ x ⇉ σ′ x) → (∀ x → raise 1 σ x ⇉ raise 1 σ′ x)
⇉/raise h zero = ⇉/var
⇉/raise h (suc x) = ⇉/map suc (h x)

⇉/bind : ∀ {σ σ′ t t′} → (∀ x → σ x ⇉ σ′ x) → t ⇉ t′ → bind σ t ⇉ bind σ′ t′
⇉/bind h ⇉/var = h _
⇉/bind h (⇉/elim s) = ⇉/elim (⇉/bind h s)
⇉/bind h ⇉/tt = ⇉/tt
⇉/bind h (⇉/fst s) = ⇉/fst (⇉/bind h s)
⇉/bind h (⇉/snd s) = ⇉/snd (⇉/bind h s)
⇉/bind h (⇉/cons s₁ s₂) = ⇉/cons (⇉/bind h s₁) (⇉/bind h s₂)
⇉/bind h (⇉/lam s) = ⇉/lam (⇉/bind (⇉/raise h) s)
⇉/bind h (⇉/app s₁ s₂) = ⇉/app (⇉/bind h s₁) (⇉/bind h s₂)
⇉/bind h (⇉/beta s₁ s₂) = subst (_ ⇉_)
  (reduce tree-rule refl)
  (⇉/beta (⇉/bind (⇉/raise h) s₁) (⇉/bind h s₂))
⇉/bind h (⇉/fst-cons s) = ⇉/fst-cons (⇉/bind h s)
⇉/bind h (⇉/snd-cons s) = ⇉/snd-cons (⇉/bind h s)
⇉/bind h (⇉/left s) = ⇉/left (⇉/bind h s)
⇉/bind h (⇉/right s) = ⇉/right (⇉/bind h s)
⇉/bind h (⇉/switch s₁ s₂ s₃) = ⇉/switch (⇉/bind h s₁) (⇉/bind h s₂) (⇉/bind h s₃)
⇉/bind h (⇉/switch-left s₁ s₂) = ⇉/switch-left (⇉/bind h s₁) (⇉/bind h s₂)
⇉/bind h (⇉/switch-right s₁ s₂) = ⇉/switch-right (⇉/bind h s₁) (⇉/bind h s₂)

⇉/sub : ∀ {t t′} → t ⇉ t′ → ∀ x → (t ∺ var) x ⇉ (t′ ∺ var) x
⇉/sub s zero = s
⇉/sub s (suc x) = ⇉/var

⇉/diamond : ∀ {t t₁′ t₂′} → t ⇉ t₁′ → t ⇉ t₂′ → ∃ λ t″ → (t₁′ ⇉ t″) × (t₂′ ⇉ t″)
⇉/diamond ⇉/var ⇉/var = _ , ⇉/var , ⇉/var
⇉/diamond (⇉/elim s₁) (⇉/elim s₂) =
  let _ , s₁′ , s₂′ = ⇉/diamond s₁ s₂
  in _ , ⇉/elim s₁′ , ⇉/elim s₂′
⇉/diamond ⇉/tt ⇉/tt = _ , ⇉/tt , ⇉/tt
⇉/diamond (⇉/fst s₁) (⇉/fst s₂) =
  let _ , s₁′ , s₂′ = ⇉/diamond s₁ s₂
  in _ , ⇉/fst s₁′ , ⇉/fst s₂′
⇉/diamond (⇉/snd s₁) (⇉/snd s₂) =
  let _ , s₁′ , s₂′ = ⇉/diamond s₁ s₂
  in _ , ⇉/snd s₁′ , ⇉/snd s₂′
⇉/diamond (⇉/fst (⇉/cons s₁ _)) (⇉/fst-cons s₂) =
  let _ , s₁ , s₂ = ⇉/diamond s₁ s₂
  in _ , ⇉/fst-cons s₁ , s₂
⇉/diamond (⇉/snd (⇉/cons _ s₁)) (⇉/snd-cons s₂) =
  let _ , s₁ , s₂ = ⇉/diamond s₁ s₂
  in _ , ⇉/snd-cons s₁ , s₂
⇉/diamond (⇉/fst-cons s₁) (⇉/fst (⇉/cons s₂ _)) =
  let _ , s₁ , s₂ = ⇉/diamond s₁ s₂
  in _ , s₁ , ⇉/fst-cons s₂
⇉/diamond (⇉/fst-cons s₁) (⇉/fst-cons s₂) = ⇉/diamond s₁ s₂
⇉/diamond (⇉/snd-cons s₁) (⇉/snd (⇉/cons _ s₂)) =
  let _ , s₁ , s₂ = ⇉/diamond s₁ s₂
  in _ , s₁ , ⇉/snd-cons s₂
⇉/diamond (⇉/snd-cons s₁) (⇉/snd-cons s₂) = ⇉/diamond s₁ s₂
⇉/diamond (⇉/cons s₁₁ s₁₂) (⇉/cons s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/cons s₁₁′ s₁₂′ , ⇉/cons s₂₁′ s₂₂′
⇉/diamond (⇉/lam s₁) (⇉/lam s₂) =
  let _ , s₁′ , s₂′ = ⇉/diamond s₁ s₂
  in _ , ⇉/lam s₁′ , ⇉/lam s₂′
⇉/diamond (⇉/app s₁₁ s₁₂) (⇉/app s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/app s₁₁′ s₁₂′ , ⇉/app s₂₁′ s₂₂′
⇉/diamond (⇉/beta s₁₁ s₁₂) (⇉/app (⇉/lam s₂₁) s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/bind (⇉/sub s₁₂′) s₁₁′ , ⇉/beta s₂₁′ s₂₂′
⇉/diamond (⇉/app (⇉/lam s₁₁) s₁₂) (⇉/beta s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/beta s₁₁′ s₁₂′ , ⇉/bind (⇉/sub s₂₂′) s₂₁′
⇉/diamond (⇉/beta s₁₁ s₁₂) (⇉/beta s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/bind (⇉/sub s₁₂′) s₁₁′ , ⇉/bind (⇉/sub s₂₂′) s₂₁′
⇉/diamond (⇉/left s₁) (⇉/left s₂) =
  let _ , s₁′ , s₂′ = ⇉/diamond s₁ s₂
  in _ , ⇉/left s₁′ , ⇉/left s₂′
⇉/diamond (⇉/right s₁) (⇉/right s₂) =
  let _ , s₁′ , s₂′ = ⇉/diamond s₁ s₂
  in _ , ⇉/right s₁′ , ⇉/right s₂′
⇉/diamond (⇉/switch s₁₁ s₁₂ s₁₃) (⇉/switch s₂₁ s₂₂ s₂₃) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
      _ , s₁₃′ , s₂₃′ = ⇉/diamond s₁₃ s₂₃
  in _ , ⇉/switch s₁₁′ s₁₂′ s₁₃′ , ⇉/switch s₂₁′ s₂₂′ s₂₃′
⇉/diamond (⇉/switch s₁₁ _ (⇉/left s₁₂)) (⇉/switch-left s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/switch-left s₁₁′ s₁₂′ , ⇉/app s₂₁′ s₂₂′
⇉/diamond (⇉/switch _ s₁₁ (⇉/right s₁₂)) (⇉/switch-right s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/switch-right s₁₁′ s₁₂′ , ⇉/app s₂₁′ s₂₂′
⇉/diamond (⇉/switch-left s₁₁ s₁₂) (⇉/switch s₂₁ _ (⇉/left s₂₂)) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/app s₁₁′ s₁₂′ , ⇉/switch-left s₂₁′ s₂₂′
⇉/diamond (⇉/switch-left s₁₁ s₁₂) (⇉/switch-left s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/app s₁₁′ s₁₂′ , ⇉/app s₂₁′ s₂₂′
⇉/diamond (⇉/switch-right s₁₁ s₁₂) (⇉/switch _ s₂₁ (⇉/right s₂₂)) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/app s₁₁′ s₁₂′ , ⇉/switch-right s₂₁′ s₂₂′
⇉/diamond (⇉/switch-right s₁₁ s₁₂) (⇉/switch-right s₂₁ s₂₂) =
  let _ , s₁₁′ , s₂₁′ = ⇉/diamond s₁₁ s₂₁
      _ , s₁₂′ , s₂₂′ = ⇉/diamond s₁₂ s₂₂
  in _ , ⇉/app s₁₁′ s₁₂′ , ⇉/app s₂₁′ s₂₂′

_⇉*_ = Star _⇉_

⇉/strong : ∀ {t t₁′ t₂′} → t ⇉* t₁′ → t ⇉ t₂′ → ∃ λ t″ → (t₁′ ⇉ t″) × (t₂′ ⇉* t″)
⇉/strong ε s = _ , s , ε
⇉/strong (s₁ ◅ s₂) s₃ =
  let _ , s₁ , s₃ = ⇉/diamond s₁ s₃
      _ , s₂ , s₁ = ⇉/strong s₂ s₁
  in _ , s₂ , s₃ ◅ s₁

⇉/global : ∀ {t t₁′ t₂′} → t ⇉* t₁′ → t ⇉* t₂′ → ∃ λ t″ → (t₁′ ⇉* t″) × (t₂′ ⇉* t″)
⇉/global s ε = _ , ε , s
⇉/global s₁ (s₂ ◅ s₃) =
  let _ , s₁ , s₂ = ⇉/strong s₁ s₂
      _ , s₂ , s₃ = ⇉/global s₂ s₃
  in _ , s₁ ◅ s₂ , s₃

data _→¹_ : Term → Term → Set where
  →¹/elim : ∀ {t t′} → t →¹ t′ → elim t →¹ elim t′
  →¹/left : ∀ {t t′} → t →¹ t′ → left t →¹ left t′
  →¹/right : ∀ {t t′} → t →¹ t′ → right t →¹ right t′
  →¹/switch₁ : ∀ {t₁ t₂ t₃ t₁′} → t₁ →¹ t₁′ → switch t₁ t₂ t₃ →¹ switch t₁′ t₂ t₃
  →¹/switch₂ : ∀ {t₁ t₂ t₃ t₂′} → t₂ →¹ t₂′ → switch t₁ t₂ t₃ →¹ switch t₁ t₂′ t₃
  →¹/switch₃ : ∀ {t₁ t₂ t₃ t₃′} → t₃ →¹ t₃′ → switch t₁ t₂ t₃ →¹ switch t₁ t₂ t₃′
  →¹/fst : ∀ {t t′} → t →¹ t′ → fst t →¹ fst t′
  →¹/snd : ∀ {t t′} → t →¹ t′ → snd t →¹ snd t′
  →¹/consₗ : ∀ {t₁ t₁′ t₂} → t₁ →¹ t₁′ → cons t₁ t₂ →¹ cons t₁′ t₂
  →¹/consᵣ : ∀ {t₁ t₂ t₂′} → t₂ →¹ t₂′ → cons t₁ t₂ →¹ cons t₁ t₂′
  →¹/lam : ∀ {a t t′} → t →¹ t′ → lam a t →¹ lam a t′
  →¹/appₗ : ∀ {t₁ t₁′ t₂} → t₁ →¹ t₁′ → app t₁ t₂ →¹ app t₁′ t₂
  →¹/appᵣ : ∀ {t₁ t₂ t₂′} → t₂ →¹ t₂′ → app t₁ t₂ →¹ app t₁ t₂′
  →¹/beta : ∀ {a t₁ t₂} → app (lam a t₁) t₂ →¹ bind (t₂ ∺ var) t₁
  →¹/fst-cons : ∀ {t₁ t₂} → fst (cons t₁ t₂) →¹ t₁
  →¹/snd-cons : ∀ {t₁ t₂} → snd (cons t₁ t₂) →¹ t₂
  →¹/switch-left : ∀ {t₁ t₂ t₃} → switch t₁ t₂ (left t₃) →¹ app t₁ t₃
  →¹/switch-right : ∀ {t₁ t₂ t₃} → switch t₁ t₂ (right t₃) →¹ app t₂ t₃

→¹/map : ∀ σ {t t′} → t →¹ t′ → map σ t →¹ map σ t′
→¹/map σ (→¹/elim s) = →¹/elim (→¹/map σ s)
→¹/map σ (→¹/fst s) = →¹/fst (→¹/map σ s)
→¹/map σ (→¹/snd s) = →¹/snd (→¹/map σ s)
→¹/map σ (→¹/consₗ s) = →¹/consₗ (→¹/map σ s)
→¹/map σ (→¹/consᵣ s) = →¹/consᵣ (→¹/map σ s)
→¹/map σ (→¹/lam s) = →¹/lam (→¹/map (lift 1 σ) s)
→¹/map σ (→¹/appₗ s) = →¹/appₗ (→¹/map σ s)
→¹/map σ (→¹/appᵣ s) = →¹/appᵣ (→¹/map σ s)
→¹/map σ →¹/beta = subst (map σ (app (lam _ _) _) →¹_) (reduce tree-rule refl) →¹/beta
→¹/map σ →¹/fst-cons = →¹/fst-cons
→¹/map σ →¹/snd-cons = →¹/snd-cons
→¹/map σ (→¹/left s) = →¹/left (→¹/map σ s)
→¹/map σ (→¹/right s) = →¹/right (→¹/map σ s)
→¹/map σ (→¹/switch₁ s) = →¹/switch₁ (→¹/map σ s)
→¹/map σ (→¹/switch₂ s) = →¹/switch₂ (→¹/map σ s)
→¹/map σ (→¹/switch₃ s) = →¹/switch₃ (→¹/map σ s)
→¹/map σ →¹/switch-left = →¹/switch-left
→¹/map σ →¹/switch-right = →¹/switch-right

→¹-to-⇉ : ∀ {t t′} → t →¹ t′ → t ⇉ t′
→¹-to-⇉ (→¹/elim s) = ⇉/elim (→¹-to-⇉ s)
→¹-to-⇉ (→¹/fst s) = ⇉/fst (→¹-to-⇉ s)
→¹-to-⇉ (→¹/snd s) = ⇉/snd (→¹-to-⇉ s)
→¹-to-⇉ (→¹/consₗ s) = ⇉/cons (→¹-to-⇉ s) ⇉/refl
→¹-to-⇉ (→¹/consᵣ s) = ⇉/cons ⇉/refl (→¹-to-⇉ s)
→¹-to-⇉ (→¹/lam s) = ⇉/lam (→¹-to-⇉ s)
→¹-to-⇉ (→¹/appₗ s) = ⇉/app (→¹-to-⇉ s) ⇉/refl
→¹-to-⇉ (→¹/appᵣ s) = ⇉/app ⇉/refl (→¹-to-⇉ s)
→¹-to-⇉ →¹/beta = ⇉/beta ⇉/refl ⇉/refl
→¹-to-⇉ →¹/fst-cons = ⇉/fst-cons ⇉/refl
→¹-to-⇉ →¹/snd-cons = ⇉/snd-cons ⇉/refl
→¹-to-⇉ (→¹/left s) = ⇉/left (→¹-to-⇉ s)
→¹-to-⇉ (→¹/right s) = ⇉/right (→¹-to-⇉ s)
→¹-to-⇉ (→¹/switch₁ s) = ⇉/switch (→¹-to-⇉ s) ⇉/refl ⇉/refl
→¹-to-⇉ (→¹/switch₂ s) = ⇉/switch ⇉/refl (→¹-to-⇉ s) ⇉/refl
→¹-to-⇉ (→¹/switch₃ s) = ⇉/switch ⇉/refl ⇉/refl (→¹-to-⇉ s)
→¹-to-⇉ →¹/switch-left = ⇉/switch-left ⇉/refl ⇉/refl
→¹-to-⇉ →¹/switch-right = ⇉/switch-right ⇉/refl ⇉/refl

_→¹*_ = Star _→¹_

⇉-to-→¹ : ∀ {t t′} → t ⇉ t′ → t →¹* t′
⇉-to-→¹ ⇉/var = ε
⇉-to-→¹ ⇉/tt = ε
⇉-to-→¹ (⇉/elim s) = gmap _ →¹/elim (⇉-to-→¹ s)
⇉-to-→¹ (⇉/lam s) = gmap _ →¹/lam (⇉-to-→¹ s)
⇉-to-→¹ (⇉/app s₁ s₂) =
  gmap _ →¹/appᵣ (⇉-to-→¹ s₂) ◅◅
  gmap _ →¹/appₗ (⇉-to-→¹ s₁)
⇉-to-→¹ (⇉/beta s₁ s₂) =
  gmap _ →¹/appᵣ (⇉-to-→¹ s₂) ◅◅
  gmap _ (→¹/appₗ ∘ →¹/lam) (⇉-to-→¹ s₁) ◅◅
  return →¹/beta
⇉-to-→¹ (⇉/fst s) = gmap _ →¹/fst (⇉-to-→¹ s)
⇉-to-→¹ (⇉/snd s) = gmap _ →¹/snd (⇉-to-→¹ s)
⇉-to-→¹ (⇉/cons s₁ s₂) =
  gmap _ →¹/consₗ (⇉-to-→¹ s₁) ◅◅
  gmap _ →¹/consᵣ (⇉-to-→¹ s₂)
⇉-to-→¹ (⇉/fst-cons s) = →¹/fst-cons ◅ ⇉-to-→¹ s
⇉-to-→¹ (⇉/snd-cons s) = →¹/snd-cons ◅ ⇉-to-→¹ s
⇉-to-→¹ (⇉/left s) = gmap _ →¹/left (⇉-to-→¹ s)
⇉-to-→¹ (⇉/right s) = gmap _ →¹/right (⇉-to-→¹ s)
⇉-to-→¹ (⇉/switch s₁ s₂ s₃) =
  gmap _ →¹/switch₁ (⇉-to-→¹ s₁) ◅◅
  gmap _ →¹/switch₂ (⇉-to-→¹ s₂) ◅◅
  gmap _ →¹/switch₃ (⇉-to-→¹ s₃)
⇉-to-→¹ (⇉/switch-left s₁ s₂) =
  gmap _ →¹/switch₁ (⇉-to-→¹ s₁) ◅◅
  gmap _ (→¹/switch₃ ∘ →¹/left) (⇉-to-→¹ s₂) ◅◅
  return →¹/switch-left
⇉-to-→¹ (⇉/switch-right s₁ s₂) =
  gmap _ →¹/switch₂ (⇉-to-→¹ s₁) ◅◅
  gmap _ (→¹/switch₃ ∘ →¹/right) (⇉-to-→¹ s₂) ◅◅
  return →¹/switch-right

→¹/global : ∀ {t t₁′ t₂′} → t →¹* t₁′ → t →¹* t₂′ → ∃ λ t″ → (t₁′ →¹* t″) × (t₂′ →¹* t″)
→¹/global s₁ s₂ =
  let _ , s₁ , s₂ = ⇉/global (Star.map →¹-to-⇉ s₁) (Star.map →¹-to-⇉ s₂)
  in _ , (s₁ >>= ⇉-to-→¹) , (s₂ >>= ⇉-to-→¹)
