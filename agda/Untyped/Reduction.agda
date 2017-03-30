module Untyped.Reduction where

open import Agda.Builtin.Reflection using (unify)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (∃; _×_; _,_)
open import Data.Star as Star using (Star; ε; _◅_; _◅◅_; gmap; return; _>>=_)
open import Function using (_∘_; flip)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import Binding.Tree
open import Reflection.Rewriting
open import Reflection.Rewriting.Tree

open import Untyped.Syntax

data _⇉_ : Term → Term → Set where
  ⇉/var : ∀ {x} → var x ⇉ var x
  ⇉/lam : ∀ {t t′} → t ⇉ t′ → lam t ⇉ lam t′
  ⇉/app : ∀ {t₁ t₁′ t₂ t₂′} → t₁ ⇉ t₁′ → t₂ ⇉ t₂′ → app t₁ t₂ ⇉ app t₁′ t₂′
  ⇉/beta : ∀ {t₁ t₁′ t₂ t₂′} → t₁ ⇉ t₁′ → t₂ ⇉ t₂′ → app (lam t₁) t₂ ⇉ bind (t₂′ ∺ var) t₁′

⇉/refl : ∀ {t} → t ⇉ t
⇉/refl {var x} = ⇉/var
⇉/refl {lam _} = ⇉/lam ⇉/refl
⇉/refl {app _ _} = ⇉/app ⇉/refl ⇉/refl

⇉/map : ∀ σ {t t′} → t ⇉ t′ → map σ t ⇉ map σ t′
⇉/map σ ⇉/var = ⇉/var
⇉/map σ (⇉/lam s) = ⇉/lam (⇉/map (lift 1 σ) s)
⇉/map σ (⇉/app s₁ s₂) = ⇉/app (⇉/map σ s₁) (⇉/map σ s₂)
⇉/map σ (⇉/beta s₁ s₂) = subst (_ ⇉_)
  (reduce tree-rule refl)
  (⇉/beta (⇉/map (lift 1 σ) s₁) (⇉/map σ s₂))

⇉/raise : ∀ {σ σ′} → (∀ x → σ x ⇉ σ′ x) → (∀ x → raise 1 σ x ⇉ raise 1 σ′ x)
⇉/raise h zero = ⇉/var
⇉/raise h (suc x) = ⇉/map suc (h x)

⇉/bind : ∀ {σ σ′ t t′} → (∀ x → σ x ⇉ σ′ x) → t ⇉ t′ → bind σ t ⇉ bind σ′ t′
⇉/bind h ⇉/var = h _
⇉/bind h (⇉/lam s) = ⇉/lam (⇉/bind (⇉/raise h) s)
⇉/bind h (⇉/app s₁ s₂) = ⇉/app (⇉/bind h s₁) (⇉/bind h s₂)
⇉/bind h (⇉/beta s₁ s₂) = subst (_ ⇉_)
  (reduce tree-rule refl)
  (⇉/beta (⇉/bind (⇉/raise h) s₁) (⇉/bind h s₂))

⇉/sub : ∀ {t t′} → t ⇉ t′ → ∀ x → (t ∺ var) x ⇉ (t′ ∺ var) x
⇉/sub s zero = s
⇉/sub s (suc n) = ⇉/var

⇉/diamond : ∀ {t t₁′ t₂′} → t ⇉ t₁′ → t ⇉ t₂′ → ∃ λ t″ → (t₁′ ⇉ t″) × (t₂′ ⇉ t″)
⇉/diamond ⇉/var ⇉/var = _ , ⇉/var , ⇉/var
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
  →¹/lam : ∀ {t t′} → t →¹ t′ → lam t →¹ lam t′
  →¹/appₗ : ∀ {t₁ t₁′ t₂} → t₁ →¹ t₁′ → app t₁ t₂ →¹ app t₁′ t₂
  →¹/appᵣ : ∀ {t₁ t₂ t₂′} → t₂ →¹ t₂′ → app t₁ t₂ →¹ app t₁ t₂′
  →¹/beta : ∀ {t₁ t₂} → app (lam t₁) t₂ →¹ bind (t₂ ∺ var) t₁

→¹-to-⇉ : ∀ {t t′} → t →¹ t′ → t ⇉ t′
→¹-to-⇉ (→¹/lam s) = ⇉/lam (→¹-to-⇉ s)
→¹-to-⇉ (→¹/appₗ s) = ⇉/app (→¹-to-⇉ s) ⇉/refl
→¹-to-⇉ (→¹/appᵣ s) = ⇉/app ⇉/refl (→¹-to-⇉ s)
→¹-to-⇉ →¹/beta = ⇉/beta ⇉/refl ⇉/refl

_→¹*_ = Star _→¹_

⇉-to-→¹ : ∀ {t t′} → t ⇉ t′ → t →¹* t′
⇉-to-→¹ ⇉/var = ε
⇉-to-→¹ (⇉/lam s) = gmap lam →¹/lam (⇉-to-→¹ s)
⇉-to-→¹ (⇉/app s₁ s₂) =
  gmap (app _) →¹/appᵣ (⇉-to-→¹ s₂) ◅◅
  gmap (flip app _) →¹/appₗ (⇉-to-→¹ s₁)
⇉-to-→¹ (⇉/beta s₁ s₂) =
  gmap (app _) →¹/appᵣ (⇉-to-→¹ s₂) ◅◅
  gmap (flip app _ ∘ lam) (→¹/appₗ ∘ →¹/lam) (⇉-to-→¹ s₁) ◅◅
  return →¹/beta

→¹/global : ∀ {t t₁′ t₂′} → t →¹* t₁′ → t →¹* t₂′ → ∃ λ t″ → (t₁′ →¹* t″) × (t₂′ →¹* t″)
→¹/global s₁ s₂ =
  let _ , s₁ , s₂ = ⇉/global (Star.map →¹-to-⇉ s₁) (Star.map →¹-to-⇉ s₂)
  in _ , (s₁ >>= ⇉-to-→¹) , (s₂ >>= ⇉-to-→¹)
