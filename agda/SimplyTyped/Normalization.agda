module SimplyTyped.Normalization where

open import Data.Empty using (⊥)
open import Data.Product using (∃; _×_; _,_)
open import Data.List.All using (_∷_; [])
open import Data.List.Any using (here; there)
open import Data.Nat using (_+_)
open import Data.Nat.Properties.Simple using (+-assoc; +-suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Star using (ε; _◅_; _◅◅_; gmap; return)
open import Data.Unit using (⊤)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (refl; cong; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import Binding.Tree
open import Reflection.Rewriting
open import Reflection.Rewriting.Nat
open import Reflection.Rewriting.Tree

open import SimplyTyped.Syntax
open import SimplyTyped.Reduction
open import SimplyTyped.Typing

mutual
  data Nm : Term → Set where
    nm/tt : Nm tt
    nm/left : ∀ {t} → Nm t → Nm (left t)
    nm/right : ∀ {t} → Nm t → Nm (right t)
    nm/cons : ∀ {t u} → Nm t → Nm u → Nm (cons t u)
    nm/lam : ∀ {a t} → Nm t → Nm (lam a t)
    nm/ne : ∀ {t} → Ne t → Nm t

  data Ne : Term → Set where
    ne/var : ∀ {x} → Ne (var x)
    ne/elim : ∀ {t} → Nm t → Ne (elim t)
    ne/switch : ∀ {t u v} → Nm t → Nm u → Ne v → Ne (switch t u v)
    ne/fst : ∀ {t} → Ne t → Ne (fst t)
    ne/snd : ∀ {t} → Ne t → Ne (snd t)
    ne/app : ∀ {t u} → Ne t → Nm u → Ne (app t u)

mutual
  nm/map : ∀ σ {t} → Nm t → Nm (map σ t)
  nm/map σ nm/tt = nm/tt
  nm/map σ (nm/cons nm₁ nm₂) = nm/cons (nm/map σ nm₁) (nm/map σ nm₂)
  nm/map σ (nm/lam nm) = nm/lam (nm/map (lift 1 σ) nm)
  nm/map σ (nm/ne ne) = nm/ne (ne/map σ ne)
  nm/map σ (nm/left nm) = nm/left (nm/map σ nm)
  nm/map σ (nm/right nm) = nm/right (nm/map σ nm)

  ne/map : ∀ σ {t} → Ne t → Ne (map σ t)
  ne/map σ ne/var = ne/var
  ne/map σ (ne/elim nm) = ne/elim (nm/map σ nm)
  ne/map σ (ne/fst ne) = ne/fst (ne/map σ ne)
  ne/map σ (ne/snd ne) = ne/snd (ne/map σ ne)
  ne/map σ (ne/app ne nm) = ne/app (ne/map σ ne) (nm/map σ nm)
  ne/map σ (ne/switch nm₁ nm₂ ne) = ne/switch (nm/map σ nm₁) (nm/map σ nm₂) (ne/map σ ne)

record _⇓ᴺᴹ t : Set where
  constructor _,_
  field
    {t′} : Term
    steps : t →¹* t′
    normal : Nm t′

record _⇓ᴺᴱ t : Set where
  constructor _,_
  field
    {t′} : Term
    steps : t →¹* t′
    neutral : Ne t′

mutual
  ⟦_∶_⟧ : Term → Type → Set
  ⟦ t ∶ a ⟧ = t ⇓ᴺᴱ ⊎ t ⇓ᴺᴹ × ⟦ t ∶ a ⟧′

  ⟦_∶_⟧′ : Term → Type → Set
  ⟦ t ∶ bot ⟧′ = ⊥
  ⟦ t ∶ top ⟧′ = ⊤
  ⟦ t ∶ choice a b ⟧′ = (∃ λ u → (t →¹* left u) × ⟦ u ∶ a ⟧) ⊎ (∃ λ u → (t →¹* right u) × ⟦ u ∶ b ⟧)
  ⟦ t ∶ pair a b ⟧′ = ⟦ fst t ∶ a ⟧ × ⟦ snd t ∶ b ⟧
  ⟦ t ∶ arr a b ⟧′ = ∀ {u} n → ⟦ u ∶ a ⟧ → ⟦ app (map (n +_) t) u ∶ b ⟧

⇓ᴺᴹ/rel : ∀ {a t} → ⟦ t ∶ a ⟧ → t ⇓ᴺᴹ
⇓ᴺᴹ/rel (inj₁ (ss , ne)) = ss , nm/ne ne
⇓ᴺᴹ/rel (inj₂ (nm , _)) = nm

mutual
  rel/→¹ : ∀ {a t t′} → t →¹ t′ → ⟦ t′ ∶ a ⟧ → ⟦ t ∶ a ⟧
  rel/→¹ s (inj₁ (ss , ne)) = inj₁ (s ◅ ss , ne)
  rel/→¹ s (inj₂ ((ss , nm) , r′)) = inj₂ ((s ◅ ss , nm) , rel′/→¹ s r′)

  rel′/→¹ : ∀ {a t t′} → t →¹ t′ → ⟦ t′ ∶ a ⟧′ → ⟦ t ∶ a ⟧′
  rel′/→¹ {bot} s r = r
  rel′/→¹ {top} s r = r
  rel′/→¹ {choice a b} s (inj₁ (_ , ss , r)) = inj₁ (_ , s ◅ ss , r)
  rel′/→¹ {choice a b} s (inj₂ (_ , ss , r)) = inj₂ (_ , s ◅ ss , r)
  rel′/→¹ {pair a b} s (r₁ , r₂) = rel/→¹ (→¹/fst s) r₁ , rel/→¹ (→¹/snd s) r₂
  rel′/→¹ {arr a b} s r₁ n r₂ = rel/→¹ (→¹/appₗ (→¹/map (n +_) s)) (r₁ n r₂)

rel/→¹* : ∀ {a t t′} → t →¹* t′ → ⟦ t′ ∶ a ⟧ → ⟦ t ∶ a ⟧
rel/→¹* ε = id
rel/→¹* (s ◅ ss) = rel/→¹ s ∘ rel/→¹* ss

mutual
  rel/+ : ∀ n {a t} → ⟦ t ∶ a ⟧ → ⟦ map (n +_) t ∶ a ⟧
  rel/+ n (inj₁ (ss , ne)) = inj₁ (gmap _ (→¹/map (n +_)) ss , ne/map (n +_) ne)
  rel/+ n (inj₂ ((ss , nm) , r′)) = inj₂ ((gmap _ (→¹/map (n +_)) ss , nm/map (n +_) nm) , rel′/+ n r′)

  rel′/+ : ∀ n {a t} → ⟦ t ∶ a ⟧′ → ⟦ map (n +_) t ∶ a ⟧′
  rel′/+ n {bot} r = r
  rel′/+ n {top} r = r
  rel′/+ n {choice a b} (inj₁ (_ , ss , r)) = inj₁ (_ , gmap _ (→¹/map (n +_)) ss , rel/+ n r)
  rel′/+ n {choice a b} (inj₂ (_ , ss , r)) = inj₂ (_ , gmap _ (→¹/map (n +_)) ss , rel/+ n r)
  rel′/+ n {pair a b} (r₁ , r₂) = rel/+ n r₁ , rel/+ n r₂
  rel′/+ n {arr a b} {t} r₁ m r₂ =
    subst
      (λ x → ⟦ app x _ ∶ _ ⟧)
      (reduce (ℕ-rule & tree-rule) refl)
      (r₁ (m + n) r₂)

rel/app : ∀ {a b t u} → ⟦ t ∶ arr a b ⟧ → ⟦ u ∶ a ⟧ → ⟦ app t u ∶ b ⟧
rel/app (inj₁ (ss , ne)) r =
  let ss′ , nm = ⇓ᴺᴹ/rel r
  in inj₁ (gmap _ →¹/appₗ ss ◅◅ gmap _ →¹/appᵣ ss′ , ne/app ne nm)
rel/app (inj₂ (nm , p′)) r = subst (λ x → ⟦ app x _ ∶ _ ⟧) (reduce tree-rule refl) (p′ 0 r)

rel/⊢ : ∀ {Γ σ t a} → (∀ {x a} → Γ [ x ]= a → ⟦ σ x ∶ a ⟧) → Γ ⊢ t ∶ a → ⟦ bind σ t ∶ a ⟧
rel/⊢ h (⊢/var x) = h x
rel/⊢ h (⊢/elim d) =
  let ss , nm = ⇓ᴺᴹ/rel (rel/⊢ h d)
  in inj₁ (gmap _ →¹/elim ss , ne/elim nm)
rel/⊢ h ⊢/tt = inj₂ ((ε , nm/tt) , _)
rel/⊢ h (⊢/left d) =
  let r = rel/⊢ h d
      ss , nm = ⇓ᴺᴹ/rel r
  in inj₂ ((gmap _ →¹/left ss , nm/left nm) , inj₁ (_ , ε , r))
rel/⊢ h (⊢/right d) =
  let r = rel/⊢ h d
      ss , nm = ⇓ᴺᴹ/rel r
  in inj₂ ((gmap _ →¹/right ss , nm/right nm) , inj₂ (_ , ε , r))
rel/⊢ h (⊢/switch d₁ d₂ d₃) with rel/⊢ h d₃
... | inj₁ (ss₃ , ne₃) =
  let r₁ = rel/⊢ h d₁
      r₂ = rel/⊢ h d₂
      ss₁ , nm₁ = ⇓ᴺᴹ/rel r₁
      ss₂ , nm₂ = ⇓ᴺᴹ/rel r₂
  in inj₁ (gmap _ →¹/switch₁ ss₁ ◅◅ gmap _ →¹/switch₂ ss₂ ◅◅ gmap _ →¹/switch₃ ss₃ , ne/switch nm₁ nm₂ ne₃)
... | inj₂ (_ , inj₁ (_ , ss , r)) = rel/→¹* (gmap _ →¹/switch₃ ss ◅◅ return →¹/switch-left) (rel/app (rel/⊢ h d₁) r)
... | inj₂ (_ , inj₂ (_ , ss , r)) = rel/→¹* (gmap _ →¹/switch₃ ss ◅◅ return →¹/switch-right) (rel/app (rel/⊢ h d₂) r)
rel/⊢ h (⊢/fst d) with rel/⊢ h d
rel/⊢ h (⊢/fst d) | inj₁ (ss , ne) = inj₁ (gmap _ →¹/fst ss , ne/fst ne)
rel/⊢ h (⊢/fst d) | inj₂ (_ , r , _) = r
rel/⊢ h (⊢/snd d) with rel/⊢ h d
rel/⊢ h (⊢/snd d) | inj₁ (ss , ne) = inj₁ (gmap _ →¹/snd ss , ne/snd ne)
rel/⊢ h (⊢/snd d) | inj₂ (_ , _ , r) = r
rel/⊢ h (⊢/cons d₁ d₂) =
  let r₁ = rel/⊢ h d₁
      r₂ = rel/⊢ h d₂
      (ss₁ , nm₁) = ⇓ᴺᴹ/rel r₁
      (ss₂ , nm₂) = ⇓ᴺᴹ/rel r₂
  in inj₂ ((gmap _ →¹/consₗ ss₁ ◅◅ gmap _ →¹/consᵣ ss₂ , nm/cons nm₁ nm₂)
   , rel/→¹ →¹/fst-cons r₁
   , rel/→¹ →¹/snd-cons r₂)
rel/⊢ {σ = σ} h (⊢/lam {t = t} d) =
  let (ss , nm) = ⇓ᴺᴹ/rel (rel/⊢
        (λ where
          here → inj₁ (ε , ne/var)
          (there x) → rel/+ 1 (h x))
        d)
  in inj₂ ((gmap _ →¹/lam ss , nm/lam nm) , λ {u} n p →
    let d′ = rel/⊢
          {σ = u ∺ map (n +_) ∘ σ}
          (λ where
            here → p
            (there x) → rel/+ n (h x))
          d
    in rel/→¹ →¹/beta (subst ⟦_∶ _ ⟧ (reduce tree-rule refl) d′))
rel/⊢ h (⊢/app d₁ d₂) = rel/app (rel/⊢ h d₁) (rel/⊢ h d₂)

Normal : Term → Set
Normal t = ∀ {t′} → ¬ t →¹ t′

record _⇓ t : Set where
  constructor _,_
  field
    {t′} : Term
    steps : t →¹* t′
    normal : Normal t′

mutual
  normal/nm : ∀ {t} → Nm t → Normal t
  normal/nm nm/tt ()
  normal/nm (nm/left nm) (→¹/left s) = normal/nm nm s
  normal/nm (nm/right nm) (→¹/right s) = normal/nm nm s
  normal/nm (nm/cons nm₁ nm₂) (→¹/consₗ s) = normal/nm nm₁ s
  normal/nm (nm/cons nm₁ nm₂) (→¹/consᵣ s) = normal/nm nm₂ s
  normal/nm (nm/lam nm) (→¹/lam s) = normal/nm nm s
  normal/nm (nm/ne ne) s = normal/ne ne s

  normal/ne : ∀ {t} → Ne t → Normal t
  normal/ne ne/var ()
  normal/ne (ne/elim nm) (→¹/elim s) = normal/nm nm s
  normal/ne (ne/switch nm₁ nm₂ ne) (→¹/switch₁ s) = normal/nm nm₁ s
  normal/ne (ne/switch nm₁ nm₂ ne) (→¹/switch₂ s) = normal/nm nm₂ s
  normal/ne (ne/switch nm₁ nm₂ ne) (→¹/switch₃ s) = normal/ne ne s
  normal/ne (ne/switch nm₁ nm₂ ()) →¹/switch-left
  normal/ne (ne/switch nm₁ nm₂ ()) →¹/switch-right
  normal/ne (ne/fst ne) (→¹/fst s) = normal/ne ne s
  normal/ne (ne/fst ()) →¹/fst-cons
  normal/ne (ne/snd ne) (→¹/snd s) = normal/ne ne s
  normal/ne (ne/snd ()) →¹/snd-cons
  normal/ne (ne/app ne nm) (→¹/appₗ s) = normal/ne ne s
  normal/ne (ne/app ne nm) (→¹/appᵣ s) = normal/nm nm s
  normal/ne (ne/app () nm) →¹/beta

⇓ᴺᴹ-to-⇓ : ∀ {t} → t ⇓ᴺᴹ → t ⇓
⇓ᴺᴹ-to-⇓ (ss , nm) = ss , normal/nm nm

⇓/⊢ : ∀ {Γ t a} → Γ ⊢ t ∶ a → t ⇓
⇓/⊢ = subst _⇓ (reduce tree-rule refl)
    ∘ ⇓ᴺᴹ-to-⇓
    ∘ ⇓ᴺᴹ/rel
    ∘ rel/⊢ λ {x} _ → inj₁ (ε , ne/var {x})
