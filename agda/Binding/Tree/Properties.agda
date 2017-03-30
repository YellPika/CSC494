module Binding.Tree.Properties where

open import Data.List.All using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
open        Relation.Binary.PropositionalEquality.≡-Reasoning

open import Binding.Tree

∺-dist : ∀ {A B : Set} (f : A → B) x xs → f ∘ (x ∺ xs) ≗ f x ∺ f ∘ xs
∺-dist f x xs zero = refl
∺-dist f x xs (suc n) = refl

∺-cong : ∀ {A : Set} {xs ys} (x : A) → xs ≗ ys → x ∺ xs ≗ x ∺ ys
∺-cong x h zero = refl
∺-cong x h (suc n) = h n

lift-cong : ∀ {σ τ} n → σ ≗ τ → lift n σ ≗ lift n τ
lift-cong zero h x = h x
lift-cong (suc n) h = ∺-cong zero (cong suc ∘ lift-cong n h)

mutual
  map-cong : ∀ {F σ τ} → σ ≗ τ → map {F} σ ≗ map τ
  map-cong h (var x) = cong var (h x)
  map-cong h (op p ts) = cong (op p) (map*-cong h ts)

  map*-cong : ∀ {F σ τ ns} → σ ≗ τ → map* {F} σ {ns} ≗ map* τ
  map*-cong h [] = refl
  map*-cong h (t ∷[ n ] ts) = cong₂ _∷_ (map-cong (lift-cong n h) t) (map*-cong h ts)

raise-cong : ∀ {F σ τ} n → σ ≗ τ → raise {F} n σ ≗ raise n τ
raise-cong zero h x = h x
raise-cong (suc n) h = ∺-cong (var zero) (cong (map suc) ∘ raise-cong n h)

mutual
  bind-cong : ∀ {F σ τ} → σ ≗ τ → bind {F} σ ≗ bind τ
  bind-cong h (var x) = h x
  bind-cong h (op p ts) = cong (op p) (bind*-cong h ts)

  bind*-cong : ∀ {F σ τ ns} → σ ≗ τ → bind* {F} σ {ns} ≗ bind* τ
  bind*-cong h [] = refl
  bind*-cong h (t ∷[ n ] ts) = cong₂ _∷_ (bind-cong (raise-cong n h) t) (bind*-cong h ts)

lift-id : ∀ n → lift n id ≗ id
lift-id zero x = refl
lift-id (suc n) zero = refl
lift-id (suc n) (suc x) = cong suc (lift-id n x)

mutual
  map-id : ∀ {F} → map {F} id ≗ id
  map-id (var x) = refl
  map-id (op p ts) = cong (op p) (map*-id ts)

  map*-id : ∀ {F ns} → map* {F} id {ns} ≗ id
  map*-id [] = refl
  map*-id (t ∷[ n ] ts) =
    cong₂ _∷_
      (begin
        map (lift n id) t ≡⟨ map-cong (lift-id n) t ⟩
        map id t          ≡⟨ map-id t ⟩
        t                 ∎)
      (map*-id ts)

raise-id : ∀ {F} n → raise {F} n var ≗ var
raise-id zero x = refl
raise-id (suc n) zero = refl
raise-id (suc n) (suc x) = cong (map suc) (raise-id n x)

mutual
  bind-id : ∀ {F} → bind {F} var ≗ id
  bind-id (var x) = refl
  bind-id (op p ts) = cong (op p) (bind*-id ts)

  bind*-id : ∀ {F ns} → bind* {F} var {ns} ≗ id
  bind*-id [] = refl
  bind*-id (t ∷[ n ] ts) =
    cong₂ _∷_
      (begin
        bind (raise n var) t ≡⟨ bind-cong (raise-id n) t ⟩
        bind var t           ≡⟨ bind-id t ⟩
        t                    ∎)
      (bind*-id ts)

lift-∘ : ∀ n σ τ → lift n (σ ∘ τ) ≗ lift n σ ∘ lift n τ
lift-∘ zero σ τ x = refl
lift-∘ (suc n) σ τ zero = refl
lift-∘ (suc n) σ τ (suc x) = cong suc (lift-∘ n σ τ x)

mutual
  map-∘ : ∀ {F} σ τ → map {F} (σ ∘ τ) ≗ map σ ∘ map τ
  map-∘ σ τ (var x) = refl
  map-∘ σ τ (op p ts) = cong (op p) (map*-∘ σ τ ts)

  map*-∘ : ∀ {F s} σ τ → map* {F} (σ ∘ τ) {s} ≗ map* σ ∘ map* τ
  map*-∘ σ τ [] = refl
  map*-∘ σ τ (t ∷[ n ] ts) =
    cong₂ _∷_
      (begin
        map (lift n (σ ∘ τ)) t            ≡⟨ map-cong (lift-∘ n σ τ) t ⟩
        map (lift n σ ∘ lift n τ) t       ≡⟨ map-∘ (lift n σ) (lift n τ) t ⟩
        map (lift n σ) (map (lift n τ) t) ∎)
      (map*-∘ σ τ ts)

raise∘lift : ∀ {F} n σ τ → raise {F} n (σ ∘ τ) ≗ raise n σ ∘ lift n τ
raise∘lift zero σ τ x = refl
raise∘lift (suc n) σ τ zero = refl
raise∘lift (suc n) σ τ (suc x) = cong (map suc) (raise∘lift n σ τ x)

mutual
  bind∘map : ∀ {F} σ τ → bind {F} (σ ∘ τ) ≗ bind σ ∘ map τ
  bind∘map σ τ (var x) = refl
  bind∘map σ τ (op p ts) = cong (op p) (bind*∘map* σ τ ts)

  bind*∘map* : ∀ {F s} σ τ → bind* {F} (σ ∘ τ) {s} ≗ bind* σ ∘ map* τ
  bind*∘map* σ τ [] = refl
  bind*∘map* σ τ (t ∷[ n ] ts) =
    cong₂ _∷_
      (begin
        bind (raise n (σ ∘ τ)) t            ≡⟨ bind-cong (raise∘lift n σ τ) t ⟩
        bind (raise n σ ∘ lift n τ) t       ≡⟨ bind∘map (raise n σ) (lift n τ) t ⟩
        bind (raise n σ) (map (lift n τ) t) ∎)
      (bind*∘map* σ τ ts)

lift∘raise : ∀ {F} n σ τ → raise {F} n (map σ ∘ τ) ≗ map (lift n σ) ∘ raise n τ
lift∘raise zero σ τ x = refl
lift∘raise (suc n) σ τ zero = refl
lift∘raise (suc n) σ τ (suc x) =
  begin
    map suc (raise n (map σ ∘ τ) x)              ≡⟨ cong (map suc) (lift∘raise n σ τ x) ⟩
    map suc (map (lift n σ) (raise n τ x))       ≡⟨ sym (map-∘ suc (lift n σ) (raise n τ x)) ⟩
    map (suc ∘ lift n σ) (raise n τ x)           ≡⟨ map-∘ (lift (suc n) σ) suc (raise n τ x) ⟩
    map (lift (suc n) σ) (map suc (raise n τ x)) ∎

mutual
  map∘bind : ∀ {F} σ τ → bind {F} (map σ ∘ τ) ≗ map σ ∘ bind τ
  map∘bind σ τ (var x) = refl
  map∘bind σ τ (op p ts) = cong (op p) (map*∘bind* σ τ ts)

  map*∘bind* : ∀ {F s} σ τ → bind* {F} (map σ ∘ τ) {s} ≗ map* σ ∘ bind* τ
  map*∘bind* σ τ [] = refl
  map*∘bind* σ τ (t ∷[ n ] ts) =
    cong₂ _∷_
      (begin
        bind (raise n (map σ ∘ τ)) t        ≡⟨ bind-cong (lift∘raise n σ τ) t ⟩
        bind (map (lift n σ) ∘ raise n τ) t ≡⟨ map∘bind (lift n σ) (raise n τ) t ⟩
        map (lift n σ) (bind (raise n τ) t) ∎)
      (map*∘bind* σ τ ts)

raise-∘ : ∀ {F} n σ τ → raise {F} n (bind σ ∘ τ) ≗ bind (raise n σ) ∘ raise n τ
raise-∘ zero σ τ x = refl
raise-∘ (suc n) σ τ zero = refl
raise-∘ (suc n) σ τ (suc x) =
  begin
    map suc (raise n (bind σ ∘ τ) x)               ≡⟨ cong (map suc) (raise-∘ n σ τ x) ⟩
    map suc (bind (raise n σ) (raise n τ x))       ≡⟨ sym (map∘bind suc (raise n σ) (raise n τ x)) ⟩
    bind (map suc ∘ raise n σ) (raise n τ x)       ≡⟨ bind∘map (raise (suc n) σ) suc (raise n τ x) ⟩
    bind (raise (suc n) σ) (map suc (raise n τ x)) ∎

mutual
  bind-∘ : ∀ {F} σ τ → bind {F} (bind σ ∘ τ) ≗ bind σ ∘ bind τ
  bind-∘ σ τ (var x) = refl
  bind-∘ σ τ (op p ts) = cong (op p) (bind*-∘ σ τ ts)

  bind*-∘ : ∀ {F s} σ τ → bind* {F} (bind σ ∘ τ) {s} ≗ bind* σ ∘ bind* τ
  bind*-∘ σ τ [] = refl
  bind*-∘ σ τ (t ∷[ n ] ts) =
    cong₂ _∷_
      (begin
        bind (raise n (bind σ ∘ τ)) t         ≡⟨ bind-cong (raise-∘ n σ τ) t ⟩
        bind (bind (raise n σ) ∘ raise n τ) t ≡⟨ bind-∘ (raise n σ) (raise n τ) t ⟩
        bind (raise n σ) (bind (raise n τ) t) ∎)
      (bind*-∘ σ τ ts)

bind≡map : ∀ {F} σ → bind {F} (var ∘ σ) ≗ map σ
bind≡map σ t = begin
  bind (var ∘ σ) t   ≡⟨ bind∘map var σ t ⟩
  bind var (map σ t) ≡⟨ bind-id (map σ t) ⟩
  map σ t            ∎
