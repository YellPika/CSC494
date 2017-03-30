module Reflection.Rewriting.Nat where

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _+_; _≤?_)
open import Data.Nat.Properties.Simple using (+-assoc; +-comm; +-right-identity)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong-app; sym; trans)
open import Relation.Nullary using (yes; no)

open import Reflection
open import Reflection.Patterns
open import Reflection.Rewriting

private
  +-comm′ : ∀ m n o → m + n + o ≡ m + o + n
  +-comm′ m n o =
    trans (+-assoc m n o)
      (trans (cong (m +_) (+-comm n o))
        (sym (+-assoc m o n)))

+-right-identity-rule : Rule
+-right-identity-rule rec (def₂ (quote _+_) n (con (quote zero) [])) = returnTC (just (def₁ (quote +-right-identity) n))
+-right-identity-rule rec (def₂ (quote _+_) n (lit (nat 0))) = returnTC (just (def₁ (quote +-right-identity) n))
+-right-identity-rule rec term = returnTC nothing

+-comm-rule : Rule
+-comm-rule rec (def₂ (quote _+_) (var m []) (var n [])) with suc m ≤? n
... | yes p = returnTC (just (def₂ (quote +-comm) (var m []) (var n [])))
... | no ¬p = returnTC nothing
+-comm-rule rec (def₂ (quote _+_) (var m []) n) = returnTC (just (def₂ (quote +-comm) (var m []) n))
+-comm-rule rec (def₂ (quote _+_) (def₂ (quote _+_) m n) o) =
  bindTC (+-comm-rule rec (def₂ (quote _+_) n o)) λ where
    nothing → returnTC nothing
    (just proof) → returnTC (just (def₃ (quote +-comm′) m n o))
+-comm-rule rec term = returnTC nothing

+-assoc-rule : Rule
+-assoc-rule rec (def₂ (quote _+_) m (def₂ (quote _+_) n o)) = returnTC (just (def₁ (quote sym) (def₃ (quote +-assoc) m n o)))
+-assoc-rule rec term = returnTC nothing

+-cong-rule₁ : Rule
+-cong-rule₁ rec (def₂ (quote _+_) m n) =
  bindTC (rec m) λ where
    nothing → returnTC nothing
    (just proof) → returnTC (just (def₂ (quote cong-app) (def₂ (quote cong) (def₀ (quote _+_)) proof) n))
+-cong-rule₁ rec term = returnTC nothing

+-cong-rule₂ : Rule
+-cong-rule₂ rec (def₂ (quote _+_) m n) =
  bindTC (rec n) λ where
    nothing → returnTC nothing
    (just proof) → returnTC (just (def₂ (quote cong) (def₁ (quote _+_) m) proof))
+-cong-rule₂ rec term = returnTC nothing

ℕ-rule : Rule
ℕ-rule = +-right-identity-rule
       & +-comm-rule
       & +-assoc-rule
       & +-cong-rule₁
       & +-cong-rule₂
