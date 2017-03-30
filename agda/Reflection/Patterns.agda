module Reflection.Patterns where

open import Data.List using ([]; _∷_)
open import Reflection

pattern arg′ t = arg (arg-info visible relevant) t

pattern def₀ n = def n []
pattern def₁ n x = def n (arg′ x ∷ [])
pattern def₂ n x y = def n (arg′ x ∷ arg′ y ∷ [])
pattern def₃ n x y z = def n (arg′ x ∷ arg′ y ∷ arg′ z ∷ [])
pattern def₄ n x y z w = def n (arg′ x ∷ arg′ y ∷ arg′ z ∷ arg′ w ∷ [])
pattern def₅ n x y z w u = def n (arg′ x ∷ arg′ y ∷ arg′ z ∷ arg′ w ∷ arg′ u ∷ [])
