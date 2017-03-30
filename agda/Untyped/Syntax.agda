module Untyped.Syntax where

open import Data.List using (List; []; _∷_)
open import Data.List.All using (All)
open import Data.Nat using (ℕ)

open import Binding.Tree

data Untyped : List ℕ → Set where
  `lam : Untyped (1 ∷ [])
  `app : Untyped (0 ∷ 0 ∷ [])

pattern lam t = op `lam (t All.∷ All.[])
pattern app t u = op `app (t All.∷ u All.∷ All.[])

{-# DISPLAY lam t = lam t #-}
{-# DISPLAY app t u = app t u #-}

Term = Tree Untyped
