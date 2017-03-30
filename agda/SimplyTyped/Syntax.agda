module SimplyTyped.Syntax where

open import Data.List using (List; []; _∷_)
open import Data.List.All using (All)
open import Data.Nat using (ℕ)

open import Binding.Tree

data Type : Set where
  bot top : Type
  choice pair arr : Type → Type → Type

data SimplyTyped : List ℕ → Set where
  `elim : SimplyTyped (0 ∷ [])
  `tt : SimplyTyped []
  `left : SimplyTyped (0 ∷ [])
  `right : SimplyTyped (0 ∷ [])
  `switch : SimplyTyped (0 ∷ 0 ∷ 0 ∷ [])
  `fst : SimplyTyped (0 ∷ [])
  `snd : SimplyTyped (0 ∷ [])
  `cons : SimplyTyped (0 ∷ 0 ∷ [])
  `lam : Type → SimplyTyped (1 ∷ [])
  `app : SimplyTyped (0 ∷ 0 ∷ [])

pattern elim t = op `elim (t All.∷ All.[])
pattern tt = op `tt All.[]
pattern left t = op `left (t All.∷ All.[])
pattern right t = op `right (t All.∷ All.[])
pattern switch t u v = op `switch (t All.∷ u All.∷ v All.∷ All.[])
pattern fst t = op `fst (t All.∷ All.[])
pattern snd t = op `snd (t All.∷ All.[])
pattern cons t u = op `cons (t All.∷ u All.∷ All.[])
pattern lam a t = op (`lam a) (t All.∷ All.[])
pattern app t u = op `app (t All.∷ u All.∷ All.[])

{-# DISPLAY elim t = elim t #-}
{-# DISPLAY left t = left t #-}
{-# DISPLAY right t = right t #-}
{-# DISPLAY switch t u v = switch t u v #-}
{-# DISPLAY fst t = fst t #-}
{-# DISPLAY snd t = snd t #-}
{-# DISPLAY cons t u = cons t u #-}
{-# DISPLAY tt = tt #-}
{-# DISPLAY lam a t = lam a t #-}
{-# DISPLAY app t u = app t u #-}

Term = Tree SimplyTyped
