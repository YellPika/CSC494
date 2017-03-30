module Reflection.Substitution where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃; _,_; proj₁)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Reflection
open import Relation.Binary.PropositionalEquality using ([_]; inspect; subst; sym)

rename : (ℕ → ℕ) → Term → Term

private
  lift : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  lift zero σ x = σ x
  lift (suc n) σ zero = zero
  lift (suc n) σ (suc x) = suc (lift n σ x)

  patternVars : List (Arg Pattern) → ℕ
  patternVars [] = 0
  patternVars (arg i (con c ps) ∷ xs) = patternVars ps + patternVars xs
  patternVars (arg i dot ∷ xs) = suc (patternVars xs)
  patternVars (arg i (var s) ∷ xs) = suc (patternVars xs)
  patternVars (arg i (lit l) ∷ xs) = patternVars xs
  patternVars (arg i (proj f) ∷ xs) = patternVars xs
  patternVars (arg i absurd ∷ xs) = patternVars xs

  renameArg : (ℕ → ℕ) → Arg Term → Arg Term
  renameArg σ (arg i x) = arg i (rename σ x)

  renameArgs : (ℕ → ℕ) → List (Arg Term) → List (Arg Term)
  renameArgs σ [] = []
  renameArgs σ (x ∷ xs) = renameArg σ x ∷ renameArgs σ xs

  renameAbs : (ℕ → ℕ) → Abs Term → Abs Term
  renameAbs σ (abs s x) = abs s (rename (lift 1 σ) x)

  renameClause : (ℕ → ℕ) → Clause → Clause
  renameClause σ (clause ps t) = clause ps (rename (lift (patternVars ps) σ) t)
  renameClause σ (absurd-clause ps) = absurd-clause ps

  renameClauses : (ℕ → ℕ) → List Clause → List Clause
  renameClauses σ [] = []
  renameClauses σ (x ∷ xs) = renameClause σ x ∷ renameClauses σ xs

rename σ (var x args) = var (σ x) (renameArgs σ args)
rename σ (con c args) = con c (renameArgs σ args)
rename σ (def f args) = def f (renameArgs σ args)
rename σ (lam v t) = lam v (renameAbs σ t)
rename σ (pat-lam cs args) = pat-lam (renameClauses σ cs) (renameArgs σ args)
rename σ (pi a b) = pi (renameArg σ a) (renameAbs σ b)
rename σ (sort s) = sort s
rename σ (lit l) = lit l
rename σ (meta m args) = meta m (renameArgs σ args)
rename σ unknown = unknown

isNonLam : Term → Bool
isNonLam (lam _ _) = false
isNonLam _ = true

IsNonLam : Term → Set
IsNonLam t =  T (isNonLam t)

NonLam : Set
NonLam = ∃ IsNonLam

applyNonLam : NonLam → List (Arg Term) → Term
applyNonLam (var x args , _) xs = var x (args ++ xs)
applyNonLam (con c args , _) xs = con c (args ++ xs)
applyNonLam (def f args , _) xs = def f (args ++ xs)
applyNonLam (pat-lam cs args , _) xs = pat-lam cs (args ++ xs)
applyNonLam (meta m args , _) xs = meta m (args ++ xs)
applyNonLam (lam v t , ()) xs
applyNonLam (t , _) xs = t

replace : (ℕ → NonLam) → Term → Term

private
  renameNonLam : (ℕ → ℕ) → NonLam → NonLam
  renameNonLam σ (t , _) with isNonLam (rename σ t) | inspect isNonLam (rename σ t)
  ... | true  | [ eq ] = rename σ t , subst T (sym eq) _
  ... | false | [ eq ] = unknown , _

  raise : ℕ → (ℕ → NonLam) → (ℕ → NonLam)
  raise zero σ x = σ x
  raise (suc n) σ zero = (var zero []) , _
  raise (suc n) σ (suc x) = renameNonLam suc (raise n σ x)

  replaceArg : (ℕ → NonLam) → Arg Term → Arg Term
  replaceArg σ (arg i x) = arg i (replace σ x)

  replaceArgs : (ℕ → NonLam) → List (Arg Term) → List (Arg Term)
  replaceArgs σ [] = []
  replaceArgs σ (x ∷ xs) = replaceArg σ x ∷ replaceArgs σ xs

  replaceAbs : (ℕ → NonLam) → Abs Term → Abs Term
  replaceAbs σ (abs s x) = abs s (replace (raise 1 σ) x)

  replaceClause : (ℕ → NonLam) → Clause → Clause
  replaceClause σ (clause ps t) = clause ps (replace (raise (patternVars ps) σ) t)
  replaceClause σ (absurd-clause ps) = absurd-clause ps

  replaceClauses : (ℕ → NonLam) → List Clause → List Clause
  replaceClauses σ [] = []
  replaceClauses σ (x ∷ xs) = replaceClause σ x ∷ replaceClauses σ xs

replace σ (var x args) = applyNonLam (σ x) args
replace σ (con c args) = con c (replaceArgs σ args)
replace σ (def f args) = def f (replaceArgs σ args)
replace σ (lam v t) = lam v (replaceAbs σ t)
replace σ (pat-lam cs args) = pat-lam (replaceClauses σ cs) (replaceArgs σ args)
replace σ (pi a b) = pi (replaceArg σ a) (replaceAbs σ b)
replace σ (sort s) = sort s
replace σ (lit l) = lit l
replace σ (meta m args) = meta m (replaceArgs σ args)
replace σ unknown = unknown 

private
  toArgTerms : List (Arg NonLam) → List (Arg Term)
  toArgTerms = map λ where (arg i (t , _)) → arg i t

  lookup : List (Arg NonLam) → ℕ → NonLam
  lookup [] x = var x [] , _
  lookup (arg i t ∷ ts) zero = t
  lookup (t ∷ ts) (suc x) = lookup ts x

apply : Term → List (Arg NonLam) → Term
apply (var x args) xs = var x (args ++ toArgTerms xs)
apply (con c args) xs = con c (args ++ toArgTerms xs)
apply (def f args) xs = def f (args ++ toArgTerms xs)
apply (pat-lam cs args) xs = pat-lam cs (args ++ toArgTerms xs)
apply (meta m args) xs = meta m (args ++ toArgTerms xs)
apply (lam v (abs s t)) xs = replace (lookup xs) t
apply t xs = t
