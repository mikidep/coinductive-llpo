{-# OPTIONS --allow-unsolved-metas #-}

open import CoindLLPO.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma using (Σ)
open import Cubical.Relation.Nullary using (¬_)


module CoindLLPO.BoolSeq where

module TAMO where
  isTruePos : (ℕ → Bool) → ℕ → Type
  isTruePos seq n = seq n ≡ true
  
  TruePos : (ℕ → Bool) → Type
  TruePos seq = Σ ℕ (isTruePos seq)

  isTAMO = TruePos ； isProp

  isProp-isTAMO : ∀ seq → isProp $ isTAMO seq
  isProp-isTAMO _ = isPropIsProp

  TAMO : Type
  TAMO = Σ _ isTAMO

  TrueTAMO≡ : {tamo₁ tamo₂ : TAMO}
    → (n : ℕ)
    → tamo₁ .fst n ≡ true
    → tamo₂ .fst n ≡ true
    → tamo₁ ≡ tamo₂
  TrueTAMO≡ = {!   !}
  
  TrueTAMO≢ : {tamo₁ tamo₂ : TAMO}
    → (n : ℕ)
    → tamo₁ .fst n ≡ true
    → tamo₂ .fst n ≡ false
    → ¬ (tamo₁ ≡ tamo₂)
  TrueTAMO≢ = {!   !}

