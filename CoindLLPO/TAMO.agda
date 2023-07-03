open import CoindLLPO.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ) renaming (zero to ℕ-zero; suc to ℕ-suc)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; false≢true; isSetBool)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Foundations.Isomorphism using (Iso)

open import CoindLLPO.Conat
open import CoindLLPO.BoolSeq as BoolSeq
open BoolSeq.TAMO

module CoindLLPO.TAMO where

open import Cubical.Data.Bool

seq-to-Coℕ : (ℕ → Bool) → Conat
seq-to-Coℕ = Conat-corec α
  where
  α : (ℕ → Bool) → 1+ (ℕ → Bool)
  α seq = if seq ℕ-zero
    then zero
    else suc $ ℕ-suc ； seq

Coℕ-to-seq′ : Conat′ → ℕ → Bool
Coℕ-to-seq′ zero ℕ-zero = true
Coℕ-to-seq′ (suc _) ℕ-zero = false
Coℕ-to-seq′ zero (ℕ-suc n') = false
Coℕ-to-seq′ (suc con') (ℕ-suc n') = Coℕ-to-seq′ (force con') n'

Coℕ-to-seq : Conat → ℕ → Bool
Coℕ-to-seq = force ； Coℕ-to-seq′

isTAMO-Coℕ-to-seq : ∀ con → isTAMO $ Coℕ-to-seq con
isTAMO-Coℕ-to-seq con (n , p) (n' , p') = Σ≡Prop (λ _ → isSetBool _ _) (n≡n' (force con) n n' p p')
  where
  n≡n' : (con′ : Conat′) (n n' : ℕ) (p : isTruePos (Coℕ-to-seq′ con′) n) (p' : isTruePos (Coℕ-to-seq′ con′) n') → n ≡ n'
  n≡n' zero       ℕ-zero     ℕ-zero     _ _  = refl
  n≡n' zero       ℕ-zero     (ℕ-suc _)  _ p' = ⊥.rec $ false≢true p'
  n≡n' zero       (ℕ-suc _)  _          p _  = ⊥.rec $ false≢true p
  n≡n' (suc _)    ℕ-zero     ℕ-zero     _ _  = refl
  n≡n' (suc _)    ℕ-zero     (ℕ-suc _)  p _  = ⊥.rec $ false≢true p
  n≡n' (suc _)    (ℕ-suc _)  ℕ-zero     _ p' = ⊥.rec $ false≢true p'
  n≡n' (suc con') (ℕ-suc n)  (ℕ-suc n') p p' = cong ℕ-suc
    $ n≡n' (force con') n n' p p'

Coℕ-to-TAMO : Conat → TAMO
Coℕ-to-TAMO con = Coℕ-to-seq con , isTAMO-Coℕ-to-seq con

TAMO-to-Coℕ : TAMO → Conat
TAMO-to-Coℕ = fst ； seq-to-Coℕ

open Iso

TAMO-Conat-Iso : Iso TAMO Conat
TAMO-Conat-Iso .fun = TAMO-to-Coℕ
TAMO-Conat-Iso .inv = Coℕ-to-TAMO
TAMO-Conat-Iso .rightInv con = {!   !}
TAMO-Conat-Iso .leftInv tamo = aux (tamo ‣ TAMO-to-Coℕ ‣ force) refl
  where
  aux : (con′ : Conat′) → con′ ≡ tamo ‣ TAMO-to-Coℕ ‣ force → con′ ‣ conat ‣ Coℕ-to-TAMO ≡ tamo
  aux zero eq = aux' (ℕ-zero ‣ tamo .fst) refl
    where
    aux' : (b : Bool) → b ≡ ℕ-zero ‣ tamo .fst → zero ‣ conat ‣ Coℕ-to-TAMO ≡ tamo
    aux' false eq' = ⊥.rec (falsehyp refl)
      where
      falsehyp : _
      falsehyp = TrueTAMO≢ {tamo₂ = tamo} ℕ-zero {!   !} (sym eq')
    aux' true eq' = TrueTAMO≡ ℕ-zero refl (sym eq')
  aux (suc con') eq = {!   !}
TAMO≃Conat : TAMO ≃ Conat
TAMO≃Conat = {!   !}
