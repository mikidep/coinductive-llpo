open import CoindLLPO.Prelude

open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit using (Unit)

module CoindLLPO.Conat where

open import Cubical.Codata.Conat public
open Conat

1+_ : ∀ {ℓ} -> Type ℓ -> Type ℓ
1+_ = Unit ⊎_

infixr 20 1+_

Conat-corec : ∀ {ℓ} {A : Type ℓ} → (α : A → 1+ A) → A → Conat
Conat-corec {A = A} α a .force = corec-aux (α a)
  where
  corec-aux : 1+ A → Conat′
  corec-aux zero = zero
  corec-aux (suc a') = suc (Conat-corec α a')
