open import CoindLLPO.Prelude

open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Codata.Conat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (const)

open import Cubical.HITs.PropositionalTruncation

module CoindLLPO.LLPO where

1+_ : ∀ {ℓ} -> Type ℓ -> Type ℓ
1+_ = Unit ⊎_

infixr 20 1+_

Conat-corec : ∀ {ℓ} {A : Type ℓ} → (α : A → 1+ A) → A → Conat
Conat-corec {A = A} α a .force = aux (α a)
  where
  aux : 1+ A → Conat′
  aux zero = zero
  aux (suc a') = suc (Conat-corec α a')

data EvenOdd : Type where
  even odd : EvenOdd

getEvenOdd : EvenOdd → Conat → Conat
getEvenOdd eo con = Conat-corec coalg (eo , con)
  where
  coalg : EvenOdd × Conat → 1+ (EvenOdd × Conat)
  coalg (even , con) = ⊎-rec
    (const zero)
    (λ con' → suc (odd , con'))
    (force con)
  coalg (odd , con) = ⊎-rec
    (const $ suc $ (even , ∞))
    ((λ con' → suc (even , con')))
    (force con)

evens = getEvenOdd even
odds = getEvenOdd odd

Coℕ-LLPO = ∀ (n : Conat) → ∥ (evens n ≡ ∞) ⊎ (odds n ≡ ∞) ∥₁ 
