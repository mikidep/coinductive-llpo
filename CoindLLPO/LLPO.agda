open import CoindLLPO.Prelude

open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Foundations.Function using (const)

open import Cubical.HITs.PropositionalTruncation

open import CoindLLPO.Conat
open import CoindLLPO.TAMO using (TruePos; seq-to-Coℕ; Coℕ-to-seq)

module CoindLLPO.LLPO where

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

-- evens di un numero pari mi dà la metà
-- evens di un numero dispari dà ∞
evens = getEvenOdd even

-- odds di un numero pari dà ∞
-- odds di un numero dispari dà (n - 1)/2
odds = getEvenOdd odd

-- entrambi conservano ∞



Coℕ-LLPO = ∀ (n : Conat) → ∥ (evens n ≡ ∞) ⊎ (odds n ≡ ∞) ∥₁ 

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (zero to ℕ-zero; suc to ℕ-suc)

nth-even nth-odd : ℕ → ℕ

nth-even ℕ-zero = ℕ-zero
nth-even (ℕ-suc n) = ℕ-suc $ ℕ-suc $ nth-even n

nth-odd ℕ-zero = ℕ-suc ℕ-zero
nth-odd (ℕ-suc n) = ℕ-suc $ ℕ-suc $ nth-odd n



ℕ→𝟚-LLPO = ∀ (seq : ℕ → Bool)
  → isProp (TruePos seq)
  → ∥ (∀ n → seq (nth-even n) ≡ false) ⊎ (∀ n → seq (nth-odd n) ≡ false) ∥₁


evens-reflect : ∀ seq → isProp (TruePos seq) → seq ‣ seq-to-Coℕ ； evens ； Coℕ-to-seq ≡ nth-even ； seq
evens-reflect = {!   !}

Coℕ-LLPO⇒ℕ→𝟚-LLPO : Coℕ-LLPO → ℕ→𝟚-LLPO
Coℕ-LLPO⇒ℕ→𝟚-LLPO coℕ-llpo seq isPropTrue = {!   !}
  where
  con con-e con-o : Conat
  con = seq-to-Coℕ seq
  con-e = evens con
  con-o = odds con
  hyp : ∥ (con-e ≡ ∞) ⊎ (con-o ≡ ∞) ∥₁
  hyp = coℕ-llpo con

