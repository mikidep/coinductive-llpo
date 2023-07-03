open import CoindLLPO.Prelude

open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit)

module CoindLLPO.Stream (E : Type₀) where

open import Cubical.Codata.Stream public
open Stream

E×_ : ∀ {ℓ} -> Type ℓ -> Type ℓ
E×_ = E ×_

infix 20 E×_

Stream-corec : ∀ {ℓ} {A : Type ℓ} → (α : A → E× A) → A → Stream E
Stream-corec {A = A} α a .head = α a .fst
Stream-corec {A = A} α a .tail = Stream-corec α (α a .snd)

module TAMO where
  open import Cubical.Data.Bool

  module Inductive where
    data TruePos : Stream Bool → Type where
      trueHead : ∀ strm → TruePos (true , strm)
      trueTail : ∀ strm b → TruePos strm → TruePos (b , strm)
    
    isTAMO = TruePos ； isProp

  module IndexedW where
    open import Cubical.Data.W.Indexed
    data Strue : Type where
      trueHead trueTail : Strue
    
    data Sfalse : Type where
      trueTail : Sfalse
    
    S : Stream Bool → Type
    S strm = if (strm .head)
      then Strue
      else Sfalse

    P : ∀ strm → S strm → Type
    P strm = case (strm .head) (strm .tail)
      where
      case : ∀ head tail → S (head , tail) → Type
      case true  _ trueHead = ⊥
      case true  _ trueTail = Unit
      case false _ trueTail = Unit

    inX : ∀ strm (s : S strm) → P strm s → Stream Bool
    inX strm = case (strm .head) (strm .tail)
      where
      case : ∀ -head -tail (s : S (-head , -tail)) → P (-head , -tail) s → Stream Bool
      case false -tail trueTail _ = -tail
      case true  -tail trueTail _ = -tail

    TruePos = Types.IW S P inX

    isTAMO = TruePos ； isProp

  module Lookup where
    open import Cubical.Data.Nat
    open Stream≅Nat→
    
    TruePos : Stream Bool → Type
    TruePos strm = Σ ℕ λ n → lookup strm n ≡ true

    isTAMO = TruePos ； isProp  