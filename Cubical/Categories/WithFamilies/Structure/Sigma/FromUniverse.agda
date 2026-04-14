module Cubical.Categories.WithFamilies.Structure.Sigma.FromUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Categories.WithFamilies.Base
import Cubical.Categories.WithFamilies.FromUniverse as FU
open import Cubical.Categories.WithFamilies.Structure.Sigma.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module Internal (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ')
         (ElSet : (a : U) → isSet (El a))
         (Unit : U)
         (UnitTerminal : (a : U) → isContr (El a → El Unit)) -- isContr (El Unit)
         (Sig : (a : U) → (El a → U) → U)
         (SigIso : (a : U) (b : El a → U) → El (Sig a b) ≃ (Σ[ x ∈ El a ] El (b x)))
         where
  open FU.Internal U USet El ElSet Unit UnitTerminal Sig SigIso


