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
         (ElSet : (Γ : U) → isSet (El Γ))
         (Unit : U)
         (UnitTerminal : isContr (El Unit))
         (Sig : (Γ : U) → (El Γ → U) → U)
         (SigIso : (Γ : U) (A : El Γ → U) → El (Sig Γ A) ≃ (Σ[ x ∈ El Γ ] El (A x)))
         where
  open FU.Internal U USet El ElSet Unit UnitTerminal Sig SigIso

  U-Σ : Σ-Structure-CwF UCwF
  U-Σ .Σ-Structure-CwF.idsubst-action _ x = x
  U-Σ .Σ-Structure-CwF.sig Γ A B x = Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))
  U-Σ .Σ-Structure-CwF.sig-nat {Γ} {Δ} A B σ = funExt (λ x → cong (Sig (A (σ x))) (funExt (λ y → {!cong (λ m → B (invEq (SigIso Γ A) m .fst .fst))!})))
  U-Σ .Σ-Structure-CwF.sig-iso = {!!}
  U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq = {!!}
  U-Σ .Σ-Structure-CwF.sig-iso-nat = {!!}

