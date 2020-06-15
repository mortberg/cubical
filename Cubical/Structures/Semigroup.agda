{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Semigroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Data.Sigma

open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp

open Iso

private
  variable
    ℓ : Level

-- Semigroups as a record, inspired by the Agda standard library:
--
--  https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Bundles.agda#L48
--  https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Structures.agda#L50
--
-- Note that as we are using Path for all equations the IsMagma record
-- would only contain isSet A if we had it.
record IsSemigroup {A : Type ℓ} (_·_ : A → A → A) : Type ℓ where

  constructor issemigroup

  field
    is-set : isSet A
    assoc  : (x y z : A) → x · (y · z) ≡ (x · y) · z


record Semigroup : Type (ℓ-suc ℓ) where

  constructor semigroup

  field
    Carrier     : Type ℓ
    _·_         : Carrier → Carrier → Carrier
    isSemigroup : IsSemigroup _·_

  infixl 7 _·_

  open IsSemigroup isSemigroup public

-- Extractor for the carrier type
⟨_⟩ : Semigroup → Type ℓ
⟨ G ⟩ = Semigroup.Carrier G


record SemigroupIso (M N : Semigroup {ℓ}) : Type ℓ where

  constructor semigroupiso

  -- Shorter qualified names
  module M = Semigroup M
  module N = Semigroup N

  field
    e : ⟨ M ⟩ ≃ ⟨ N ⟩
    isHom : (x y : ⟨ M ⟩) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y


-- Develop some theory about Semigroups using various general results
-- that are stated using Σ-types. For this we define Semigroup as a
-- nested Σ-type, prove that it's equivalent to the above record
-- definition and then transport results along this equivalence.
module SemigroupΣ-theory where

  raw-semigroup-structure : Type ℓ → Type ℓ
  raw-semigroup-structure A = A → A → A

  raw-semigroup-is-SNS : SNS {ℓ} raw-semigroup-structure _
  raw-semigroup-is-SNS = binaryFunSNS pointed-iso pointed-is-SNS

  semigroup-axioms : (A : Type ℓ) → raw-semigroup-structure A → Type ℓ
  semigroup-axioms A _·_ = isSet A
                         × ((x y z : A) → x · (y · z) ≡ (x · y) · z)

  semigroup-structure : Type ℓ → Type ℓ
  semigroup-structure = add-to-structure raw-semigroup-structure semigroup-axioms

  SemigroupΣ : Type (ℓ-suc ℓ)
  SemigroupΣ {ℓ} = TypeWithStr ℓ semigroup-structure

  semigroup-iso : StrIso semigroup-structure ℓ
  semigroup-iso = add-to-iso (binaryFunIso pointed-iso) semigroup-axioms

  semigroup-axioms-isProp : (A : Type ℓ) (s : raw-semigroup-structure A)
                          → isProp (semigroup-axioms A s)
  semigroup-axioms-isProp A _·_ = isPropΣ isPropIsSet λ isSetA → isPropΠ3 λ _ _ _ → isSetA _ _

  semigroup-axiomsIsoIsSemigroup : (A : Type ℓ) (s : raw-semigroup-structure A)
                                 → Iso (semigroup-axioms A s) (IsSemigroup s)
  fun (semigroup-axiomsIsoIsSemigroup A s) (x , y)           = issemigroup x y
  inv (semigroup-axiomsIsoIsSemigroup A s) (issemigroup x y) = (x , y)
  rightInv (semigroup-axiomsIsoIsSemigroup A s) _            = refl
  leftInv (semigroup-axiomsIsoIsSemigroup A s) _             = refl

  semigroup-axioms≡IsSemigroup : (A : Type ℓ) (s : raw-semigroup-structure A)
                               → semigroup-axioms A s ≡ IsSemigroup s
  semigroup-axioms≡IsSemigroup A s = isoToPath (semigroup-axiomsIsoIsSemigroup A s)

  Semigroup→SemigroupΣ : Semigroup {ℓ} → SemigroupΣ
  Semigroup→SemigroupΣ (semigroup A _·_ isSemigroup) =
    A , _·_ , semigroup-axiomsIsoIsSemigroup _ _ .inv isSemigroup

  SemigroupΣ→Semigroup : SemigroupΣ {ℓ} → Semigroup
  SemigroupΣ→Semigroup (X , _·_ , isSemigroupΣ) =
    semigroup X _·_ (semigroup-axiomsIsoIsSemigroup _ _ .fun isSemigroupΣ)

  SemigroupIsoSemigroupΣ : Iso (Semigroup {ℓ}) SemigroupΣ
  SemigroupIsoSemigroupΣ = iso Semigroup→SemigroupΣ SemigroupΣ→Semigroup (λ _ → refl) (λ _ → refl)

  Semigroup≡SemigroupΣ : Semigroup {ℓ} ≡ SemigroupΣ
  Semigroup≡SemigroupΣ = isoToPath SemigroupIsoSemigroupΣ

  semigroup-is-SNS : SNS {ℓ} semigroup-structure semigroup-iso
  semigroup-is-SNS = add-axioms-SNS _ semigroup-axioms-isProp raw-semigroup-is-SNS

  SemigroupPathΣ : (M N : SemigroupΣ {ℓ}) → (M ≃[ semigroup-iso ] N) ≃ (M ≡ N)
  SemigroupPathΣ = SIP semigroup-is-SNS

  SemigroupIsoΣ : (M N : Semigroup {ℓ}) → Type ℓ
  SemigroupIsoΣ M N = Semigroup→SemigroupΣ M ≃[ semigroup-iso ] Semigroup→SemigroupΣ N

  SemigroupIsoΣPath : (M N : Semigroup {ℓ}) → Iso (SemigroupIso M N) (SemigroupIsoΣ M N)
  fun (SemigroupIsoΣPath M N) (semigroupiso e h) = (e , h)
  inv (SemigroupIsoΣPath M N) (e , h)            = semigroupiso e h
  rightInv (SemigroupIsoΣPath M N) _             = refl
  leftInv (SemigroupIsoΣPath M N) _              = refl

  SemigroupPath : (M N : Semigroup {ℓ}) → (SemigroupIso M N) ≃ (M ≡ N)
  SemigroupPath M N =
    SemigroupIso M N                                ≃⟨ isoToEquiv (SemigroupIsoΣPath M N) ⟩
    SemigroupIsoΣ M N                               ≃⟨ SemigroupPathΣ (Semigroup→SemigroupΣ M) (Semigroup→SemigroupΣ N) ⟩
    Semigroup→SemigroupΣ M ≡ Semigroup→SemigroupΣ N ≃⟨ isoToEquiv (invIso (congIso SemigroupIsoSemigroupΣ)) ⟩
    M ≡ N ■


-- We now extract the important results from the above module

isPropIsSemiGroup : {A : Type ℓ} (_·_ : A → A → A) → isProp (IsSemigroup _·_)
isPropIsSemiGroup s =
  subst isProp (SemigroupΣ-theory.semigroup-axioms≡IsSemigroup _ s)
        (SemigroupΣ-theory.semigroup-axioms-isProp _ s)

SemigroupPath : (M N : Semigroup {ℓ}) → (SemigroupIso M N) ≃ (M ≡ N)
SemigroupPath = SemigroupΣ-theory.SemigroupPath


-- To rename the fields when using a Semigroup use for example the following:
--
-- open Semigroup M renaming ( Carrier to M ; _·_ to _·M_ )
