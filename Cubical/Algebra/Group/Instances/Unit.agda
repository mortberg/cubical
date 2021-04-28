{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit renaming (Unit to UnitType)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open GroupStr
open GroupIso
open GroupHom

private
  variable
    ℓ : Level

Unit : Group₀
Unit = UnitType , groupstr tt (λ _ _ → tt) (λ _ → tt)
                      (makeIsGroup isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)
                                   (λ _ → refl) (λ _ → refl))

open Iso

-- The trivial group is a unit.
lUnitGroupIso : {G : Group {ℓ}} → GroupIso (dirProd Unit G) G
fun (isom lUnitGroupIso) = snd
inv (isom lUnitGroupIso) g = tt , g
rightInv (isom lUnitGroupIso) _ = refl
leftInv (isom lUnitGroupIso) _ = refl
isHom lUnitGroupIso _ _ = refl

rUnitGroupIso : {G : Group {ℓ}} → GroupIso (dirProd G Unit) G
fun (isom rUnitGroupIso) = fst
inv (isom rUnitGroupIso) g = g , tt
rightInv (isom rUnitGroupIso) _ = refl
leftInv (isom rUnitGroupIso) _ = refl
isHom rUnitGroupIso _ _ = refl

lUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd Unit G) G
lUnitGroupEquiv = GrIsoToGrEquiv lUnitGroupIso

rUnitGroupEquiv : ∀ {ℓ} {G : Group {ℓ}} → GroupEquiv (dirProd G Unit) G
rUnitGroupEquiv = GrIsoToGrEquiv rUnitGroupIso

contrGroupIsoUnit : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupIso G Unit
fun (isom (contrGroupIsoUnit contr)) _ = tt
inv (isom (contrGroupIsoUnit contr)) _ = fst contr
rightInv (isom (contrGroupIsoUnit contr)) _ = refl
leftInv (isom (contrGroupIsoUnit contr)) x = snd contr x
isHom (contrGroupIsoUnit contr) _ _ = refl

contrGroupEquivUnit : {G : Group {ℓ}} → isContr ⟨ G ⟩ → GroupEquiv G Unit
contrGroupEquivUnit contr = GrIsoToGrEquiv (contrGroupIsoUnit contr)
