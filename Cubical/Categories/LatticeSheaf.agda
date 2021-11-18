{-# OPTIONS --safe #-}
module Cubical.Categories.LatticeSheaf where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (L : DistLattice ℓ) (C : Precategory ℓ ℓ') where

  -- PreShv : Precategory ℓ ℓ' → (ℓS : Level)
  --        → Precategory (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS)) (ℓ-max (ℓ-max ℓ ℓ') ℓS)
  -- PreShv C ℓS = FUNCTOR (C ^op) (SET ℓS)
