{-# OPTIONS --safe #-}
module Cubical.Categories.DistLatticeSheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (T : Terminal C) where
  open Category hiding (_⋆_)
  open Functor
  open DistLatticeStr (snd L)
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
  open PosetStr (IndPoset .snd)

  𝟙 : ob C
  𝟙 = terminalOb C T

  DLCat : Category ℓ ℓ
  DLCat = DistLatticeCategory L

  open Category DLCat

  -- C-valued presheaves on a distributive lattice
  DLPreSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLPreSheaf = Functor (DLCat ^op) C

  hom-∨₁ : (x y : L .fst) → DLCat [ x , x ∨l y ]
  hom-∨₁ x y = goal
    where
    -- TODO: isn't the fixity of the operators a bit weird?
    goal : x ∧l (x ∨l y) ≡ x
    goal = ∧lAbsorb∨l x y

  hom-∨₂ : (x y : L .fst) → DLCat [ y , x ∨l y ]
  hom-∨₂ x y = goal
    where
    -- TODO: upstream this kind of simple lemmas? Or are they already somewhere?
    goal : y ∧l (x ∨l y) ≡ y
    goal = cong (y ∧l_) (∨lComm x y) ∙ ∧lAbsorb∨l y x

  hom-∧₁ : (x y : L .fst) → DLCat [ x ∧l y , x ]
  hom-∧₁ x y = goal
    where
    goal : (x ∧l y) ∧l x ≡ x ∧l y
    goal = ∧lComm (x ∧l y) x ∙ ∧lAssoc x x y ∙ cong (_∧l y) (∧lIdem x)

  hom-∧₂ : (x y : L .fst) → DLCat [ x ∧l y , y ]
  hom-∧₂ x y = goal
    where
    goal : (x ∧l y) ∧l y ≡ x ∧l y
    goal = sym (∧lAssoc x y y) ∙ cong (x ∧l_) (∧lIdem y)

  {-
     x ∧ y ----→   y
       |           |
       |    sq     |
       V           V
       x   ----→ x ∨ y
  -}
  sq : (x y : L .fst) → hom-∧₂ x y ⋆ hom-∨₂ x y ≡ hom-∧₁ x y ⋆ hom-∨₁ x y
  sq x y = is-prop-valued (x ∧l y) (x ∨l y) (hom-∧₂ x y ⋆ hom-∨₂ x y) (hom-∧₁ x y ⋆ hom-∨₁ x y)

  {-
    F(x ∨ y) ----→ F(y)
       |            |
       |     Fsq    |
       V            V
      F(x) ------→ F(x ∧ y)
  -}
  Fsq : (F : DLPreSheaf) (x y : L .fst)
      → F .F-hom (hom-∨₂ x y) ⋆⟨ C ⟩ F .F-hom (hom-∧₂ x y) ≡
        F .F-hom (hom-∨₁ x y) ⋆⟨ C ⟩ F .F-hom (hom-∧₁ x y)
  Fsq F x y = sym (F-seq F (hom-∨₂ x y) (hom-∧₂ x y))
           ∙∙ cong (F .F-hom) (sq x y)
           ∙∙ F-seq F (hom-∨₁ x y) (hom-∧₁ x y)

  isDLSheaf : (F : DLPreSheaf) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  isDLSheaf F = (F-ob F 0l ≡ 𝟙)
              × ((x y : L .fst) → isPullback C _ _ _ (Fsq F x y))

  -- TODO: might be better to define this as a record
  DLSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLSheaf = Σ[ F ∈ DLPreSheaf ] isDLSheaf F


module Lemma1 (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (T : Terminal C) (L' : ℙ (fst L)) (hB : IsBasis L L') where

  open Category hiding (_⋆_)
  open Functor
  open DistLatticeStr (snd L)
  open IsBasis hB

  isBasisDLSheaf : (F : DLPreSheaf L C T) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  isBasisDLSheaf F = (F-ob F 0l ≡ 𝟙 L C T) -- This is not explicitly stated in the paper... Do we need it?
                   × ((x y : L .fst) → x ∈ L' → y ∈ L' → isPullback C _ _ _ (Fsq L C T F x y))

  DLBasisSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLBasisSheaf = Σ[ F ∈ DLPreSheaf L C T ] isBasisDLSheaf F

  -- TODO: is unique existence expressed like this what we want? We
  -- might have to assume that C is univalent for this to work.
  statement : (F' : DLBasisSheaf)
            → ∃![ F ∈ DLSheaf L C T ] ((x : fst L) → (x ∈ L') → CatIso C (F-ob (fst F) x) (F-ob (fst F') x)) -- TODO: if C is univalent the CatIso could be ≡?
  statement (F' , h1 , hPb) = {!!}







  -- Scrap zone:

  -- -- Sublattices: upstream later
  -- record isSublattice (L' : ℙ (fst L)) : Type ℓ where
  --   field
  --     1l-closed  : 1l ∈ L'
  --     0l-closed  : 0l ∈ L'
  --     ∧l-closed  : {x y : fst L} → x ∈ L' → y ∈ L' → x ∧l y ∈ L'
  --     ∨l-closed  : {x y : fst L} → x ∈ L' → y ∈ L' → x ∨l y ∈ L'

  -- open isSublattice

  -- Sublattice : Type (ℓ-suc ℓ)
  -- Sublattice = Σ[ L' ∈ ℙ (fst L) ] isSublattice L'

  -- restrictDLSheaf : DLSheaf → Sublattice → DLSheaf
  -- F-ob (fst (restrictDLSheaf F (L' , HL'))) x = {!F-ob (fst F) x!} -- Hmm, not nice...
  -- F-hom (fst (restrictDLSheaf F L')) = {!!}
  -- F-id (fst (restrictDLSheaf F L')) = {!!}
  -- F-seq (fst (restrictDLSheaf F L')) = {!!}
  -- snd (restrictDLSheaf F L') = {!!}
