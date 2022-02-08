{-# OPTIONS --safe #-}
module Cubical.Categories.DistLatticeSheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base
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
open import Cubical.Categories.Limits.Limits
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
  open Order (DistLattice→Lattice L)
  open DistLatticeStr (snd L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
      using (∧≤RCancel ; ∧≤LCancel)
  open PosetStr (IndPoset .snd) hiding (_≤_)

  𝟙 : ob C
  𝟙 = terminalOb C T

  DLCat : Category ℓ ℓ
  DLCat = DistLatticeCategory L

  open Category DLCat

  -- C-valued presheaves on a distributive lattice
  DLPreSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLPreSheaf = Functor (DLCat ^op) C

  hom-∨₁ : (x y : L .fst) → DLCat [ x , x ∨l y ]
  hom-∨₁ = ∨≤RCancel
    -- TODO: isn't the fixity of the operators a bit weird?

  hom-∨₂ : (x y : L .fst) → DLCat [ y , x ∨l y ]
  hom-∨₂ = ∨≤LCancel

  hom-∧₁ : (x y : L .fst) → DLCat [ x ∧l y , x ]
  hom-∧₁ _ _ = (≤m→≤j _ _ (∧≤RCancel _ _))

  hom-∧₂ : (x y : L .fst) → DLCat [ x ∧l y , y ]
  hom-∧₂ _ _ = (≤m→≤j _ _ (∧≤LCancel _ _))


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


module SheafOnBasis (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (T : Terminal C)
                    (L' : ℙ (fst L)) (hB : IsBasis L L') where

 open Category
 open Functor

 open DistLatticeStr ⦃...⦄
 open SemilatticeStr ⦃...⦄
 open PosetStr ⦃...⦄ hiding (_≤_)
 open IsBasis hB

 private
  BasisCat = MeetSemilatticeCategory (Basis→MeetSemilattice L L' hB)
  DLBasisPreSheaf = Functor (BasisCat ^op) C

  -- to avoid writing 𝟙 L C T
  1c : ob C
  1c = terminalOb C T

  instance
   _ = snd L
   _ = snd (Basis→MeetSemilattice L L' hB)


 module Limits  (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (L' : ℙ (fst L)) where

  open DistLatticeStr (snd L)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
      using (∧≤RCancel ; ∧≤LCancel)
      renaming (_≤_ to _≤l_)
  open PosetStr (IndPoset .snd) hiding (_≤_)

  -- open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L)) renaming (_≤_ to _≤l_)
  -- open PosetStr (IndPoset .snd)
  -- open PosetStr
  -- open IsPoset
  -- open BinaryRelation
  -- open DistLatticeStr

  ↓∩ : (x : fst L) → ℙ (fst L)
  ↓∩ x y = ((y ∈ L') × (y ≤l x)) , isProp× (∈-isProp L' y) (is-set _ _)

  -- JP : (x : fst L) → Poset ℓ ℓ
  -- fst (JP x) = Σ[ a ∈ fst L ] (↓∩ x a .fst)
  -- PosetStr._≤_ (snd (JP x)) (a , _) (b , _) = a ≤l b
  -- PosetStr.is-set (isPoset (snd (JP x))) = isSetΣSndProp (is-set (snd L)) λ x → isPropΣ {!!} {!!}
  -- is-prop-valued (isPoset (snd (JP x))) = λ a b → {!!}
  -- is-refl (isPoset (snd (JP x))) = λ a → {!!}
  -- is-trans (isPoset (snd (JP x))) = {!!}
  -- is-antisym (isPoset (snd (JP x))) = {!!}

  -- ↓∩ : (x : fst L) → x ∈ L' → ℙ (fst L)
  -- ↓∩ x hx y = ((y ∈ L') × (y ≤l x)) , isProp× (∈-isProp L' y) (DistLatticeStr.is-set (snd L) _ _)

  -- bar : (x : fst L) → x ∈ L' → Poset ℓ ℓ
  -- fst (bar x hx) = Σ[ y ∈ fst L ] (↓∩ x hx y .fst)
  -- _≤_ (snd (bar x hx)) (y1 , hy1) (y2 , hy2) = y1 ≤l y2
  -- is-set (isPoset (snd (bar x hx))) = {!!}
  -- is-prop-valued (isPoset (snd (bar x hx))) = {!!}
  -- is-refl (isPoset (snd (bar x hx))) a = {!!}
  -- is-trans (isPoset (snd (bar x hx))) a b c h1 h2 = {!!}
  -- is-antisym (isPoset (snd (bar x hx))) a b h1 h2 = {!!}

  -- foo : (x : fst L) → x ∈ L' → Category ℓ ℓ
  -- foo x hx = PosetCategory (bar x hx)

  -- open Pullback
  -- open LimCone
  -- open Cospan

  -- blop : (H : (x : fst L) (hx : x ∈ L') → LimitsOfShape (foo x hx) C) → Pullbacks C
  -- pbOb (blop H cspn) = {!!}
  -- pbPr₁ (blop H cspn) = {!!}
  -- pbPr₂ (blop H cspn) = {!!}
  -- pbCommutes (blop H cspn) = {!!}
  -- univProp (blop H cspn) = {!!}


 module condSquare (x y : ob BasisCat) (x∨y∈L' : fst x ∨l fst y ∈ L') where

  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
       using (∧≤RCancel ; ∧≤LCancel)
  open MeetSemilattice (Basis→MeetSemilattice L L' hB)
       using (IndPoset)

  instance
   _ = snd IndPoset

  x∨y : ob BasisCat -- = Σ[ x ∈ L ] (x ∈ L')
  x∨y = fst x ∨l fst y , x∨y∈L'

  Bhom-∨₁ : BasisCat [ x , x∨y ]
  Bhom-∨₁ = Σ≡Prop (λ _ → L' _ .snd) (∧lAbsorb∨l _ _)

  Bhom-∨₂ : BasisCat [ y , x∨y ]
  Bhom-∨₂ = Σ≡Prop (λ _ → L' _ .snd) (cong (fst y ∧l_) (∨lComm _ _) ∙ ∧lAbsorb∨l _ _)

  Bhom-∧₁ : BasisCat [ x · y , x ]
  Bhom-∧₁ = Σ≡Prop (λ _ → L' _ .snd) (∧≤RCancel _ _)

  Bhom-∧₂ : BasisCat [ x · y , y ]
  Bhom-∧₂ =  Σ≡Prop (λ _ → L' _ .snd) (∧≤LCancel _ _)

  {-
     x ∧ y ----→   y
       |           |
       |    sq     |
       V           V
       x   ----→ x ∨ y
  -}
  Bsq : Bhom-∧₂ ⋆⟨ BasisCat ⟩ Bhom-∨₂ ≡ Bhom-∧₁ ⋆⟨ BasisCat ⟩ Bhom-∨₁
  Bsq = is-prop-valued (x · y) x∨y (Bhom-∧₂ ⋆⟨ BasisCat ⟩ Bhom-∨₂) (Bhom-∧₁ ⋆⟨ BasisCat ⟩ Bhom-∨₁)

  {-
    F(x ∨ y) ----→ F(y)
       |            |
       |     Fsq    |
       V            V
      F(x) ------→ F(x ∧ y)
  -}
  BFsq : (F : DLBasisPreSheaf)
       → F .F-hom Bhom-∨₂ ⋆⟨ C ⟩ F .F-hom Bhom-∧₂ ≡
         F .F-hom Bhom-∨₁ ⋆⟨ C ⟩ F .F-hom Bhom-∧₁
  BFsq F = sym (F-seq F Bhom-∨₂ Bhom-∧₂)
           ∙∙ cong (F .F-hom) Bsq
           ∙∙ F-seq F Bhom-∨₁ Bhom-∧₁


 -- TODO: check that this is equivalent to the functor
 -- preserving terminal objects and pullbacks
 isDLBasisSheaf : DLBasisPreSheaf → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
 isDLBasisSheaf F = ((0∈L' : 0l ∈ L') → F .F-ob (0l , 0∈L') ≡ 1c)
                  × ((x y : ob BasisCat) (x∨y∈L' : fst x ∨l fst y ∈ L')
                  → isPullback C _ _ _ (BFsq x y x∨y∈L' F))
  where
  open condSquare

  DLBasisSheaf : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  DLBasisSheaf = Σ[ F ∈ DLBasisPreSheaf ] isDLBasisSheaf F

  -- To prove the statement we probably need that C is:
  -- 1. univalent
  -- 2. has finite limits (or pullbacks and a terminal object)
  -- 3. isGroupoid (C .ob)
  -- The last point is not strictly necessary, but we have to have some
  -- control over the hLevel as we want to write F(x) in terms of its
  -- basis cover which is information hidden under a prop truncation...
  -- Alternatively we just prove the statement for C = CommRingsCategory

  -- TODO: is unique existence expressed like this what we want?
  -- statement : (F' : DLBasisSheaf)
  --           → ∃![ F ∈ DLSheaf L C T ] ((x : fst L) → (x ∈ L') → CatIso C (F-ob (fst F) x) (F-ob (fst F') x)) -- TODO: if C is univalent the CatIso could be ≡?
  -- statement (F' , h1 , hPb) = ?

  -- It might be easier to prove all of these if we use the definition
  -- in terms of particular limits instead





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
