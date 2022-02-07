{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.Tricky where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 hiding (decode ; encode)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group renaming (Unit to UnitGr ; Bool to BoolGr)
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.ZAction

open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.HITs.S2

open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Whitehead

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; map to pMap)

-- Move to Base
≃∙→πEquiv : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
        → (A ≃∙ B)
        → (n : ℕ) → GroupEquiv (πGr n A) (πGr n B)
fst (fst (≃∙→πEquiv e n)) = fst (πHom n (≃∙map e))
snd (fst (≃∙→πEquiv e n)) =
  isoToIsEquiv
    (setTruncIso
      (equivToIso (_ , isEquivΩ^→ (suc n) (≃∙map e) (snd (fst e)))))
snd (≃∙→πEquiv e n) = snd (πHom n (≃∙map e))

open Exact4

-- extending exact sequence on the left by surjective map
extendExact4Surjective : {ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level}
  (G : Group ℓ) (H : Group ℓ') (L : Group ℓ'') (R : Group ℓ''') (S : Group ℓ'''')
  (G→H : GroupHom G H) (H→L : GroupHom H L) (L→R : GroupHom L R) (R→S : GroupHom R S)
  → isSurjective G→H
  → Exact4 H L R S H→L L→R R→S
  → Exact4 G L R S (compGroupHom G→H H→L) L→R R→S
ImG→H⊂KerH→L (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) x =
  pRec (GroupStr.is-set (snd R) _ _)
    (uncurry λ g → J (λ x _ → isInKer L→R x)
      (ImG→H⊂KerH→L ex (fst H→L (fst G→H g))
        ∣ (fst G→H g) , refl ∣))
KerH→L⊂ImG→H (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) x ker =
  pRec squash
    (uncurry λ y → J (λ x _ → isInIm (compGroupHom G→H H→L) x)
      (pMap (uncurry
        (λ y → J (λ y _ → Σ[ g ∈ fst G ] fst H→L (fst G→H g) ≡ H→L .fst y)
        (y , refl))) (surj y)))
    (KerH→L⊂ImG→H ex x ker)
ImH→L⊂KerL→R (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) =
  ImH→L⊂KerL→R ex
KerL→R⊂ImH→L (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) =
  KerL→R⊂ImH→L ex


-- move to morphism
compSurjective : ∀ {ℓ ℓ' ℓ''} {G : Group ℓ} {H : Group ℓ'} {L : Group ℓ''}
         → (G→H : GroupHom G H) (H→L : GroupHom H L)
         → isSurjective G→H → isSurjective H→L
         → isSurjective (compGroupHom G→H H→L)
compSurjective G→H H→L surj1 surj2 l =
  pRec squash
    (λ {(h , p)
      → pMap (λ {(g , q) → g , (cong (fst H→L) q ∙ p)})
        (surj1 h)})
    (surj2 l)


-- We start off with this horrendous but useful lemma for transporting
-- exact sequences
transportExact4' : {ℓ ℓ' ℓ'' : Level}
                   (G G₂ : Group ℓ) (H H₂ : Group ℓ') (L L₂ : Group ℓ'') (R : Group₀)
                → (G≡G₂ : G ≡ G₂) → (H≡H₂ : H ≡ H₂) (L≡L₂ : L ≡ L₂) (Unit≡R : UnitGr ≡ R)
                → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
                → (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
                → (L→R : GroupHom L R)
                → Exact4 G H L R G→H H→L L→R
                → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
                → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
                → Exact4 G₂ H₂ L₂ UnitGr G₂→H₂ H₂→L₂ (→UnitHom L₂)
transportExact4' G G₂ H H₂ L L₂ R =
  J4 (λ G₂ H₂ L₂ R G≡G₂ H≡H₂ L≡L₂ Unit≡R → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
                → (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
                → (L→R : GroupHom L R)
                → Exact4 G H L R G→H H→L L→R
                → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
                → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
                → Exact4 G₂ H₂ L₂ UnitGr G₂→H₂ H₂→L₂ (→UnitHom L₂))
      (λ G→H G₂→H₂ H→L H₂→L₂ L→R ex pp1 pp2
        → J4 (λ G₂→H₂ H₂→L₂ (x : Unit) (y : Unit)
                 pp1 pp2 (_ : tt ≡ x) (_ : tt ≡ x)
             → Exact4 G H L UnitGr G₂→H₂ H₂→L₂ (→UnitHom L))
               ex G₂→H₂ H₂→L₂ tt tt pp1 pp2 refl refl )
      G₂ H₂ L₂ R 
  where
  abstract
    J4 : ∀ {ℓ ℓ₂ ℓ₃ ℓ₄ ℓ'} {A : Type ℓ}
         {A₂ : Type ℓ₂} {A₃ : Type ℓ₃} {A₄ : Type ℓ₄}
         {x : A} {x₂ : A₂} {x₃ : A₃} {x₄ : A₄}
         (B : (y : A) (z : A₂) (w : A₃) (u : A₄)
         → x ≡ y → x₂ ≡ z → x₃ ≡ w → x₄ ≡ u → Type ℓ')
      → B x x₂ x₃ x₄ refl refl refl refl
      → (y : A) (z : A₂) (w : A₃) (u : A₄)
         (p : x ≡ y) (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u)
      → B y z w u p q r s
    J4 {x = x} {x₂ = x₂} {x₃ = x₃} {x₄ = x₄} B b y z w u =
      J (λ y p → (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u) →
        B y z w u p q r s)
        (J (λ z q → (r : x₃ ≡ w) (s : x₄ ≡ u) → B x z w u refl q r s)
          (J (λ w r → (s : x₄ ≡ u) → B x x₂ w u refl refl r s)
            (J (λ u s → B x x₂ x₃ u refl refl refl s) b)))

transportExact4 : {ℓ ℓ' ℓ'' ℓ''' : Level}
                  (G G₂ : Group ℓ) (H H₂ : Group ℓ') (L L₂ : Group ℓ'') (R R₂ : Group ℓ''')
               → (G≡G₂ : G ≡ G₂) → (H≡H₂ : H ≡ H₂) (L≡L₂ : L ≡ L₂) (R≡R₂ : R ≡ R₂)
               → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
               → (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
               → (L→R : GroupHom L R)
               → Exact4 G H L R G→H H→L L→R
               → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
               → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
               → Σ[ L₂→R₂ ∈ GroupHom L₂ R₂ ]
                   Exact4 G₂ H₂ L₂ R₂ G₂→H₂ H₂→L₂ L₂→R₂
transportExact4 G G₂ H H₂ L L₂ R R₂ =
  J4 (λ G₂ H₂ L₂ R₂ G≡G₂ H≡H₂ L≡L₂ R≡R₂
    → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
               → (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
               → (L→R : GroupHom L R)
               → Exact4 G H L R G→H H→L L→R
               → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
               → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
               → Σ[ L₂→R₂ ∈ GroupHom L₂ R₂ ]
                   Exact4 G₂ H₂ L₂ R₂ G₂→H₂ H₂→L₂ L₂→R₂)
     (λ G→H G₂→H₂ H→L H₂→L₂ L→R ex
       → J (λ G₂→H₂ _
          → H→L ≡ H₂→L₂
          → Σ[ L→R ∈ GroupHom L R ]
                   Exact4 G H L R G₂→H₂ H₂→L₂ L→R)
       (J (λ H₂→L₂ _ → Σ[ L→R ∈ GroupHom L R ]
                   Exact4 G H L R G→H H₂→L₂ L→R)
          (L→R , ex)))
     G₂ H₂ L₂ R₂
  where
  abstract
    J4 : ∀ {ℓ ℓ₂ ℓ₃ ℓ₄ ℓ'} {A : Type ℓ}
         {A₂ : Type ℓ₂} {A₃ : Type ℓ₃} {A₄ : Type ℓ₄}
         {x : A} {x₂ : A₂} {x₃ : A₃} {x₄ : A₄}
         (B : (y : A) (z : A₂) (w : A₃) (u : A₄)
         → x ≡ y → x₂ ≡ z → x₃ ≡ w → x₄ ≡ u → Type ℓ')
      → B x x₂ x₃ x₄ refl refl refl refl
      → (y : A) (z : A₂) (w : A₃) (u : A₄)
         (p : x ≡ y) (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u)
      → B y z w u p q r s
    J4 {x = x} {x₂ = x₂} {x₃ = x₃} {x₄ = x₄} B b y z w u =
      J (λ y p → (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u) →
        B y z w u p q r s)
        (J (λ z q → (r : x₃ ≡ w) (s : x₄ ≡ u) → B x z w u refl q r s)
          (J (λ w r → (s : x₄ ≡ u) → B x x₂ w u refl refl r s)
            (J (λ u s → B x x₂ x₃ u refl refl refl s) b)))

-- check if exists. Move to unit otherwise?
fibreUnitMap : ∀ {ℓ} {A : Type ℓ} → Iso (fiber (λ (a : A) → tt) tt) A
fun fibreUnitMap (x , p) = x
inv fibreUnitMap a = a , refl
rightInv fibreUnitMap _ = refl
leftInv fibreUnitMap _ = refl

W : S₊ 3 → (S₊∙ 2 ⋁ S₊∙ 2)
W = joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}
   ∘ Iso.inv (IsoSphereJoin 1 1)

fold∘W : S₊ 3 → S₊ 2
fold∘W = fold⋁ ∘ W

-- any map S³ → S² is 0-connected
isConnectedS3→S2 : (f : S₊ 3 → S₊ 2) → isConnectedFun 2 f
isConnectedS3→S2 f p =
  trRec (isProp→isOfHLevelSuc 1 isPropIsContr)
    (J (λ p _ → isConnected 2 (fiber f p))
      (∣ north , refl ∣
     , (trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
         (uncurry
           (sphereElim 2
             (λ _ → isOfHLevelΠ 3
               λ _ → isOfHLevelPath 3
                 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
           λ p → trRec (isOfHLevelTrunc 2 _ _)
             (λ r → cong ∣_∣ₕ (ΣPathP (refl , r)))
            (fun (PathIdTruncIso 1)
              (isContr→isProp
                (isConnectedPath 2 (sphereConnected 2)
                  (f north) (f north)) ∣ refl ∣ ∣ p ∣)))))))
    (fun (PathIdTruncIso 2)
      (isContr→isProp (sphereConnected 2) ∣ f north ∣ ∣ p ∣))

module BM-inst =
  BlakersMassey□ (λ _ → tt) fold∘W 3 1
   (λ _ → subst (isConnected 4)
            (isoToPath (invIso fiberUnitIso))
            (sphereConnected 3))
   (isConnectedS3→S2 fold∘W)

open BM-inst

-- The central types
coFib-fold∘W : Type
coFib-fold∘W = Pushout (λ _ → tt) fold∘W

coFib-fold∘W∙ : Pointed₀
coFib-fold∘W∙ = coFib-fold∘W , inl tt

TotalPushoutPath×∙ : Pointed ℓ-zero
fst TotalPushoutPath×∙ = Σ (Unit × S₊ 2) PushoutPath×
snd TotalPushoutPath×∙ = (tt , north) , push north

S³→TotalPushoutPath× : S₊ 3 → Σ (Unit × S₊ 2) PushoutPath×
S³→TotalPushoutPath× = toPullback

private
  inr' : S₊ 2 → coFib-fold∘W
  inr' = inr

  inr∙ : S₊∙ 2 →∙ coFib-fold∘W∙
  fst inr∙ = inr'
  snd inr∙ = sym (push north)

  fiberinr'Iso' : Iso (fiber inr' (inl tt))
                     (Σ (Unit × S₊ 2) PushoutPath×)
  fiberinr'Iso' =
    compIso (Σ-cong-iso-snd (λ x → symIso))
            (Σ-cong-iso-fst (invIso lUnit×Iso))

  fiberinr'Iso : Iso (fiber inr' (inl tt))
                     (Σ (Unit × S₊ 2) PushoutPath×)
  fun fiberinr'Iso (x , p) = (tt , x) , (sym p)
  inv fiberinr'Iso ((tt , x) , p) = x , (sym p)
  rightInv fiberinr'Iso _ = refl
  leftInv fiberinr'Iso _ = refl

  P : Pointed₀
  P = (fiber inr' (inl tt) , north , (sym (push north)))

π'P→π'TotalPath× : (n : ℕ)
  → GroupEquiv (π'Gr n TotalPushoutPath×∙) (π'Gr n P)
fst (fst (π'P→π'TotalPath× n)) =
  π'eqFun n ((invEquiv (isoToEquiv fiberinr'Iso)) , refl)
snd (fst (π'P→π'TotalPath× n)) = π'eqFunIsEquiv n _
snd (π'P→π'TotalPath× n) = π'eqFunIsHom n _

-- Time to invoke the long exact sequence of homotopy groups on
-- inr∙ : S² →∙ coFib-fold∘W∙
module LESinst = πLES {A = S₊∙ 2} {B = coFib-fold∘W∙} inr∙

-- We instantiate the sequence
-- π₃ P → π₃ S² → π₃ coFib-fold∘W∙ → π₂ P
P→S²→Pushout :
  Exact4 (πGr 2 P) (πGr 2 (S₊∙ 2)) (πGr 2 coFib-fold∘W∙) (πGr 1 P)
        (LESinst.fib→A 2)
        (LESinst.A→B 2)
        (LESinst.B→fib 1)
Exact4.ImG→H⊂KerH→L P→S²→Pushout = LESinst.Im-fib→A⊂Ker-A→B 2
Exact4.KerH→L⊂ImG→H P→S²→Pushout = LESinst.Ker-A→B⊂Im-fib→A 2
Exact4.ImH→L⊂KerL→R P→S²→Pushout = LESinst.Im-A→B⊂Ker-B→fib 1
Exact4.KerL→R⊂ImH→L P→S²→Pushout = LESinst.Ker-B→fib⊂Im-A→B 1

-- The goal now is to rewrite it as
-- π₃ S³ → π₃ S² → π₃ coFib-fold∘W∙ → Unit using the
-- "functions from spheres"-definition of πₙ.
-- Here, the first map is the one induced by fold∘W. We do this by:
-- (1) showing that π₂ P is trivial
-- (2) extending the sequence by appending surjections
-- π₃ S³ → π₃ TotalPushoutPath×∙ → π₃ P on the left.
-- (3) proving that this new composition is indeed the appropriate map

-- Step 1: π₂ P is trivial
π₂P≅0 : GroupEquiv (πGr 1 P) UnitGr
π₂P≅0 = compGroupEquiv (≃∙→πEquiv (isoToEquiv fiberinr'Iso , refl) 1)
         (GroupIso→GroupEquiv
           (contrGroupIsoUnit
             (isOfHLevelRetractFromIso 0 (invIso iso₂) isContrπ₂S³)))
  where
  iso₁ : Iso (hLevelTrunc 4 (S₊ 3))
             (hLevelTrunc 4 (Σ (Unit × S₊ 2) PushoutPath×))
  iso₁ = connectedTruncIso 4 S³→TotalPushoutPath× isConnected-toPullback

  iso₂ : Iso (π 2 (hLevelTrunc∙ 4 (S₊∙ 3)))
              (π 2 TotalPushoutPath×∙)
  iso₂ =
    (compIso (setTruncIso
      (equivToIso (_ ,
        (isEquivΩ^→ 2 (fun iso₁ , refl) (isoToIsEquiv iso₁)))))
     (invIso (πTruncIso 2)))

  isContrπ₂S³ : isContr (π 2 (hLevelTrunc∙ 4 (S₊∙ 3)))
  isContrπ₂S³ =
    subst (λ x → isContr (π 2 x))
      (λ i → ((sym (isContr→≡Unit (sphereConnected 3))) i)
            , transp (λ j → isContr→≡Unit
              (sphereConnected 3) (~ i ∧ j)) i ∣ north ∣)
      (∣ refl ∣₂ , sElim (λ _ → isSetPathImplicit)
                  λ p → cong ∣_∣₂
                          (isProp→isSet
                           (isOfHLevelPath 1 isPropUnit _ _) _ _ _ p))

-- Step 2. We transform our original sequence to one for the
-- the "maps from spheres" definition of πₙ and where π₂ P is
-- replaced by the trivial group:
-- π₃ P → π₃ S² → π₃ coFib-fold∘W∙ → 0
P→S²→Pushout→P' :
  Exact4 (π'Gr 2 P) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
         (π'∘∙Hom 2 (fst , refl))
         (π'∘∙Hom 2 inr∙)
         (→UnitHom _)
P→S²→Pushout→P' =
  transportExact4' _ _  _ _ _ _ _
  (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 P)))))
  (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 (S₊∙ 2))))))
  (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 coFib-fold∘W∙)))))
  (sym (GroupPath _ _ .fst π₂P≅0))
  _ _ _ _ _
  P→S²→Pushout
  (toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (fromPathP λ i → fst (π∘∙fib→A-PathP 2 inr∙ i))))
  ((toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (fromPathP λ i → fst (π∘∙A→B-PathP 2 inr∙ i)))))

-- The two surjections in question
π₃S³→π₃P : GroupHom (π'Gr 2 (S₊∙ 3)) (π'Gr 2 TotalPushoutPath×∙)
π₃S³→π₃P = π'∘∙Hom 2 (S³→TotalPushoutPath× , refl)

TotalPushoutPath×∙→P : TotalPushoutPath×∙ →∙ P -- Surjective, and in particular on π₃
fst TotalPushoutPath×∙→P x = (snd (fst x)) , (sym (snd x))
snd TotalPushoutPath×∙→P = refl

-- This surjectivity is where Blakers-Massey is used
-- In particular, it uses isConnected-toPullback
isSurjective-π₃S³→π₃TotalPushoutPath× : isSurjective π₃S³→π₃P
isSurjective-π₃S³→π₃TotalPushoutPath× =
  transport (λ i → isSurjective (transportLem i))
              isSurjective-π₃S³→π₃TotalPushoutPath×'
  where
  π₃S³→π₃TotalPushoutPath× : GroupHom (πGr 2 (S₊∙ 3)) (πGr 2 TotalPushoutPath×∙)
  π₃S³→π₃TotalPushoutPath× = πHom 2 (S³→TotalPushoutPath× , refl)

  isSurjective-π₃S³→π₃TotalPushoutPath×' : isSurjective π₃S³→π₃TotalPushoutPath×
  isSurjective-π₃S³→π₃TotalPushoutPath×' =
    sElim (λ _ → isProp→isSet squash)
      λ p → trRec squash
        (λ s → ∣ ∣ fst s ∣₂ , (cong ∣_∣₂ (snd s)) ∣)
        (((isConnectedΩ^→ 3 3 (S³→TotalPushoutPath× , refl)
          isConnected-toPullback) p) .fst)

  transportLem : PathP (λ i → GroupHomπ≅π'PathP (S₊∙ 3) TotalPushoutPath×∙ 2 i)
                       π₃S³→π₃TotalPushoutPath× π₃S³→π₃P
  transportLem =
    toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
       (π'∘∙Hom'≡π'∘∙fun {A = S₊∙ 3} {B = TotalPushoutPath×∙}
         2 (S³→TotalPushoutPath× , refl)))

-- We get a sequence on the right form π₃S³ → π₃S² → π₃ Pushout → Unit
S³→S²→Pushout→Unit'' :
  Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
        (compGroupHom π₃S³→π₃P
          (compGroupHom
            (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl))))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
S³→S²→Pushout→Unit'' =
  extendExact4Surjective _ _ _ _ _ _ _ _ _
    isSurjective-π₃S³→π₃TotalPushoutPath×
    (extendExact4Surjective _ _ _ _ _ _ _ _ _
      ((sElim (λ _ → isProp→isSet squash)
      (λ f → ∣ ∣ (λ x → (tt , fst f x .fst) , sym (fst f x .snd))
      , ΣPathP ((ΣPathP (refl , cong fst (snd f)))
                       , λ j i → snd f j  .snd (~ i)) ∣₂
              , cong ∣_∣₂ (ΣPathP (refl , sym (rUnit _))) ∣)))
      P→S²→Pushout→P')

-- Step 3: We need to show that the map π₃S³ → π₃S² in the above sequence
-- indeed comes from fold∘W
tripleComp≡ :
    (compGroupHom π₃S³→π₃P
     (compGroupHom
      (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl))))
  ≡ π'∘∙Hom 2 (fold∘W , refl)
tripleComp≡ =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt (sElim (λ _ → isSetPathImplicit)
     λ f → cong ∣_∣₂ (ΣPathP (refl , (cong (_∙ refl)
     (λ j → cong fst (rUnit (cong (fst TotalPushoutPath×∙→P)
               (rUnit (cong S³→TotalPushoutPath× (snd f)) (~ j))) (~ j))))))))

-- We finally get the correct sequence
S³→S²→Pushout→Unit :
  Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
        (π'∘∙Hom 2 (fold∘W , refl))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
S³→S²→Pushout→Unit =
  subst
   (λ F → Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGr
            F (π'∘∙Hom 2 inr∙)
            (→UnitHom (π'Gr 2 coFib-fold∘W∙)))
            tripleComp≡
   S³→S²→Pushout→Unit''


fold∘W≡Whitehead : fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ idfun∙ (S₊∙ 3) ∣₂
      ≡ ∣ [ idfun∙ (S₊∙ 2) ∣ idfun∙ (S₊∙ 2) ]₂ ∣₂
fold∘W≡Whitehead =
  pRec (squash₂ _ _)
    (cong ∣_∣₂)
    (indΠ₃S₂ _ _
      (funExt (λ x → funExt⁻ (sym (cong fst (id∨→∙id {A = S₊∙ 2}))) (W x))))
  where
  indΠ₃S₂ : ∀ {ℓ} {A : Pointed ℓ}
    → (f g : A →∙ S₊∙ 2)
      → fst f ≡ fst g → ∥ f ≡ g ∥
  indΠ₃S₂ {A = A} f g p =
    trRec squash
     (λ r → ∣ ΣPathP (p , r) ∣)
      (isConnectedPathP 1 {A = (λ i → p i (snd A) ≡ north)}
        (isConnectedPathSⁿ 1 (fst g (pt A)) north) (snd f) (snd g) .fst )

open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Data.Int renaming (ℤ to Z ; _·_ to _·Z_ ; _+_ to _+Z_)
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.PinSn


π₄S³≅π₃coFib-fold∘W∙ : GroupEquiv (π'Gr 3 (S₊∙ 3)) (π'Gr 2 coFib-fold∘W∙)
π₄S³≅π₃coFib-fold∘W∙ =
  compGroupEquiv
    (GroupIso→GroupEquiv
      (compGroupIso
        (π'Gr≅πGr 3 (S₊∙ 3))
        (compGroupIso
          π₄S³≅π₃PushS²
          (invGroupIso (π'Gr≅πGr 2 (Pushout⋁↪fold⋁∙ (S₊∙ 2)))))))
    (compGroupEquiv (invGroupEquiv (π'Iso 2 lem∙))
      (π'Iso 2 (lem₂ , sym (push north))))
  where
  lem₂ : Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ ≃ fst coFib-fold∘W∙
  lem₂ = compEquiv
          (compEquiv pushoutSwitchEquiv
            (isoToEquiv (PushoutDistr.PushoutDistrIso fold⋁ W λ _ → tt)))
          pushoutSwitchEquiv

  lem₁ : Pushout W (λ _ → tt) ≃ cofibW S¹ S¹ base base
  lem₁ = pushoutEquiv W (λ _ → tt) joinTo⋁ (λ _ → tt)
           (isoToEquiv (invIso (IsoSphereJoin 1 1)))
           (idEquiv _)
           (idEquiv _)
           refl
           refl

  lem : Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁
      ≃ fst (Pushout⋁↪fold⋁∙ (S₊∙ 2))
  lem = pushoutEquiv inl _ ⋁↪ fold⋁
          (idEquiv _)
          (compEquiv lem₁ (isoToEquiv (invIso (Iso-Susp×Susp-cofibJoinTo⋁ S¹ S¹ base base))))
          (idEquiv _)
          (Susp×Susp→cofibW≡ S¹ S¹ base base)
          refl

  lem∙ : (Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ , inr north)
       ≃∙ (Pushout⋁↪fold⋁∙ (S₊∙ 2))
  fst lem∙ = lem
  snd lem∙ = sym (push (inl north))
