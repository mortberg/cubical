{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ' ℓ'' : Level

isPropIsGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
             → isProp (IsGroup 0g _+_ -_)
IsGroup.isMonoid (isPropIsGroup 0g _+_ -_ g1 g2 i) = isPropIsMonoid _ _ (IsGroup.isMonoid g1) (IsGroup.isMonoid g2) i
IsGroup.inverse (isPropIsGroup 0g _+_ -_ g1 g2 i) = isPropInv (IsGroup.inverse g1) (IsGroup.inverse g2) i
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid g1))

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)


module GroupTheory (G : Group {ℓ}) where
  open GroupStr (snd G)
  abstract
    +CancelL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a + b ≡ a + c → b ≡ c
    +CancelL a {b} {c} p =
       b
        ≡⟨ sym (lid b) ∙ cong (_+ b) (sym (invl a)) ∙ sym (assoc _ _ _) ⟩
      inv a + (a + b)
        ≡⟨ cong (inv a +_) p ⟩
      inv a + (a + c)
        ≡⟨ assoc _ _ _ ∙ cong (_+ c) (invl a) ∙ lid c ⟩
      c ∎

    +CancelR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a + c ≡ b + c → a ≡ b
    +CancelR {a} {b} c p =
      a
        ≡⟨ sym (rid a) ∙ cong (a +_) (sym (invr c)) ∙ assoc _ _ _ ⟩
      (a + c) + inv c
        ≡⟨ cong (λ x → x + inv c) p ⟩
      (b + c) + inv c
        ≡⟨ sym (assoc _ _ _) ∙ cong (b +_) (invr c) ∙ rid b ⟩
      b ∎

    invInvo : (a : ⟨ G ⟩) → inv (inv a) ≡ a
    invInvo a = +CancelL (inv a) (invr (inv a) ∙ sym (invl a))

    inv0g : inv 0g ≡ 0g
    inv0g = +CancelL 0g (invr 0g ∙ sym (lid 0g))

    0gUniqueL : {e : ⟨ G ⟩} (x : ⟨ G ⟩) → e + x ≡ x → e ≡ 0g
    0gUniqueL {e} x p = +CancelR x (p ∙ sym (lid _))

    0gUniqueR : (x : ⟨ G ⟩) {e : ⟨ G ⟩} → x + e ≡ x → e ≡ 0g
    0gUniqueR x {e} p = +CancelL x (p ∙ sym (rid _))

    invUniqueL : {g h : ⟨ G ⟩} → g + h ≡ 0g → g ≡ inv h
    invUniqueL {g} {h} p = +CancelR h (p ∙ sym (invl h))

    invUniqueR : {g h : ⟨ G ⟩} → g + h ≡ 0g → h ≡ inv g
    invUniqueR {g} {h} p = +CancelL g (p ∙ sym (invr g))

    invDistr : (a b : ⟨ G ⟩) → inv (a + b) ≡ inv b + inv a
    invDistr a b = sym (invUniqueR γ) where
      γ : (a + b) + (inv b + inv a) ≡ 0g
      γ = (a + b) + (inv b + inv a)
            ≡⟨ sym (assoc _ _ _) ⟩
          a + b + (inv b) + (inv a)
            ≡⟨ cong (a +_) (assoc _ _ _ ∙ cong (_+ (inv a)) (invr b)) ⟩
          a + (0g + inv a)
            ≡⟨ cong (a +_) (lid (inv a)) ∙ invr a ⟩
          0g ∎

open Iso
open GroupStr
open GroupHom
open GroupEquiv

module GroupΣTheory {ℓ} where

  RawGroupStructure : Type ℓ → Type ℓ
  RawGroupStructure = SemigroupΣTheory.RawSemigroupStructure

  RawGroupEquivStr : StrEquiv RawGroupStructure _
  RawGroupEquivStr = SemigroupΣTheory.RawSemigroupEquivStr

  rawGroupUnivalentStr : UnivalentStr RawGroupStructure _
  rawGroupUnivalentStr = SemigroupΣTheory.rawSemigroupUnivalentStr

  -- The neutral element and the inverse function will be derived from the
  -- axioms, instead of being defined in the RawGroupStructure in order
  -- to have that group equivalences are equivalences that preserves
  -- multiplication (so we don't have to show that they also preserve inversion
  -- and neutral element, although they will preserve them).
  GroupAxioms : (G : Type ℓ) → RawGroupStructure G → Type ℓ
  GroupAxioms G _·_ =
      IsSemigroup _·_
    × (Σ[ e ∈ G ] ((x : G) → (x · e ≡ x) × (e · x ≡ x))
                × ((x : G) → Σ[ x' ∈ G ] (x · x' ≡ e) × (x' · x ≡ e)))

  GroupStructure : Type ℓ → Type ℓ
  GroupStructure = AxiomsStructure RawGroupStructure GroupAxioms

  GroupΣ : Type (ℓ-suc ℓ)
  GroupΣ = TypeWithStr ℓ GroupStructure

  -- Structured equivalences for groups are those for monoids (but different axioms)
  GroupEquivStr : StrEquiv GroupStructure ℓ
  GroupEquivStr = AxiomsEquivStr RawGroupEquivStr GroupAxioms

  open MonoidTheory

  isSetGroupΣ : (G : GroupΣ)
               → isSet _
  isSetGroupΣ (_ , _ , (isSemigroup-G , _ , _)) = IsSemigroup.is-set isSemigroup-G

  isPropGroupAxioms : (G : Type ℓ)
                      → (s : RawGroupStructure G)
                      → isProp (GroupAxioms G s)
  isPropGroupAxioms G _+_ = isPropΣ (isPropIsSemigroup _) γ
    where
    γ : (h : IsSemigroup _+_) →
        isProp (Σ[ e ∈ G ] ((x : G) → (x + e ≡ x) × (e + x ≡ x))
                         × ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e)))
    γ h (e , P , _) (e' , Q , _) =
      Σ≡Prop (λ x → isPropΣ (isPropΠ λ _ → isProp× ((IsSemigroup.is-set h) _ _) ((IsSemigroup.is-set h) _ _)) (β x))
             (sym (fst (Q e)) ∙ snd (P e'))
      where
      β : (e : G) → ((x : G) → (x + e ≡ x) × (e + x ≡ x))
        → isProp ((x : G) → Σ[ x' ∈ G ] (x + x' ≡ e) × (x' + x ≡ e))
      β e He =
        isPropΠ λ { x (x' , _ , P) (x'' , Q , _) →
                Σ≡Prop (λ _ → isProp× ((IsSemigroup.is-set h) _ _) ((IsSemigroup.is-set h) _ _))
                       (inv-lemma ℳ x x' x'' P Q) }
        where
        ℳ : Monoid
        ℳ = makeMonoid e _+_ (IsSemigroup.is-set h) (IsSemigroup.assoc h) (λ x → He x .fst) (λ x → He x .snd)

  Group→GroupΣ : Group → GroupΣ
  Group→GroupΣ (G , GS) = _ , _ , (isSemigroup GS , _ , identity GS , λ x → (inv GS) x , inverse GS x)

  GroupΣ→Group : GroupΣ → Group
  GroupΣ→Group (G , _ , SG , _ , H0g , invertible ) =
     group _ _ _ (λ x → invertible x .fst) (isgroup (ismonoid SG H0g) λ x → invertible x .snd)

  GroupIsoGroupΣ : Iso Group GroupΣ
  GroupIsoGroupΣ = iso Group→GroupΣ GroupΣ→Group (λ _ → refl) (λ _ → refl)

  groupUnivalentStr : UnivalentStr GroupStructure GroupEquivStr
  groupUnivalentStr = axiomsUnivalentStr _ isPropGroupAxioms rawGroupUnivalentStr

  GroupΣPath : (G H : GroupΣ) → (G ≃[ GroupEquivStr ] H) ≃ (G ≡ H)
  GroupΣPath = SIP groupUnivalentStr

  GroupEquivΣ : (G H : Group) → Type ℓ
  GroupEquivΣ G H = Group→GroupΣ G ≃[ GroupEquivStr ] Group→GroupΣ H

  GroupIsoΣPath : {G H : Group} → Iso (GroupEquiv G H) (GroupEquivΣ G H)
  fun GroupIsoΣPath f       = (eq f) , isHom f
  inv GroupIsoΣPath (e , h) = groupequiv e h
  rightInv GroupIsoΣPath _  = refl
  leftInv GroupIsoΣPath _   = refl

  GroupPath : (G H : Group) → (GroupEquiv G H) ≃ (G ≡ H)
  GroupPath G H =
    GroupEquiv G H                  ≃⟨ strictIsoToEquiv GroupIsoΣPath ⟩
    GroupEquivΣ G H                 ≃⟨ GroupΣPath _ _ ⟩
    Group→GroupΣ G ≡ Group→GroupΣ H ≃⟨ isoToEquiv (invIso (congIso GroupIsoGroupΣ)) ⟩
    G ≡ H ■

  RawGroupΣ : Type (ℓ-suc ℓ)
  RawGroupΣ = TypeWithStr ℓ RawGroupStructure

  Group→RawGroupΣ : Group → RawGroupΣ
  Group→RawGroupΣ (G , GS) = G , _+_ GS

  InducedGroup : (G : Group) (H : RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
               → RawGroupEquivStr (Group→RawGroupΣ G) H e → Group
  InducedGroup G H e r =
    GroupΣ→Group (inducedStructure rawGroupUnivalentStr (Group→GroupΣ G) H (e , r))

  InducedGroupPath : (G : Group {ℓ}) (H : RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
                     (E : RawGroupEquivStr (Group→RawGroupΣ G) H e)
                   → G ≡ InducedGroup G H e E
  InducedGroupPath G H e E =
    GroupPath G (InducedGroup G H e E) .fst (groupequiv e E)


-- Extract the characterization of equality of groups
GroupPath : (G H : Group {ℓ}) → (GroupEquiv G H) ≃ (G ≡ H)
GroupPath = GroupΣTheory.GroupPath

InducedGroup : (G : Group {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
             → GroupΣTheory.RawGroupEquivStr (GroupΣTheory.Group→RawGroupΣ G) H e
             → Group
InducedGroup = GroupΣTheory.InducedGroup

InducedGroupPath : (G : Group {ℓ}) (H : GroupΣTheory.RawGroupΣ) (e : ⟨ G ⟩ ≃ H .fst)
                   (E : GroupΣTheory.RawGroupEquivStr (GroupΣTheory.Group→RawGroupΣ G) H e)
                 → G ≡ InducedGroup G H e E
InducedGroupPath = GroupΣTheory.InducedGroupPath


uaGroup : {G H : Group {ℓ}} → GroupEquiv G H → G ≡ H
uaGroup {G = G} {H = H} = equivFun (GroupPath G H)

carac-uaGroup : {G H : Group {ℓ}} (f : GroupEquiv G H) → cong ⟨_⟩ (uaGroup f) ≡ ua (GroupEquiv.eq f)
carac-uaGroup f = ua (eq f) ∙ refl ≡⟨ sym (rUnit _)  ⟩
                  ua (eq f) ∎

-- Group-ua functoriality

Group≡ : (G H : Group {ℓ}) → (
  Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ]
  Σ[ q ∈ PathP (λ i → p i) (0g (snd G)) (0g (snd H)) ]
  Σ[ r ∈ PathP (λ i → p i → p i → p i) (_+_ (snd G)) (_+_ (snd H)) ]
  Σ[ s ∈ PathP (λ i → p i → p i) (inv (snd G)) (inv (snd H)) ]
  PathP (λ i → IsGroup (q i) (r i) (s i)) (isGroup (snd G)) (isGroup (snd H)))
  ≃ (G ≡ H)
Group≡ G H = isoToEquiv theIso
  where
  theIso : Iso _ _
  fun theIso (p , q , r , s , t) i = p i , groupstr (q i) (r i) (s i) (t i)
  inv theIso x = cong ⟨_⟩ x , cong (0g ∘ snd) x , cong (_+_ ∘ snd) x , cong (inv ∘ snd) x , cong (isGroup ∘ snd) x
  rightInv theIso _ = refl
  leftInv theIso _ = refl

caracGroup≡ : {G H : Group {ℓ}} (p q : G ≡ H) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
caracGroup≡ {G = G} {H = H} p q P = sym (transportTransport⁻ (ua (Group≡ G H)) p)
                                 ∙∙ cong (transport (ua (Group≡ G H))) helper
                                 ∙∙ transportTransport⁻ (ua (Group≡ G H)) q
  where
  helper : transport (sym (ua (Group≡ G H))) p ≡ transport (sym (ua (Group≡ G H))) q
  helper = Σ≡Prop
             (λ _ → isPropΣ
                       (isOfHLevelPathP' 1 (is-set (snd H)) _ _)
                       λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd H)) _ _)
                       λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set (snd H)) _ _)
                       λ _ → isOfHLevelPathP 1 (isPropIsGroup _ _ _) _ _)
             (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

uaGroupId : (G : Group {ℓ}) → uaGroup (idGroupEquiv G) ≡ refl
uaGroupId G = caracGroup≡ _ _ (carac-uaGroup (idGroupEquiv G) ∙ uaIdEquiv)

uaCompGroupEquiv : {F G H : Group {ℓ}} (f : GroupEquiv F G) (g : GroupEquiv G H) → uaGroup (compGroupEquiv f g) ≡ uaGroup f ∙ uaGroup g
uaCompGroupEquiv f g = caracGroup≡ _ _ (
  cong ⟨_⟩ (uaGroup (compGroupEquiv f g))
    ≡⟨ carac-uaGroup (compGroupEquiv f g) ⟩
  ua (eq (compGroupEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  ua (eq f) ∙ ua (eq g)
    ≡⟨ cong (_∙ ua (eq g)) (sym (carac-uaGroup f)) ⟩
  cong ⟨_⟩ (uaGroup f) ∙ ua (eq g)
    ≡⟨ cong (cong ⟨_⟩ (uaGroup f) ∙_) (sym (carac-uaGroup g)) ⟩
  cong ⟨_⟩ (uaGroup f) ∙ cong ⟨_⟩ (uaGroup g)
    ≡⟨ sym (cong-∙ ⟨_⟩ (uaGroup f) (uaGroup g)) ⟩
  cong ⟨_⟩ (uaGroup f ∙ uaGroup g) ∎) where
  open GroupEquiv


congIdLeft≡congIdRight : {A : Type ℓ} (_+A_ : A → A → A) (-A_ : A → A)
            (0A : A)
            (rUnitA : (x : A) → x +A 0A ≡ x)
            (lUnitA : (x : A) → 0A +A x ≡ x)
          → (r≡l : rUnitA 0A ≡ lUnitA 0A)
          → (p : 0A ≡ 0A) →
            cong (0A +A_) p ≡ cong (_+A 0A) p
congIdLeft≡congIdRight _+A_ -A_ 0A rUnitA lUnitA r≡l p =
            rUnit (cong (0A +A_) p)
         ∙∙ ((λ i → (λ j → lUnitA 0A (i ∧ j)) ∙∙ cong (λ x → lUnitA x i) p ∙∙ λ j → lUnitA 0A (i ∧ ~ j))
         ∙∙ cong₂ (λ x y → x ∙∙ p ∙∙ y) (sym r≡l) (cong sym (sym r≡l))
         ∙∙ λ i → (λ j → rUnitA 0A (~ i ∧ j)) ∙∙ cong (λ x → rUnitA x (~ i)) p ∙∙ λ j → rUnitA 0A (~ i ∧ ~ j))
         ∙∙ sym (rUnit (cong (_+A 0A) p))
