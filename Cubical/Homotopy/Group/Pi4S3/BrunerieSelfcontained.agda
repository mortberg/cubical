{-# OPTIONS --safe #-}
module Cubical.Homotopy.Group.Pi4S3.BrunerieSelfcontained where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude using (_,_ ; fst ; snd ; _≡_ ; transport ; _∙_ ; refl ; isProp→isSet ; J)
open import Cubical.Foundations.Equiv using (_≃_ ; isEquiv ; isPropIsEquiv ; idEquiv)
open import Cubical.Foundations.Pointed using (Pointed₀ ; pt ; _→∙_)
open import Cubical.Foundations.HLevels using (hSet ; hGroupoid ; isOfHLevelTypeOfHLevel ; isOfHLevelPath ; isOfHLevelΠ)
open import Cubical.Foundations.Univalence using (Glue ; ua)

open import Cubical.Data.Int using (ℤ ; pos ; neg ; isSetℤ)

open import Cubical.HITs.S1 using (S¹ ; base ; loop ; helix ; rotIsEquiv)
open import Cubical.HITs.S2 using (S² ; base ; surf ; S²∙ ; S¹×S¹→S² ; S²ToSetElim)
open import Cubical.HITs.Join.Base using (join ; inl ; inr ; push)
open import Cubical.HITs.SetTruncation renaming (∥_∥₂ to ∥_∥₀ ; ∣_∣₂ to ∣_∣₀ ; squash₂ to squash₀ ; rec to rec₀) using ()
open import Cubical.HITs.GroupoidTruncation renaming (∥_∥₃ to ∥_∥₁ ; ∣_∣₃ to ∣_∣₁ ; squash₃ to squash₁ ; rec to rec₁) using ()
open import Cubical.HITs.2GroupoidTruncation renaming (∥_∥₄ to ∥_∥₂ ; ∣_∣₄ to ∣_∣₂ ; squash₄ to squash₂ ; rec to rec₂ ; elim to elim₂) using ()
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid ; Susp∙ ; toSusp)

S¹∙ : Pointed₀
S¹∙ = (S¹ , base)

∥_∥₁∙ ∥_∥₂∙ : Pointed₀ → Pointed₀
∥ A , a ∥₁∙ = ∥ A ∥₁ , ∣ a ∣₁
∥ A , a ∥₂∙ = ∥ A ∥₂ , ∣ a ∣₂

Ω Ω² : Pointed₀ → Pointed₀
Ω (_ , a) = ((a ≡ a) , refl)
Ω² p = Ω (Ω p)

HopfS² : S² → Type₀
HopfS² base = S¹
HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                               ; (i = i1) → _ , idEquiv S¹
                               ; (j = i0) → _ , idEquiv S¹
                               ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

codeS² : S² → hGroupoid _
codeS² s = ∥ HopfS² s ∥₁ , squash₁

codeTruncS² : ∥ S² ∥₂ → hGroupoid _
codeTruncS² = rec₂ (isOfHLevelTypeOfHLevel 3) codeS²

encodeTruncS² : Ω ∥ S²∙ ∥₂∙ .fst → ∥ S¹ ∥₁
encodeTruncS² p = transport (λ i → codeTruncS² (p i) .fst) ∣ base ∣₁

codeS¹ : S¹ → hSet _
codeS¹ s = ∥ helix s ∥₀ , squash₀

codeTruncS¹ : ∥ S¹ ∥₁ → hSet _
codeTruncS¹ = rec₁ (isOfHLevelTypeOfHLevel 2) codeS¹

encodeTruncS¹ : Ω ∥ S¹∙ ∥₁∙ .fst → ∥ ℤ ∥₀
encodeTruncS¹ p = transport (λ i → codeTruncS¹ (p i) .fst) ∣ pos 0 ∣₀

g8 : Ω² ∥ S²∙ ∥₂∙ .fst → Ω ∥ S¹∙ ∥₁∙ .fst
g8 p i = encodeTruncS² (p i)

g9 : Ω ∥ S¹∙ ∥₁∙ .fst → ∥ ℤ ∥₀
g9 = encodeTruncS¹

-- Use trick to eliminate away the truncation last
g10 : ∥ ℤ ∥₀ → ℤ
g10 = rec₀ isSetℤ (λ x → x)

-- The brunerie element can be shown to correspond to the following map
η₃ : join S¹ S¹ → Susp S²
η₃ (inl x) = north
η₃ (inr x) = north
η₃ (push a b i) =
  (toSusp (S² , base) (S¹×S¹→S² a b) ∙ toSusp (S² , base) (S¹×S¹→S² a b)) i

K₂ : Type₀
K₂ = ∥ S² ∥₂

_+₂_ : K₂ → K₂ → K₂
_+₂_ = elim₂ (λ _ → isOfHLevelΠ 4 λ _ → squash₂)
              λ { base x → x
                ; (surf i j) x → surfc x i j}
  where
  surfc : (x : K₂) → Ω² (K₂ , x) .fst
  surfc = elim₂ (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₂ _ _) _ _)
                (S²ToSetElim (λ _ → squash₂ _ _ _ _) λ i j → ∣ surf i j ∣₂)

K₂≃K₂ : (x : S²) → K₂ ≃ K₂
fst (K₂≃K₂ x) = ∣ x ∣₂ +₂_
snd (K₂≃K₂ x) = help x
  where
  help : (x : _) → isEquiv (λ y → ∣ x ∣₂ +₂ y)
  help = S²ToSetElim (λ _ → isProp→isSet (isPropIsEquiv _)) (idEquiv _ .snd)

Code : Susp S² → Type₀
Code north = K₂
Code south = K₂
Code (merid a i) = ua (K₂≃K₂ a) i

encode : (x : Susp S²) →  north ≡ x → Code x
encode x = J (λ x p → Code x) ∣ base ∣₂

f7 : Ω (Susp∙ S²) .fst → K₂
f7 = encode north

-- We can define the Brunerie number by
brunerie : ℤ
brunerie = g10 (g9 (g8 λ i j → f7 λ k → η₃ (push (loop i) (loop j) k)))

-- Computing it takes ~1s
brunerie≡-2 : brunerie ≡ -2
brunerie≡-2 = refl
