{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S1.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.HITs.S1.Base
open import Cubical.HITs.PropositionalTruncation as PropTrunc hiding ( rec ; elim )

rec : ∀ {ℓ} {A : Type ℓ} (b : A) (l : b ≡ b) → S¹ → A
rec b l base     = b
rec b l (loop i) = l i

elim : ∀ {ℓ} (C : S¹ → Type ℓ) (b : C base) (l : PathP (λ i → C (loop i)) b b) → (x : S¹) → C x
elim _ b l base     = b
elim _ b l (loop i) = l i

-- Not sure about this name
ind : ∀ {ℓ} (C : S¹ → Type ℓ) (b : C base) (l : subst C loop b ≡ b) → (x : S¹) → C x
ind _ b l = elim _ b (toPathP l)

isConnectedS¹ : (s : S¹) → ∥ base ≡ s ∥
isConnectedS¹ base = ∣ refl ∣
isConnectedS¹ (loop i) =
  squash ∣ (λ j → loop (i ∧ j)) ∣ ∣ (λ j → loop (i ∨ ~ j)) ∣ i

isGroupoidS¹ : isGroupoid S¹
isGroupoidS¹ s t =
  PropTrunc.rec isPropIsSet
    (λ p →
      subst (λ s → isSet (s ≡ t)) p
        (PropTrunc.rec isPropIsSet
          (λ q → subst (λ t → isSet (base ≡ t)) q isSetΩS¹)
          (isConnectedS¹ t)))
    (isConnectedS¹ s)

