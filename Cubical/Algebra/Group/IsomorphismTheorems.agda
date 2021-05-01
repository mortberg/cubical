{-

This file contains the classic isomorphism theorems for groups (so far
only the first theorem)

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.IsomorphismTheorems where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients renaming (_/_ to _/s_ ; rec to recS ; elim to elimS)
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.GroupPath

private
  variable
    ℓ : Level

-- The first isomorphism theorem: im ϕ ≃ G / ker ϕ
module _ {G H : Group {ℓ}} (ϕ : GroupHom G H) where

  open isSubgroup
  open GroupHom
  open GroupIso
  open Iso
  open GroupTheory

  private
    kerϕ : NormalSubgroup G
    kerϕ = kerSubgroup ϕ , isNormalKer ϕ

    imϕ : Group
    imϕ = imGroup ϕ

    module G = GroupStr (snd G)
    module H = GroupStr (snd H)
    module imG = GroupStr (snd imϕ)
    module kerG = GroupStr (snd (G / kerϕ))

  f1 : ⟨ imϕ ⟩ → ⟨ G / kerϕ ⟩
  f1 (x , Hx) = rec→Set ( squash/)
                         (λ { (y , hy) → [ y ]})
                         (λ { (y , hy) (z , hz) → eq/ y z (rem y z hy hz) })
                         Hx
    where
    rem : (y z : ⟨ G ⟩) → ϕ .fun y ≡ x → ϕ .fun z ≡ x → ϕ .fun (y G.· G.inv z) ≡ H.1g
    rem y z hy hz =
      ϕ .fun (y G.· G.inv z)        ≡⟨ ϕ .isHom _ _ ⟩
      ϕ .fun y H.· ϕ .fun (G.inv z) ≡⟨ cong (ϕ .fun y H.·_) (homInv ϕ _) ⟩
      ϕ .fun y H.· H.inv (ϕ .fun z) ≡⟨ (λ i → hy i H.· H.inv (hz i)) ⟩
      x H.· H.inv x                 ≡⟨ H.invr x ⟩
      H.1g                          ∎

  f2 : ⟨ G / kerϕ ⟩ → ⟨ imϕ ⟩
  f2 = recS imG.is-set (λ y → ϕ .fun y , ∣ y , refl ∣)
                       (λ x y r → Σ≡Prop (λ _ → squash)
                       (rem x y r))
    where
    rem : (x y : ⟨ G ⟩) → ϕ .fun (x G.· G.inv y) ≡ H.1g → ϕ .fun x ≡ ϕ .fun y
    rem x y r =
      ϕ .fun x                                      ≡⟨ sym (H.rid _) ⟩
      ϕ .fun x H.· H.1g                             ≡⟨ cong (ϕ .fun x H.·_) (sym (H.invl _)) ⟩
      ϕ .fun x H.· H.inv (ϕ .fun y) H.· ϕ .fun y    ≡⟨ (λ i → ϕ .fun x H.· homInv ϕ y (~ i) H.· ϕ .fun y) ⟩
      ϕ .fun x H.· ϕ .fun (G.inv y) H.· ϕ .fun y    ≡⟨ H.assoc _ _ _ ⟩
      (ϕ .fun x H.· ϕ .fun (G.inv y)) H.· ϕ .fun y  ≡⟨ cong (H._· _) (sym (ϕ .isHom _ _)) ⟩
      ϕ .fun (x G.· G.inv y) H.· ϕ .fun y           ≡⟨ cong (H._· ϕ .fun y) r ⟩
      H.1g H.· ϕ .fun y                             ≡⟨ H.lid _ ⟩
      ϕ .fun y ∎

  f12 : (x : ⟨ G / kerϕ ⟩) → f1 (f2 x) ≡ x
  f12 = elimProp (λ _ → squash/ _ _) (λ _ → refl)

  f21 : (x : ⟨ imϕ ⟩) → f2 (f1 x) ≡ x
  f21 (x , hx) = elim {P = λ hx → f2 (f1 (x , hx)) ≡ (x , hx)}
                      (λ _ → imG.is-set _ _)
                      (λ {(x , hx) → Σ≡Prop (λ _ → squash) hx})
                      hx

  f1-isHom : (x y : ⟨ imϕ ⟩) → f1 (x imG.· y) ≡ f1 x kerG.· f1 y
  f1-isHom (x , hx) (y , hy) =
    elim2 {P = λ hx hy → f1 ((x , hx) imG.· (y , hy)) ≡ f1 (x , hx) kerG.· f1 (y , hy)}
          (λ _ _ → kerG.is-set _ _) (λ _ _ → refl) hx hy

  -- The first isomorphism theorem for groups
  isoThm1 : GroupIso imϕ (G / kerϕ)
  fun (isom isoThm1) = f1
  inv (isom isoThm1) = f2
  rightInv (isom isoThm1) = f12
  leftInv (isom isoThm1) = f21
  isHom isoThm1 = f1-isHom

  -- The SIP lets us turn the isomorphism theorem into a path
  pathThm1 : imϕ ≡ G / kerϕ
  pathThm1 = uaGroup (GroupIso→GroupEquiv isoThm1)
