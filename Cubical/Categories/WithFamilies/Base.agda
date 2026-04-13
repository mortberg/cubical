-- {-# OPTIONS --safe #-}

module Cubical.Categories.WithFamilies.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Foundations.Univalence

import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level

open Category
open Functor

record CwF (C : Category ℓ ℓ') (ℓTy ℓTm : Level) : Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓTy) ℓTm)) where

    Ctx : Type ℓ
    Ctx = C .ob

    Subst : Ctx → Ctx → Type ℓ'
    Subst = C .Hom[_,_]

    IdSubst : {Γ : Ctx} → Subst Γ Γ
    IdSubst = C .id

    field
        emptyContext : Terminal C

    ⟨⟩ : Ctx
    ⟨⟩ = emptyContext .fst

    field
        tyPresheaf : Presheaf C ℓTy

    ∫Ty : Category (ℓ-max ℓ ℓTy) (ℓ-max ℓ' ℓTy)
    ∫Ty = ∫ᴾ tyPresheaf

    Ty : Ctx → Type ℓTy
    Ty Γ = (tyPresheaf ⟅ Γ ⟆) .fst

    _∘Ty_ : {Γ Δ : Ctx} → Ty Δ → Subst Γ Δ → Ty Γ
    A ∘Ty γ = A ∘ᴾ⟨ tyPresheaf ⟩ γ

    field
        tmPresheaf : Presheaf ∫Ty ℓTm

    Tm : (Γ : Ctx) → Ty Γ → Type ℓTm
    Tm Γ A = (tmPresheaf ⟅ Γ , A ⟆) .fst

    _[_] : {Γ Δ : Ctx} {A : Ty Δ} → Tm Δ A → (σ : Subst Γ Δ) → Tm Γ (A ∘Ty σ)
    _[_] M γ = M ∘ᴾ⟨ tmPresheaf ⟩ (γ , refl)

    field
        ctxExtFunctor : Functor ∫Ty C

    ctxExt : (Γ : Ctx) → Ty Γ → Ctx
    ctxExt Γ A = ctxExtFunctor ⟅ Γ , A ⟆

    ⟨_,_⟩ : {Γ Δ : Ctx} (σ : Subst Γ Δ) (A : Ty Δ) → Subst (ctxExt Γ (A ∘Ty σ)) (ctxExt Δ A)
    ⟨_,_⟩ σ _ = ctxExtFunctor ⟪ σ , refl ⟫

    field
        ctxExtEquiv : (Γ Δ : Ctx) (A : Ty Δ) → Subst Γ (ctxExt Δ A) ≃ (Σ[ σ ∈ Subst Γ Δ ] Tm Γ (A ∘Ty σ))

    ctxExtSubst : {Γ Δ : Ctx} (A : Ty Δ) (σ : Subst Γ Δ) → Tm Γ (A ∘Ty σ) → Subst Γ (ctxExt Δ A)
    ctxExtSubst {Γ} {Δ} A σ a = invEq (ctxExtEquiv Γ Δ A) (σ , a)

    wk : {Γ : Ctx} (A : Ty Γ) → Subst (ctxExt Γ A) Γ
    wk {Γ} a = (ctxExtEquiv (ctxExt Γ a) Γ a .fst) IdSubst .fst

    q : {Γ : Ctx} (A : Ty Γ) → Tm (ctxExt Γ A) (A ∘Ty (wk A))
    q {Γ} A = (ctxExtEquiv (ctxExt Γ A) Γ A .fst) IdSubst .snd

    ctxExtSubst-n : {Γ : Ctx} (A : Ty Γ) → ctxExtSubst A (wk A) (q A) ≡ IdSubst
    ctxExtSubst-n {Γ} A = retEq (ctxExtEquiv (ctxExt Γ A) Γ A) IdSubst

    -- remove
    field
        special-ty-rev-assoc-proof : (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) → (tmPresheaf ⟅ Γ , action tyPresheaf σ (action tyPresheaf (ctxExtEquiv Γ' Δ A .fst τ .fst) A) ⟆) .fst → (tmPresheaf ⟅ Γ , action tyPresheaf (comp' C (ctxExtEquiv Γ' Δ A .fst τ .fst) σ) A ⟆) .fst
            

    field
        ctxExtEquivNat :
            (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
            (ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ)) ≡
            (σ ⋆⟨ C ⟩ (ctxExtEquiv Γ' Δ A .fst τ .fst) ,
            special-ty-rev-assoc-proof Γ Γ' Δ A σ τ ((ctxExtEquiv Γ' Δ A .fst τ .snd) [ σ ]))
