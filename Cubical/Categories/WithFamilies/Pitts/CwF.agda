-- {-# OPTIONS --safe #-}

module Cubical.Categories.WithFamilies.Pitts.CwF where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Data.Sigma

-- open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level

open Category

record CwF (ℓOb ℓHom ℓTy ℓTm : Level) :
           Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where

  field

    -- Contexts and substitutions

    C : Category ℓOb ℓHom

    emptyContext : Terminal C

    -- Types

    ty : (Γ : ob C) → Type ℓTy

    substTy : {Γ' Γ : ob C} (A : ty Γ) (σ : C [ Γ' , Γ ])
            → -------------------------------------------
              ty Γ'

    substTyId : {Γ : ob C} (A : ty Γ)
              → ---------------------
                substTy A (id C) ≡ A

    substTyComp : {Γ'' Γ' Γ : ob C} (A : ty Γ) (σ' : C [ Γ'' , Γ' ]) (σ : C [ Γ' , Γ ])
                → ---------------------------------------------------------------------
                  substTy A (σ ∘⟨ C ⟩ σ') ≡ substTy (substTy A σ) σ'

    -- Terms

    tm : (Γ : ob C) (A : ty Γ) → Type ℓTm

    substTm : {Γ' Γ : ob C} {A : ty Γ} (a : tm Γ A) (σ : C [ Γ' , Γ ])
            → --------------------------------------------------------
              tm Γ' (substTy A σ)

    substTmId : {Γ : ob C} {A : ty Γ} (a : tm Γ A)
              → -------------------------------------------------------
                PathP (λ i → tm Γ (substTyId A i)) (substTm a (id C)) a

    substTmComp : {Γ'' Γ' Γ : ob C} {A : ty Γ}
                  (a : tm Γ A) (σ' : C [ Γ'' , Γ' ]) (σ : C [ Γ' , Γ ])
                → -----------------------------------------------------
                  PathP (λ i → tm Γ'' (substTyComp A σ' σ i))
                        (substTm a (σ ∘⟨ C ⟩ σ'))
                        (substTm (substTm a σ) σ')

    -- Comprehension object

    ext : (Γ : ob C) (A : ty Γ) → ob C

    p : (Γ : ob C) (A : ty Γ) → C [ ext Γ A , Γ ]

    q : (Γ : ob C) (A : ty Γ) → tm (ext Γ A) (substTy A (p Γ A))

    pair : {Γ' Γ : ob C} {A : ty Γ} (σ : C [ Γ' , Γ ]) (a : tm Γ' (substTy A σ))
         → C [ Γ' , ext Γ A ]

    pPair : {Γ' Γ : ob C} {A : ty Γ} (σ : C [ Γ' , Γ ]) (a : tm Γ' (substTy A σ))
          → ---------------------------------------------------------------------
            p Γ A ∘⟨ C ⟩ pair σ a ≡ σ

    qPair : {Γ' Γ : ob C} {A : ty Γ} (σ : C [ Γ' , Γ ]) (a : tm Γ' (substTy A σ))
          → ---------------------------------------------------------------------
            PathP (λ i → tm Γ' ((sym (substTyComp A (pair σ a) (p Γ A))
                               ∙ cong (substTy A) (pPair σ a)) i))
                  (substTm (q Γ A) (pair σ a))
                  a

    pairComp : {Γ'' Γ' Γ : ob C} {A : ty Γ}
               (σ' : C [ Γ'' , Γ' ]) (σ : C [ Γ' , Γ ]) (a : tm Γ' (substTy A σ))
             → ------------------------------------------------------------------
               pair σ a ∘⟨ C ⟩ σ' ≡
               pair (σ ∘⟨ C ⟩ σ') (subst⁻ (tm Γ'') (substTyComp A σ' σ) (substTm a σ'))

    pairId : (Γ : ob C) (A : ty Γ)
           → ---------------------------
             pair (p Γ A) (q Γ A) ≡ id C


record Σ-Structure-CwF {ℓOb ℓHom ℓTy ℓTm : Level} (cwf : CwF ℓOb ℓHom ℓTy ℓTm) :
       Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTm ℓTy)))) where

  open CwF cwf

  field

    ΣTy : {Γ : ob C} (A : ty Γ) (B : ty (ext Γ A)) → ty Γ

    pairΣ : {Γ : ob C} (A : ty Γ) (B : ty (ext Γ A))
            (a : tm Γ (substTy A (id C)))          -- TODO: Ok? Could also have a subst in b, but this might be nicer...
            (b : tm Γ (substTy B (pair (id C) a)))
          → --------------------------------------------------------------------
            tm Γ (ΣTy A B)

    fst : {Γ : ob C} {A : ty Γ} {B : ty (ext Γ A)} → tm Γ (ΣTy A B) → tm Γ A

    snd : {Γ : ob C} {A : ty Γ} {B : ty (ext Γ A)} (c : tm Γ (ΣTy A B)) →
          tm Γ (substTy B (pair (id C) (subst⁻ (tm Γ) (substTyId A) (fst c))))

    -- Ugh, simplify somehow?
    substΣTy : {Γ' Γ : ob C} (A : ty Γ) (B : ty (ext Γ A)) (σ : C [ Γ' , Γ ])
             → --------------------------------------------------------------
               substTy (ΣTy A B) σ ≡
               ΣTy (substTy A σ)
                   (substTy B (pair (σ ∘⟨ C ⟩ p Γ' (substTy A σ))
                                    (subst⁻ (tm (ext Γ' (substTy A σ)))
                                            (substTyComp A (p Γ' (substTy A σ)) σ)
                                            (q Γ' (substTy A σ)))))

    substPairΣ : {!!}

    substFst : {!!}

    substSnd : {!!}

    fstPairΣ : {Γ : ob C} (A : ty Γ) (B : ty (ext Γ A))
               (a : tm Γ (substTy A (id C)))
               (b : tm Γ (substTy B (pair (id C) a)))
             → --------------------------------------------------
               fst (pairΣ A B a b) ≡ subst (tm Γ) (substTyId A) a

    sndPairΣ : {Γ : ob C} (A : ty Γ) (B : ty (ext Γ A))
               (a : tm Γ (substTy A (id C)))
               (b : tm Γ (substTy B (pair (id C) a)))
             → --------------------------------------------------
               snd (pairΣ A B a b) ≡
               subst (tm Γ)
                     (cong (λ x → substTy B (pair (id C) x))
                           (sym (subst⁻Subst (tm Γ) (substTyId A) a) ∙
                           sym (cong (subst⁻ (tm Γ) (substTyId A)) (fstPairΣ A B a b))))
                     b

    pairFstSnd : {!!}
