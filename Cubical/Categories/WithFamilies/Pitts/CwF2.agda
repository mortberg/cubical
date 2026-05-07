-- {-# OPTIONS --safe #-}

module Cubical.Categories.WithFamilies.Pitts.CwF2 where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Data.Sigma

-- open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
--open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level

open Category

record CwF (ℓOb ℓHom ℓTy ℓTm : Level) :
           Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where

  field

    -- | Contexts and substitutions

    C : Category ℓOb ℓHom

    ⟨⟩ : Terminal C

    -- | Types

    Ty : (Γ : ob C) → Type ℓTy

    _[_]Ty : {Δ Γ : ob C} (A : Ty Γ) (σ : C [ Δ , Γ ])
           → -------------------------------------------
             Ty Δ

    [id]Ty : {Γ : ob C} (A : Ty Γ)
           → ---------------------
             A [ id C ]Ty ≡ A

    [][]Ty : {Θ Δ Γ : ob C} (A : Ty Γ) (σ' : C [ Θ , Δ ]) (σ : C [ Δ , Γ ])
           → ---------------------------------------------------------------------
             A [ σ ∘⟨ C ⟩ σ' ]Ty ≡ (A [ σ ]Ty ) [ σ' ]Ty

    -- | Terms

    Tm : (Γ : ob C) (A : Ty Γ) → Type ℓTm

    _[_]Tm : {Δ Γ : ob C} {A : Ty Γ} (a : Tm Γ A) (σ : C [ Δ , Γ ])
           → --------------------------------------------------------
             Tm Δ (A [ σ ]Ty)

    [id]Tm : {Γ : ob C} {A : Ty Γ} (a : Tm Γ A)
           → -------------------------------------------------------
             PathP (λ i → Tm Γ ([id]Ty A i)) (a [ id C ]Tm) a

    [][]Tm : {Θ Δ Γ : ob C} {A : Ty Γ}
             (a : Tm Γ A) (σ' : C [ Θ , Δ ]) (σ : C [ Δ , Γ ])
           → -----------------------------------------------------
              PathP (λ i → Tm Θ ([][]Ty A σ' σ i))
                    (a [ σ ∘⟨ C ⟩ σ' ]Tm)
                    ((a [ σ ]Tm) [ σ' ]Tm)

    -- | Comprehension objects

    -- Γ.A
    _,,_ : (Γ : ob C) (A : Ty Γ) → ob C

    -- p : Γ.A → Γ
    p : {Γ : ob C} {A : Ty Γ} → C [ Γ ,, A , Γ ]

    -- q : A[p]
    q : {Γ : ob C} {A : Ty Γ} → Tm (Γ ,, A) (A [ p ]Ty)

    -- ⟨σ , a⟩
    ⟨_,_⟩ : {Δ Γ : ob C} {A : Ty Γ} (σ : C [ Δ , Γ ]) (a : Tm Δ (A [ σ ]Ty))
         → C [ Δ , Γ ,, A ]

    -- p ∘ ⟨ σ , a ⟩ = σ
    p⟨⟩ : {Δ Γ : ob C} {A : Ty Γ} (σ : C [ Δ , Γ ]) (a : Tm Δ (A [ σ ]Ty))
       → ---------------------------------------------------------------------
         p ∘⟨ C ⟩ ⟨ σ , a ⟩ ≡ σ

    -- q[⟨ σ , a ⟩] = a
    q⟨⟩ : {Δ Γ : ob C} {A : Ty Γ} (σ : C [ Δ , Γ ]) (a : Tm Δ (A [ σ ]Ty))
         (p : (A [ p ]Ty) [ ⟨ σ , a ⟩ ]Ty ≡ A [ σ ]Ty)
       → ---------------------------------------------------------------------
        PathP (λ i → Tm Δ (p i)) ( q [ ⟨ σ , a ⟩ ]Tm) a

    -- ⟨ σ , a ⟩ ∘ σ' = ⟨ σ ∘ σ' , a[σ'] ⟩
    ⟨⟩∘ : {Θ Δ Γ : ob C} {A : Ty Γ}
         (σ' : C [ Θ , Δ ]) (σ : C [ Δ , Γ ]) (a : Tm Δ (A [ σ ]Ty))

         -- Used to represent a[σ'] so that we don't need subst/transport
         (a' : Tm Θ (A [ σ ∘⟨ C ⟩ σ' ]Ty))
         (pa' : PathP (λ i → Tm Θ ([][]Ty A σ' σ i)) a' (a [ σ' ]Tm))
       → ------------------------------------------------------------------
         ⟨ σ , a ⟩ ∘⟨ C ⟩ σ' ≡ ⟨ σ ∘⟨ C ⟩ σ' , a' ⟩

    -- ⟨ p , q ⟩ = id
    pairId : {Γ : ob C} (A : Ty Γ)
           → ---------------------
             ⟨ p {A = A} , q ⟩ ≡ id C

  infix 30 _[_]Ty
  infix 30 _[_]Tm
  infix 20 _,,_

record Σ-Structure-CwF {ℓOb ℓHom ℓTy ℓTm : Level} (cwf : CwF ℓOb ℓHom ℓTy ℓTm) :
       Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTm ℓTy)))) where

  open CwF cwf

  field

    ΣTy : {Γ : ob C} (A : Ty Γ) (B : Ty (Γ ,, A)) → Ty Γ

    pair : {Γ : ob C} (A : Ty Γ) (B : Ty (Γ ,, A))
           (a : Tm Γ A)
           (a' : Tm Γ (A [ id C ]Ty))
           (pa' : PathP (λ i → Tm Γ ([id]Ty A i)) a' a)
           (b : Tm Γ (B [ ⟨ id C , a' ⟩ ]Ty))
         → --------------------------------------
           Tm Γ (ΣTy A B)

    fst : {Γ : ob C} {A : Ty Γ} {B : Ty (Γ ,, A)}
         → Tm Γ (ΣTy A B)
         → Tm Γ A

    snd : {Γ : ob C} {A : Ty Γ} {B : Ty (Γ ,, A)}
          (c : Tm Γ (ΣTy A B))
          (fstc : Tm Γ (A [ id C ]Ty))
          (pfstc : PathP (λ i → Tm Γ ([id]Ty A i)) fstc (fst c))
        → Tm Γ (B [ ⟨ id C , fstc ⟩ ]Ty)

    substΣTy : {Δ Γ : ob C} (A : Ty Γ) (B : Ty (Γ ,, A)) (σ : C [ Δ , Γ ])
               (q' : Tm (Δ ,, A [ σ ]Ty) (A [ σ ∘⟨ C ⟩ p ]Ty))
               (pq' : PathP (λ i → Tm  (Δ ,, A [ σ ]Ty) ([][]Ty A p σ i)) q' q)
             → ----------------------------------------------------------------
               (ΣTy A B) [ σ ]Ty ≡ ΣTy (A [ σ ]Ty) (B [ ⟨ σ ∘⟨ C ⟩ p , q' ⟩ ]Ty)

--     -- (pair a b)[σ] = pair (a[σ]) (b[σ])
--     substPairΣ : {Δ Γ : ob C} (A : Ty Γ) (B : Ty (ext Γ A)) (σ : C [ Δ , Γ ])
--                  (a : Tm Γ (substTy A (id C)))
--                  (b : Tm Γ (substTy B (pair (id C) a)))
--                → --------------------------------------------------------------
--                  PathP (λ i → Tm Δ (substΣTy A B σ i))
--                        (substTm (pairΣ _ _ a b) σ)
--                        (pairΣ {!!} {!!} {!substTm a σ!} {!substTm b σ!})

--     -- (fst c)[σ] = fst (c[σ])
--     substFst : {Δ Γ : ob C} {A : Ty Γ} {B : Ty (ext Γ A)} (c : Tm Γ (ΣTy A B))
--                (σ : C [ Δ , Γ ])
--              → substTm (fst c) σ ≡ fst (subst (Tm Δ) (substΣTy A B σ) (substTm c σ))

--     -- (snd c)[σ] = snd (c[σ])
--     substSnd : {Δ Γ : ob C} {A : Ty Γ} {B : Ty (ext Γ A)} (c : Tm Γ (ΣTy A B))
--                (σ : C [ Δ , Γ ])
--              → substTm (snd c) σ ≡ {!!}

--     fstPairΣ : {Γ : ob C} (A : Ty Γ) (B : Ty (ext Γ A))
--                (a : Tm Γ (substTy A (id C)))
--                (b : Tm Γ (substTy B (pair (id C) a)))
--              → --------------------------------------------------
--                fst (pairΣ A B a b) ≡ subst (Tm Γ) (substTyId A) a

--     sndPairΣ : {Γ : ob C} (A : Ty Γ) (B : Ty (ext Γ A))
--                (a : Tm Γ (substTy A (id C)))
--                (b : Tm Γ (substTy B (pair (id C) a)))
--              → --------------------------------------------------
--                snd (pairΣ A B a b) ≡
--                subst (Tm Γ)
--                      (cong (λ x → substTy B (pair (id C) x))
--                            (sym (subst⁻Subst (Tm Γ) (substTyId A) a) ∙
--                            sym (cong (subst⁻ (Tm Γ) (substTyId A)) (fstPairΣ A B a b))))
--                      b

--     -- pair (fst c) (snd c) = c
--     pairFstSnd : {!!}
