{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.WithFamilies.Pitts.CwF3 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

private
  variable
    ℓ ℓ' : Level

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

open Functor

import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

module _ {ℓOb ℓHom : Level} {C : Category ℓOb ℓHom} where

  open Category C

  record Presheaf∫ (P : Presheaf C ℓ) (ℓ' : Level) : Type (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓ (ℓ-suc ℓ')))) where

    P-fun : (x : ob) → Type ℓ
    P-fun x = P .F-ob x .fst

    field
      obPresheaf∫ : (x : ob) (px : P-fun x) → Type ℓ'
      isSetObPresheaf∫ : (x : ob) (px : P-fun x) → isSet (obPresheaf∫ x px)

      homPresheaf∫ : {x y : ob} {px : P-fun x} (a : obPresheaf∫ x px) (f : C [ y , x ])
                   → obPresheaf∫ y (P .F-hom f px)

      homPresheaf∫Id : {x : ob} {px : P-fun x} (a : obPresheaf∫ x px)
                     → PathP (λ i → obPresheaf∫ x (P .F-id i px))
                             (homPresheaf∫ a id)
                             a

      homPresheaf∫Comp : {x y z : ob} {px : P-fun x} (a : obPresheaf∫ x px) (f : C [ y , x ]) (g : C [ z , y ])
                       → PathP (λ i → obPresheaf∫ z (P .F-seq f g i px))
                               (homPresheaf∫ a (f ∘ g))
                               (homPresheaf∫ (homPresheaf∫ a f) g)


  open Presheaf∫

  toPresheaf∫ : {F : Presheaf C ℓ} → Presheaf (∫ F) ℓ → Presheaf∫ F ℓ
  toPresheaf∫ P .obPresheaf∫ x px = P .F-ob (x , px) .fst
  toPresheaf∫ P .isSetObPresheaf∫ x px = P .F-ob (x , px) .snd
  toPresheaf∫ P .homPresheaf∫ a f = P .F-hom (f , refl) a
  toPresheaf∫ {F = F} P .homPresheaf∫Id {x = x} {px} a =
    let
        q : (px : F .F-ob x .fst) → F .F-hom id px ≡ px
        q px i = F .F-id i px

        B : (px : F .F-ob x .fst) → Type (ℓ-suc _)
        B px = P .F-ob (x , F .F-hom id px) .fst ≡ P .F-ob (x , px) .fst

        p : (px : F .F-ob x .fst) → B px
        p px i = P .F-ob (x , q px i) .fst

        goal2 : PathP (λ i → p px i) (P .F-hom (id , refl) a) (P .F-hom (id , q px) a)
        goal2 i = P .F-hom (id , λ j → isSet→isSet' (F .F-ob x .snd) refl (funExt⁻ (F .F-id) px) refl (funExt⁻ (F .F-id) px) i j) a

        goal : transport (p px) (P .F-hom (id , refl) a) ≡ P .F-hom (id , q px) a
        goal = fromPathP goal2
    in toPathP (goal ∙ funExt⁻ (P .F-id) a )
   -- toPathP (fromPathP (cong {B = λ z → P .F-ob (x , z) .fst} (λ px' → {!!}) (funExt⁻ (F .F-id) px)) ∙ funExt⁻ (P .F-id) a)
  toPresheaf∫ P .homPresheaf∫Comp a f g = {! !}

  fromPresheaf∫ : {F : Presheaf C ℓ} → Presheaf∫ F ℓ → Presheaf (∫ F) ℓ
  fromPresheaf∫ P .F-ob (x , px) .fst = P .obPresheaf∫ x px
  fromPresheaf∫ P .F-ob (x , px) .snd = P .isSetObPresheaf∫ x px
  fromPresheaf∫ P .F-hom {y = y} (f , h) a = subst (P .obPresheaf∫ (y .fst)) h (P .homPresheaf∫ a f)
  fromPresheaf∫ P .F-id = funExt (λ a → fromPathP (P .homPresheaf∫Id a))
  fromPresheaf∫ P .F-seq (f , hf) (g , hg) = funExt (λ a → {!fromPathP (symP (P .homPresheaf∫Comp a f g))!})

module Categorical {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)
  open Functor
  open Iso

  Ctx = Category.ob C

  _⟶_ : (Δ Γ : Ctx) → Type ℓHom
  Δ ⟶ Γ = C [ Δ , Γ ]

  infix 20 _⟶_

  private variable
    Θ Δ Γ : Ctx

  -- More categorical definition of CwF
  record CwF (ℓTy ℓTm : Level) :
             Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where
    field
      emptyContext : Terminal C

      Ty : Presheaf C ℓTy

    -- Some nicer notations
    Ty[_] : (Γ : Ctx) → Type ℓTy
    Ty[ Γ ] = Ty .F-ob Γ .fst

    _[_]Ty : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) → Ty[ Δ ]
    A [ σ ]Ty = Ty .F-hom σ A

    open Presheaf∫

    field
      Tm : Presheaf∫ Ty ℓTm

      ctxExt : Functor (∫ Ty) C

    _[_]Tm : {A : Ty[ Γ ]} (a : Tm .obPresheaf∫ Γ A) (σ : Δ ⟶ Γ) → Tm .obPresheaf∫ Δ (A [ σ ]Ty)
    _[_]Tm = Tm .homPresheaf∫

    _⋆_ : (Γ : Ctx) (A : Ty[ Γ ]) → Ctx
    Γ ⋆ A = ctxExt .F-ob (Γ , A)

    infix  40 _[_]Ty
    infix  40 _[_]Tm
    infixl 30 _⋆_

    field
      ctxExtIso : (A : Ty[ Γ ])
                → Iso (Δ ⟶ Γ ⋆ A) (Σ[ σ ∈ Δ ⟶ Γ ] Tm .obPresheaf∫ Δ (A [ σ ]Ty))


    -- TODO: what is a good name for this?
    drop : (A : Ty[ Γ ]) (τ : Δ ⟶ Γ ⋆ A) → Δ ⟶ Γ
    drop A τ = ctxExtIso A .fun τ .fst

    field
      -- This looks strictly worse than the next field. So drop?
      ctxExtIsoFunNat : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ ⋆ A) (τ : Θ ⟶ Δ)
                      → ctxExtIso A .fun (σ ∘ τ) ≡
                        (drop A σ ∘ τ , subst (Tm .obPresheaf∫ Θ) (sym (funExt⁻ (Ty .F-seq (drop A σ) τ) A)) ((ctxExtIso A .fun σ .snd) [ τ ]Tm))

      -- In fact it is not, see instantation below...
      -- ctxExtIsoInvNat : (A : Ty[ Γ ]) (σ : Δ ⟶ Γ) (a : Tm Δ (A [ σ ]Ty)) (τ : Θ ⟶ Δ)
      --                 → ctxExtIso A .inv (σ , a) ∘ τ
      --                 ≡ ctxExtIso A .inv (σ ∘ τ , subst (Tm Θ) (sym (funExt⁻ (Ty .F-seq σ τ) A)) (a [ τ ]Tm))

  record Σ-Structure-CwF {ℓTy ℓTm : Level} (cwf : CwF ℓTy ℓTm) :
         Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTm ℓTy)))) where

    open CwF cwf
    open Presheaf∫

    field
      ΣTy : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ]) → Ty[ Γ ]

      ΣTyNat : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ]) (σ : Δ ⟶ Γ)
             → (ΣTy A B) [ σ ]Ty ≡ ΣTy (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty)

      ΣTmIso : (A : Ty[ Γ ]) (B : Ty[ Γ ⋆ A ])
             → Iso (Tm .obPresheaf∫ Γ (ΣTy A B))
                   (Σ[ a ∈ Tm .obPresheaf∫ Γ A ] Tm .obPresheaf∫ Γ (B [ ctxExtIso A .inv (id , (a [ id ]Tm)) ]Ty))

      coerceInv : (A : Ty[ Γ ])
                  (B : Ty[ Γ ⋆ A ])
                  (a : Tm .obPresheaf∫ Γ A)
                  (σ : Δ ⟶ Γ)
                → (B [ inv (ctxExtIso A) (id , a [ id ]Tm) ]Ty) [ σ ]Ty
                ≡ (B [ ctxExt .F-hom (σ , refl) ]Ty) [ inv (ctxExtIso (A [ σ ]Ty)) (id , (a [ σ ]Tm) [ id ]Tm) ]Ty

      ΣTmIsoInvNat : (A : Ty[ Γ ])
                     (B : Ty[ Γ ⋆ A ])
                     (a : Tm .obPresheaf∫ Γ A)
                     (b : Tm .obPresheaf∫ Γ (B [ ctxExtIso A .inv (id , (a [ id ]Tm)) ]Ty))
                     (σ : Δ ⟶ Γ)
                   → PathP (λ i → Tm .obPresheaf∫ Δ (ΣTyNat A B σ i))
                           (ΣTmIso A B .inv (a , b) [ σ ]Tm)
                           (ΣTmIso (A [ σ ]Ty) (B [ ctxExt .F-hom (σ , refl) ]Ty) .inv
                             (a [ σ ]Tm , subst (Tm .obPresheaf∫ Δ) (coerceInv A B a σ) (b [ σ ]Tm)))

module V_Categorical_CwF {ℓ : Level} where

  open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
  open import Cubical.Data.IterativeSets.Sigma
  open import Cubical.Data.IterativeSets.Unit
  open import Agda.Builtin.Unit

  open Category renaming (_⋆_ to _⋆C_)

  VCat : Category (ℓ-suc ℓ) ℓ
  VCat .ob       = V
  VCat .Hom[_,_] = λ Δ Γ → El Δ → El Γ
  VCat .id       = λ x → x
  VCat ._⋆C_     = λ f g x → g (f x)
  VCat .⋆IdL     = λ _ → refl
  VCat .⋆IdR     = λ _ → refl
  VCat .⋆Assoc   = λ _ _ _ → refl
  VCat .isSetHom {y = y} = isSet→ (isSetEl y)

  open Categorical
  open CwF
  open Iso
  open Functor
  open Presheaf∫

  VCwF : CwF VCat (ℓ-suc ℓ) ℓ
  VCwF .emptyContext    = unit⁰ , λ _ → (λ _ → lift tt) , λ _ _ _ → lift tt
  VCwF .Ty .F-ob Γ .fst = El Γ → V {ℓ}
  VCwF .Ty .F-ob Γ .snd = isSet→ isSetV⁰
  VCwF .Ty .F-hom σ A x = A (σ x)
  VCwF .Ty .F-id        = refl
  VCwF .Ty .F-seq _ _   = refl
  VCwF .Tm .obPresheaf∫ Γ A = (x : El Γ) → El (A x)
  VCwF .Tm .isSetObPresheaf∫ Γ A = isSetΠ (λ _ → isSetEl _)
  VCwF .Tm .homPresheaf∫ a σ x = a (σ x)
  VCwF .Tm .homPresheaf∫Id a = refl
  VCwF .Tm .homPresheaf∫Comp a σ' σ = refl
  VCwF .ctxExt .F-ob (Γ , A) = Σ⁰ Γ A
  VCwF .ctxExt .F-hom σ (x , a) .fst = σ .fst x
  VCwF .ctxExt .F-hom σ (x , a) .snd = subst⁻ El (funExt⁻ (σ .snd) x) a
  VCwF .ctxExt .F-id = funExt (λ x → ΣPathP (refl , transportRefl _))
  VCwF .ctxExt .F-seq σ τ  =
    funExt (λ x → ΣPathP ( refl
                         , cong (λ p → subst El p (x .snd)) (isSetV⁰ _ _ _ _)
                         ∙ substComposite El _ _ _))
  VCwF .ctxExtIso A = Σ-Π-Iso
  VCwF .ctxExtIsoFunNat A σ τ = ΣPathP (refl , sym (transportRefl _))
--  VCwF .ctxExtIsoInvNat A σ a τ = funExt (λ x → ΣPathP (refl , (λ i → {!!})))

  open import Cubical.Foundations.Path

  open Σ-Structure-CwF

  goal : Σ-Structure-CwF VCat VCwF
  goal .ΣTy A B x = Σ⁰ (A x) (λ y → B (x , y))
  goal .ΣTyNat A B σ = funExt (λ x → cong (Σ⁰ (A (σ x))) (funExt (λ y → cong B (ΣPathP (refl , sym (transportRefl _))))))
  goal .ΣTmIso A B = Σ-Π-Iso
  goal .coerceInv A B a σ = funExt (λ ρ → cong B (ΣPathP (refl , (sym (transportRefl _)))))
  goal .ΣTmIsoInvNat {Δ = Δ} A B a b σ = funExt (λ ρ → ΣPathP (refl ,
    let goal : transp (λ i → El (B (σ ρ , transp (λ _ → El (A (σ ρ))) i (a (σ ρ)))))
                        i0
                        (transp (λ i → El (B (σ (transp (λ _ → El Δ) i ρ) , transp (λ _ → El (A (σ (transp (λ _ → El Δ) i ρ)))) (~ i) (a (σ (transp (λ _ → El Δ) i ρ))))))
                                i0
                                (b (σ (transp (λ _ → El Δ) i0 ρ))))
               ≡ b (σ ρ)
        goal j = transp (λ i → El (B (σ ρ , transp (λ _ → El (A (σ ρ))) (i ∨ j) (a (σ ρ)))))
                          j
                          (transp (λ i → El (B ((σ (transp (λ _ → El Δ) (i ∨ j) ρ)) , transp (λ _ → El (A (σ (transp (λ _ → El Δ) (i ∨ j) ρ)))) (~ i ∨ j) (a (σ (transp (λ _ → El Δ) _ ρ))))))
                                  j
                                  (b (σ (transp (λ _ → El Δ) j ρ))))
    in symP (toPathP goal)))

