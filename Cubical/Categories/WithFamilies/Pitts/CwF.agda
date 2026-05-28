{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.WithFamilies.Pitts.CwF where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Data.Sigma

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level

module _ {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where

  open Category C hiding (_⋆_)

  Ctx = Category.ob C

  _⟶_ : (Δ Γ : Ctx) → Type ℓHom
  Δ ⟶ Γ = C [ Δ , Γ ]

  infix 20 _⟶_

  variable
    Γ Δ Θ : Ctx

  record CwF (ℓTy ℓTm : Level) :
             Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTy  ℓTm)))) where
    field
      -- Empty context
      ⟨⟩ : Terminal C

      -- | Types

      Ty : (Γ : Ctx) → Type ℓTy

      _[_]Ty : (A : Ty Γ) (σ : Δ ⟶ Γ)
             → ----------------------
               Ty Δ

      [id]Ty : (A : Ty Γ)
             → ----------------
               A [ id ]Ty ≡ A

      [][]Ty : (A : Ty Γ) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
             → -------------------------------------------
               A [ σ ∘ σ' ]Ty ≡ (A [ σ ]Ty ) [ σ' ]Ty

      -- | Terms

      Tm : (Γ : Ctx) (A : Ty Γ) → Type ℓTm

      _[_]Tm : {A : Ty Γ} (a : Tm Γ A) (σ : Δ ⟶ Γ)
             → -----------------------------------
               Tm Δ (A [ σ ]Ty)

      [id]Tm : {A : Ty Γ} (a : Tm Γ A)
             → ------------------------------------------------
               PathP (λ i → Tm Γ ([id]Ty A i)) (a [ id ]Tm) a

      [][]Tm : {A : Ty Γ} (a : Tm Γ A) (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
             → ------------------------------------------------
                PathP (λ i → Tm Θ ([][]Ty A σ' σ i))
                      (a [ σ ∘ σ' ]Tm)
                      (a [ σ ]Tm [ σ' ]Tm)

      -- | Comprehension objects

      _⋆_ : (Γ : Ctx) (A : Ty Γ) → Ctx

      p : {A : Ty Γ} → (Γ ⋆ A) ⟶ Γ

      q : {A : Ty Γ} → Tm (Γ ⋆ A) (A [ p ]Ty)

      ⟨_,_⟩ : {A : Ty Γ} (σ : Δ ⟶ Γ) (a : Tm Δ (A [ σ ]Ty))
            → ---------------------------------------------
              C [ Δ , Γ ⋆ A ]

      p⟨⟩ : {A : Ty Γ} (σ : Δ ⟶ Γ) (a : Tm Δ (A [ σ ]Ty))
          → ---------------------------------------------
            p ∘ ⟨ σ , a ⟩ ≡ σ

      -- This is redundant, but makes instantiating easier
      coerce : {A : Ty Γ} (σ : Δ ⟶ Γ)
              (a : Tm Δ (A [ σ ]Ty))
            → A [ p ]Ty [ ⟨ σ , a ⟩ ]Ty ≡ A [ σ ]Ty

      q⟨⟩ : {A : Ty Γ} (σ : Δ ⟶ Γ)
            (a : Tm Δ (A [ σ ]Ty))
          → -----------------------------------------------
            PathP (λ i → Tm Δ (coerce σ a i)) ( q [ ⟨ σ , a ⟩ ]Tm) a

      ⟨⟩∘ : {A : Ty Γ} (σ' : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (a : Tm Δ (A [ σ ]Ty))

            -- Used to represent a[σ'] so that we don't need subst/transport
            {a' : Tm Θ (A [ σ ∘ σ' ]Ty)}
            (pa' : PathP (λ i → Tm Θ ([][]Ty A σ' σ i)) a' (a [ σ' ]Tm))
          → ----------------------------------------------------------------
            ⟨ σ , a ⟩ ∘ σ' ≡ ⟨ σ ∘ σ' , a' ⟩

      ⟨p,q⟩ : (A : Ty Γ)
            → ------------------------
              ⟨ p {A = A} , q ⟩ ≡ id

    infix 30 _[_]Ty
    infix 30 _[_]Tm
    infix 20 _⋆_

  record Σ-Structure-CwF {ℓTy ℓTm : Level} (cwf : CwF ℓTy ℓTm) :
         Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓHom (ℓ-max ℓTm ℓTy)))) where

    open CwF cwf

    field
      ΣTy : (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Ty Γ

      pair : {A : Ty Γ} {B : Ty (Γ ⋆ A)}
             (a : Tm Γ A)
             (a' : Tm Γ (A [ id ]Ty))
             (pa' : PathP (λ i → Tm Γ ([id]Ty A (~ i))) a a')
             (b : Tm Γ (B [ ⟨ id , a' ⟩ ]Ty))
           → --------------------------------------------
             Tm Γ (ΣTy A B)

      fst : {A : Ty Γ} {B : Ty (Γ ⋆ A)}
            (c : Tm Γ (ΣTy A B))
          → ---------------------------
            Tm Γ A

      snd : {A : Ty Γ} {B : Ty (Γ ⋆ A)}
            (c : Tm Γ (ΣTy A B))
            (fstc : Tm Γ (A [ id ]Ty))
            (pfstc : PathP (λ i → Tm Γ ([id]Ty A (~ i))) (fst c) fstc)
          → ----------------------------------------------------------
            Tm Γ (B [ ⟨ id , fstc ⟩ ]Ty)

      -- Computation rules
      fstPair : {A : Ty Γ} {B : Ty (Γ ⋆ A)}
                (a : Tm Γ A)
                (a' : Tm Γ (A [ id ]Ty))
                (pa' : PathP (λ i → Tm Γ ([id]Ty A (~ i))) a a')
                (b : Tm Γ (B [ ⟨ id , a' ⟩ ]Ty))
              → ------------------------------------------------
                fst (pair a a' pa' b) ≡ a

      sndPair : {A : Ty Γ} {B : Ty (Γ ⋆ A)}
                (a : Tm Γ A)
                (a' : Tm Γ (A [ id ]Ty))
                (pa' : PathP (λ i → Tm Γ ([id]Ty A (~ i))) a a')
                (b : Tm Γ (B [ ⟨ id , a' ⟩ ]Ty))
                (fstc : Tm Γ (A [ id ]Ty))
                (pfstc : PathP (λ i → Tm Γ ([id]Ty A (~ i))) (fst (pair a a' pa' b)) fstc)
                (pfstca' : fstc ≡ a')
              → --------------------------------------------------------------------------------------
                PathP (λ i → Tm Γ ((B [ ⟨ id , pfstca' i ⟩ ]Ty))) (snd (pair a a' pa' b) fstc pfstc) b

      -- Uniqueness/eta rule:
      pairFstSnd : {A : Ty Γ} {B : Ty (Γ ⋆ A)}
                   (c : Tm Γ (ΣTy A B))
                   (fstc : Tm Γ (A [ id ]Ty))
                   (pfstc : PathP (λ i → Tm Γ ([id]Ty A (~ i))) (fst c) fstc)
                 → ------------------------------------------------------
                   pair (fst c) fstc pfstc (snd c fstc pfstc) ≡ c

      -- Naturality laws
      ΣTy[] : {A : Ty Γ} {B : Ty (Γ ⋆ A)} (σ : Δ ⟶ Γ)
              (q' : Tm (Δ ⋆ A [ σ ]Ty) (A [ σ ∘ p ]Ty))
              (pq' : PathP (λ i → Tm  (Δ ⋆ A [ σ ]Ty) ([][]Ty A p σ (~ i))) q q')
            → ---------------------------------------------------------------
              (ΣTy A B) [ σ ]Ty ≡ ΣTy (A [ σ ]Ty) (B [ ⟨ σ ∘ p , q' ⟩ ]Ty)

      -- (pair a b)[σ] = pair (a[σ]) (b[σ])
      pair[] : {A : Ty Γ} {B : Ty (Γ ⋆ A)} (σ : Δ ⟶ Γ)
               (q' : Tm (Δ ⋆ A [ σ ]Ty) (A [ σ ∘ p ]Ty))
               (pq' : PathP (λ i → Tm  (Δ ⋆ A [ σ ]Ty) ([][]Ty A p σ (~ i))) q q')
               (a : Tm Γ A)
               (a' : Tm Γ (A [ id ]Ty))
               (pa' : PathP (λ i → Tm Γ ([id]Ty A (~ i))) a a')
               (aσ : Tm Δ (A [ σ ]Ty [ id ]Ty))
               (paσ  : PathP (λ i → Tm Δ ([id]Ty (A [ σ ]Ty) (~ i))) (a [ σ ]Tm) aσ)
               (b : Tm Γ (B [ ⟨ id , a' ⟩ ]Ty))
               (bσ : Tm Δ ((B [ ⟨ σ ∘ p , q' ⟩ ]Ty) [ ⟨ id , aσ ⟩ ]Ty))
               (p : B [ ⟨ id , a' ⟩ ]Ty [ σ ]Ty ≡ B [ ⟨ σ ∘ p , q' ⟩ ]Ty [ ⟨ id , aσ ⟩ ]Ty)
               (pbσ : PathP (λ i → Tm Δ (p i)) (b [ σ ]Tm) bσ)
             → ----------------------------------------------------------------------------
               PathP (λ i → Tm Δ (ΣTy[] {B = B} σ q' pq' i))
                     ((pair a a' pa' b) [ σ ]Tm)
                     (pair (a [ σ ]Tm) aσ paσ bσ)

      -- (fst c)[σ] = fst (c[σ])
      fst[] : {A : Ty Γ} {B : Ty (Γ ⋆ A)} (σ : Δ ⟶ Γ)
              (c : Tm Γ (ΣTy A B))
              (q' : Tm (Δ ⋆ A [ σ ]Ty) (A [ σ ∘ p ]Ty))
              (pq' : PathP (λ i → Tm  (Δ ⋆ A [ σ ]Ty) ([][]Ty A p σ (~ i))) q q')
              (cσ : Tm Δ (ΣTy (A [ σ ]Ty) (B [ ⟨ σ ∘ p , q' ⟩ ]Ty)))
              (pcσ : PathP (λ i → Tm Δ (ΣTy[] {B = B} σ q' pq' i)) (c [ σ ]Tm) cσ)
            → --------------------------------------------------------------------
              (fst c) [ σ ]Tm ≡ fst cσ

      -- (snd c)[σ] = snd (c[σ])
      snd[] : {A : Ty Γ} {B : Ty (Γ ⋆ A)} (σ : Δ ⟶ Γ)
              (c : Tm Γ (ΣTy A B))
              (q' : Tm (Δ ⋆ A [ σ ]Ty) (A [ σ ∘ p ]Ty))
              (pq' : PathP (λ i → Tm  (Δ ⋆ A [ σ ]Ty) ([][]Ty A p σ (~ i))) q q')
              (fstc : Tm Γ (A [ id ]Ty))
              (pfstc : PathP (λ i → Tm Γ ([id]Ty A (~ i))) (fst c) fstc)
              (cσ : Tm Δ (ΣTy (A [ σ ]Ty) (B [ ⟨ σ ∘ p , q' ⟩ ]Ty)))
              (pcσ : PathP (λ i → Tm Δ (ΣTy[] {B = B} σ q' pq' i)) (c [ σ ]Tm) cσ)
              (fstcσ : Tm Δ ((A [ σ ]Ty) [ id ]Ty))
              (pfstcσ : PathP (λ i → Tm Δ ([id]Ty (A [ σ ]Ty) (~ i))) (fst cσ) fstcσ)
              (p : B [ ⟨ id , fstc ⟩ ]Ty [ σ ]Ty ≡ B [ ⟨ σ ∘ p , q' ⟩ ]Ty [ ⟨ id , fstcσ ⟩ ]Ty)
            → ---------------------------------------------------------------------------------
              PathP (λ i → Tm Δ (p i)) ((snd c fstc pfstc) [ σ ]Tm) (snd cσ fstcσ pfstcσ)

module V {ℓ : Level} where

  open import Cubical.Data.IterativeSets.Base renaming (V⁰ to V ; El⁰ to El ; isSetEl⁰ to isSetEl)
  open import Cubical.Data.IterativeSets.Sigma
  open import Cubical.Data.IterativeSets.Unit
  open import Agda.Builtin.Unit

  open Category

  VCat : Category (ℓ-suc ℓ) ℓ
  VCat .ob       = V
  VCat .Hom[_,_] = λ Δ Γ → El Δ → El Γ
  VCat .id       = λ x → x
  VCat ._⋆_      = λ f g x → g (f x)
  VCat .⋆IdL     = λ _ → refl
  VCat .⋆IdR     = λ _ → refl
  VCat .⋆Assoc   = λ _ _ _ → refl
  VCat .isSetHom {y = y} = isSet→ (isSetEl y)

  open CwF
  open Iso

  VCwF : CwF VCat (ℓ-suc ℓ) ℓ
  VCwF .⟨⟩                 = unit⁰ , λ _ → (λ _ → lift tt) , λ _ _ _ → lift tt
  VCwF .Ty Γ               = El Γ → V {ℓ}
  VCwF ._[_]Ty A σ x       = A (σ x)
  VCwF .[id]Ty _           = refl
  VCwF .[][]Ty _ _ _       = refl
  VCwF .Tm Γ A             = (x : El Γ) → El (A x)
  VCwF ._[_]Tm a σ x       = a (σ x)
  VCwF .[id]Tm _           = refl
  VCwF .[][]Tm _ _ _       = refl
  VCwF ._⋆_                = Σ⁰
  VCwF .p                  = fst
  VCwF .q                  = snd
  VCwF .⟨_,_⟩ σ a x        = (σ x) , a x
  VCwF .p⟨⟩ σ a            = refl
  VCwF .coerce σ a         = refl
  VCwF .q⟨⟩ σ a            = refl
  VCwF .⟨⟩∘ σ' σ a pa' i x = σ (σ' x) , pa' (~ i) x
  VCwF .⟨p,q⟩ _            = refl

  open Σ-Structure-CwF

  goal : Σ-Structure-CwF VCat VCwF
  goal .ΣTy A B x  = Σ⁰ (A x) (λ y → B (x , y))
  goal .pair a a' pa' b x .fst = a x
  goal .pair {B = B} a a' pa' b x .snd = subst⁻ (λ a → El (B (x , a x))) pa' (b x)
  goal .fst c x = fst (c x)
  goal .snd {B = B} c fstc pfstc x = subst (λ f → El (B (x , f x))) pfstc (snd (c x)) -- J> (λ x → snd (c x))
  goal .fstPair a _ _ _ = refl
  goal .sndPair {A = A} {B = B} a =
    J> (λ b → J> (λ pfstca' → funExt (λ x → toPathP (
        let rem : pfstca' ≡ refl
            rem = isSetΠ (λ z → isSetEl (A z)) _ a pfstca' refl
        in cong (transport (λ z → El (B (x , pfstca' z x))))
                (substSubst⁻ {x = a} (λ f → El (B (x , f x))) refl (b x))
         ∙ subst⁻ (λ p → transport (λ z → El (B (x , p z x))) (b x) ≡ b x) rem (transportRefl _)))))
  goal .pairFstSnd {Γ = Γ} {A = A} {B = B} c =
    J> funExt (λ x → ΣPathP ( refl
                            , subst⁻Subst {A = (z : El Γ) → El (A z)}
                                          {x = λ z → fst (c z)}
                                          (λ f → El (B (x , f x))) refl (snd (c x))))
  goal .ΣTy[] {A = A} {B = B} σ q' pq' =
    funExt (λ x → cong (Σ⁰ (A (σ x)))
                       (funExt (λ y → cong B (λ i → (σ x) , (pq' i  (x , y))))))
  goal .pair[] {Δ = Δ} {A = A} {B = B} σ =
    J> λ a → J> (J> (λ b bσ p pbσ →
      let rem : p ≡ refl
          rem = isSet→ isSetV⁰ _ _ p refl
      in funExt (λ z → ΣPathP ( refl
                              , cong (transport refl)
                                     (subst (λ p → PathP (λ i → El (p i z)) (b (σ z)) (bσ z))
                                            rem
                                            (funExt⁻ pbσ z))))))
  goal .fst[]      = λ σ c q' pq' cσ pcσ i x → fst (pcσ i x)
  goal .snd[] {Δ = Δ} {B = B} σ c     =
    J> (J> (J> (J> (λ p →
      let rem : p ≡ refl
          rem = isSet→ isSetV⁰ _ _ p refl
          goalType : (z : El Δ) (p : _) → Type ℓ
          goalType z p = PathP (λ i → El (p i z))
                               (subst (λ f → El (B (σ z , f))) refl (snd (c (σ z))))
                               (subst (λ f → El (B (σ z , f))) refl (snd (c (σ z))))
      in funExt (λ z → subst⁻ (λ p₁ → goalType z p₁) rem refl)))))












-- TODO: generalize


-- module Tarski (U : Type ℓ)
--               (isSetU : isSet U)
--               (El : U → Type ℓ')
--               (isSetEl : (a : U) → isSet (El a))
--               (Unit : U)
--               (UnitTerminal : isContr (El Unit))
--               (Sig : (a : U) → (El a → U) → U)
--               (SigIso : (a : U) (b : El a → U) → Iso (El (Sig a b)) (Σ[ x ∈ El a ] El (b x))) where

--   open Category

--   UCtx : Category ℓ ℓ'
--   UCtx .ob       = U
--   UCtx .Hom[_,_] = λ Δ Γ → El Δ → El Γ
--   UCtx .id       = λ x → x
--   UCtx ._⋆_      = λ f g x → g (f x)
--   UCtx .⋆IdL     = λ _ → refl
--   UCtx .⋆IdR     = λ _ → refl
--   UCtx .⋆Assoc   = λ _ _ _ → refl
--   UCtx .isSetHom = isSet→ (isSetEl _)

--   open CwF
--   open Iso

--   UCwF : CwF UCtx (ℓ-max ℓ ℓ') ℓ'
--   UCwF .⟨⟩           = Unit , (λ _ → isContrΠ (λ _ → UnitTerminal))
--   UCwF .Ty Γ         = El Γ → U
--   UCwF ._[_]Ty A σ x = A (σ x)
--   UCwF .[id]Ty _     = refl
--   UCwF .[][]Ty _ _ _ = refl
--   UCwF .Tm Γ A       = (x : El Γ) → El (A x)
--   UCwF ._[_]Tm a σ x = a (σ x)
--   UCwF .[id]Tm _     = refl
--   UCwF .[][]Tm _ _ _ = refl
--   UCwF ._⋆_          = Sig
--   UCwF .p            = λ x → SigIso _ _ .fun x .fst
--   UCwF .q            = λ x → SigIso _ _ .fun x .snd
--   UCwF .⟨_,_⟩        = λ σ a x → SigIso _ _ .inv (σ x , a x)
--   UCwF .p⟨⟩          = λ σ a i x → fst (SigIso _ _ .sec (σ x , a x) i)
--   UCwF .q⟨⟩          = λ σ a p → funExt (λ x → {!cong snd (SigIso _ _ .sec (σ x , a x))!})
--   UCwF .⟨⟩∘          = {!!}
--   UCwF .⟨p,q⟩        = {!!}
