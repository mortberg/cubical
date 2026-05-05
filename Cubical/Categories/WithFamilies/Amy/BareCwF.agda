-- {-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.WithFamilies.Amy.BareCwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

open import Cubical.Data.Sigma

-- open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
-- open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level

-- TODO: upstream and add some levels?
_⊔_ : Level → Level → Level
ℓ ⊔ ℓ' = ℓ-max ℓ ℓ'

infixr 20 _⊔_

data Con : Type
data Ty  : Con → Type
data Tms : Con → Con → Type
data Tm  : ∀ Γ → Ty Γ → Type

private variable
  Γ Δ Θ Ψ : Con
  A B C : Ty Γ
  ρ σ δ ν : Tms Γ Δ
  x y z : Tm Γ A

data Con where
  []  : Con
  _,_ : (Γ : Con) → Ty Γ → Con

private
  _[_]T' : Ty Δ → Tms Γ Δ → Ty Γ
  _[_]t' : Tm Δ A → (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T')

--  ε'   : Tms Γ []
--  _,'_ : (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T') → Tms Γ (Δ , A)
--  id'  : Tms Γ Γ
  _∘'_ : Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  π₁'  : Tms Γ (Δ , A) → Tms Γ Δ
  [][]T' : A [ δ ]T' [ σ ]T' ≡ A [ δ ∘' σ ]T'

  π₂'  : (δ : Tms Γ (Δ , A)) → Tm Γ (A [ π₁' δ ]T')

data Tms where
  ε   : Tms Γ []
  _,_ : (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T') → Tms Γ (Δ , A)
  id  : Tms Γ Γ
  _∘_ : Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  π₁  : Tms Γ (Δ , A) → Tms Γ Δ

  idl   : id ∘ σ ≡ σ
  idr   : σ ∘ id ≡ σ
  assoc : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

  ,∘
    : ∀ {Γ Δ Θ} (δ : Tms Δ Γ) (σ : Tms Θ Δ) (t : Ty Γ) {x : Tm Δ (t [ δ ]T')} {y : Tm Θ (t [ δ ∘' σ ]T')}
    → PathP (λ i → Tm Θ ([][]T' {A = t} {δ = δ} {σ = σ} i)) (x [ σ ]t') y
    → (δ , x) ∘ σ ≡ ((δ ∘' σ) , y)

  π₁β : π₁ (δ , x) ≡ δ
  πη  : δ ≡ (π₁' δ , π₂' δ)
  εη  : (σ : Tms Γ []) → ε ≡ σ

  squash : isSet (Tms Γ Δ)

data Ty where
  _[_]T : Ty Δ → Tms Γ Δ → Ty Γ

  [id]T : A [ id ]T' ≡ A
  [][]T : A [ δ ]T' [ σ ]T' ≡ A [ δ ∘' σ ]T'

  squash : isSet (Ty Γ)

_[_]T' = _[_]T
--ε'     = ε
--_,'_   = _,_
--id'    = id
_∘'_   = _∘_
π₁'    = π₁
[][]T' = [][]T

data Tm where
  _[_]t : Tm Δ A → (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T)
  π₂    : (δ : Tms Γ (Δ , A)) → Tm Γ (A [ π₁ δ ]T)

  [id]t : {x : Tm Γ A} → PathP (λ i → Tm Γ ([id]T {A = A} i)) (x [ id ]t) x
  [][]t : {x : Tm Γ A} → PathP (λ i → Tm Γ ([][]T {A = A} {δ = δ} {σ = σ} i)) (x [ δ ]t [ σ ]t) (x [ δ ∘ σ ]t)
  π₂β   : PathP (λ i → Tm Γ (A [ π₁β {δ = δ} {x = x} i ]T)) (π₂ (δ , x)) x

  squash : isSet (Tm Γ A)

_[_]t' = _[_]t
π₂'    = π₂

wk : Tms (Γ , A) Γ
wk = π₁ id

vz : Tm (Γ , A) (A [ wk ]T)
vz = π₂ id

vs : Tm Γ A → Tm (Γ , B) (A [ wk ]T)
vs x = x [ wk ]t



record Motives ℓ ℓ' ℓ'' ℓ''' : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')))) where
  field
    Conᴹ : Con → Type ℓ
    Tyᴹ  : Conᴹ Γ → Ty Γ → Type ℓ'
    Tmsᴹ
      : Conᴹ Δ → Conᴹ Γ
      → Tms Δ Γ → Type ℓ''
    Tmᴹ
      : (Γᴹ : Conᴹ Γ) → Tyᴹ Γᴹ A
      → Tm Γ A
      → Type ℓ'''


module _ {ℓ ℓ' ℓ'' ℓ'''} (M : Motives ℓ ℓ' ℓ'' ℓ''') where
  open Motives M
  private variable
    Γᴹ Δᴹ Θᴹ Ψᴹ : Conᴹ Γ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ A
    ρᴹ σᴹ δᴹ νᴹ : Tmsᴹ Γᴹ Δᴹ ρ
    xᴹ yᴹ zᴹ : Tmᴹ Γᴹ Aᴹ x

  record Methods : Type (ℓ-suc (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ''')) where
    field
      Tyᴹ-is-set  : isSet (Tyᴹ Γᴹ A)
      Tmᴹ-is-set  : isSet (Tmᴹ Γᴹ Aᴹ x)
      Tmsᴹ-is-set : isSet (Tmsᴹ Γᴹ Δᴹ ρ)

      []ᴹ  : Conᴹ []
      _,ᴹ_ : (Γᵐ : Conᴹ Γ) → Tyᴹ Γᵐ A → Conᴹ (Γ , A)

      _[_]Tᴹ : ∀ {Γ Δ} {σ : Tms Γ Δ} {A : Ty Δ} {Δᴹ : Conᴹ Δ} {Γᴹ : Conᴹ Γ} → Tyᴹ Δᴹ A → Tmsᴹ Γᴹ Δᴹ σ → Tyᴹ Γᴹ (A [ σ ]T)


      εᴹ : ∀ {Γ} (Γᴹ : Conᴹ Γ) → Tmsᴹ Γᴹ []ᴹ ε
      idᴹ  : Tmsᴹ Γᴹ Γᴹ id
      _∘ᴹ_ : (ρᴹ : Tmsᴹ Δᴹ Θᴹ ρ) (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) → Tmsᴹ Γᴹ Θᴹ (ρ ∘ σ)
      π₁ᴹ  : Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ → Tmsᴹ Γᴹ Δᴹ (π₁ σ)
      _▶ᴹ_
        : {δ : Tms Γ Δ} {x : Tm Γ (A [ δ ]T')}
        → {Γᴹ : Conᴹ Γ} {Δᴹ : Conᴹ Δ}
        → (δᴹ : Tmsᴹ Γᴹ Δᴹ δ)
        → {Aᴹ : Tyᴹ Δᴹ A}
        → Tmᴹ Γᴹ (Aᴹ [ δᴹ ]Tᴹ) x
        → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) (δ , x)

      _[_]tᴹ : Tmᴹ Δᴹ Aᴹ x → (δᴹ : Tmsᴹ Γᴹ Δᴹ δ) → Tmᴹ Γᴹ (Aᴹ [ δᴹ ]Tᴹ) (x [ δ ]t)

      π₂ᴹ  : (δᴹ : Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) δ) → Tmᴹ Γᴹ (Aᴹ [ π₁ᴹ δᴹ ]Tᴹ) (π₂ δ)

      idlᴹ   : (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) → PathP (λ i → Tmsᴹ Γᴹ Δᴹ (idl {σ = σ} i)) (idᴹ ∘ᴹ σᴹ) σᴹ
      idrᴹ   : (σᴹ : Tmsᴹ Γᴹ Δᴹ σ) → PathP (λ i → Tmsᴹ Γᴹ Δᴹ (idr {σ = σ} i)) (σᴹ ∘ᴹ idᴹ) σᴹ
      assocᴹ
        : (σᴹ : Tmsᴹ Δᴹ Θᴹ σ) (δᴹ : Tmsᴹ Γᴹ Δᴹ δ) (νᴹ : Tmsᴹ Ψᴹ Γᴹ ν)
        → PathP (λ i → Tmsᴹ Ψᴹ Θᴹ (assoc {σ = σ} {δ = δ} {ν = ν} i))
            ((σᴹ ∘ᴹ δᴹ) ∘ᴹ νᴹ) (σᴹ ∘ᴹ (δᴹ ∘ᴹ νᴹ))

      [id]Tᴹ : PathP (λ i → Tyᴹ Γᴹ ([id]T {A = A} i)) (Aᴹ [ idᴹ ]Tᴹ) Aᴹ
      [][]Tᴹ : PathP (λ i → Tyᴹ Γᴹ ([][]T {A = A} {δ = δ} {σ = σ} i))
        (Aᴹ [ δᴹ ]Tᴹ [ σᴹ ]Tᴹ) (Aᴹ [ δᴹ ∘ᴹ σᴹ ]Tᴹ)

      ,∘ᴹ
        : ∀ (δᴹ : Tmsᴹ Δᴹ Γᴹ δ) (σᴹ : Tmsᴹ Θᴹ Δᴹ σ) (Aᴹ : Tyᴹ Γᴹ A) {xᴹ : Tmᴹ Δᴹ (Aᴹ [ δᴹ ]Tᴹ) x} {yᴹ : Tmᴹ Θᴹ (Aᴹ [ δᴹ ∘ᴹ σᴹ ]Tᴹ) y}
        → (p : PathP (λ i → Tm Θ ([][]T' {A = A} {δ = δ} {σ = σ} i)) (x [ σ ]t') y)
        → PathP (λ i → Tmᴹ Θᴹ ([][]Tᴹ {Aᴹ = Aᴹ} {δᴹ = δᴹ} {σᴹ = σᴹ} i) (p i)) (xᴹ [ σᴹ ]tᴹ) yᴹ
        → PathP (λ i → Tmsᴹ Θᴹ (Γᴹ ,ᴹ Aᴹ) (,∘ δ σ A {x} {y} p i)) ((δᴹ ▶ᴹ xᴹ) ∘ᴹ σᴹ) (((δᴹ ∘ᴹ σᴹ) ▶ᴹ yᴹ))

      π₁βᴹ
        : ∀ {δᴹ : Tmsᴹ Δᴹ Γᴹ δ} {xᴹ : Tmᴹ _ (Aᴹ [ δᴹ ]Tᴹ) x}
        → PathP (λ i → Tmsᴹ Δᴹ Γᴹ (π₁β {δ = δ} {x = x} i)) (π₁ᴹ (δᴹ ▶ᴹ xᴹ)) δᴹ

      πηᴹ  : ∀ {δᴹ : Tmsᴹ Δᴹ (Γᴹ ,ᴹ Aᴹ) δ} → PathP (λ i → Tmsᴹ Δᴹ (Γᴹ ,ᴹ Aᴹ) (πη {δ = δ} i)) δᴹ (π₁ᴹ δᴹ ▶ᴹ π₂ᴹ δᴹ)
      εηᴹ  : (σᴹ : Tmsᴹ Γᴹ []ᴹ σ) → PathP (λ i → Tmsᴹ Γᴹ []ᴹ (εη σ i)) (εᴹ Γᴹ) σᴹ

      [id]tᴹ : PathP (λ i → Tmᴹ Δᴹ ([id]Tᴹ {Aᴹ = Aᴹ} i) ([id]t {x = x} i)) (xᴹ [ idᴹ ]tᴹ) xᴹ
      [][]tᴹ : PathP (λ i → Tmᴹ Δᴹ ([][]Tᴹ {Aᴹ = Aᴹ} {δᴹ = δᴹ} {σᴹ = σᴹ} i) ([][]t {x = x} i))
        ((xᴹ [ δᴹ ]tᴹ) [ σᴹ ]tᴹ) (xᴹ [ δᴹ ∘ᴹ σᴹ ]tᴹ)
      π₂βᴹ : PathP (λ i → Tmᴹ Δᴹ (Aᴹ [ π₁βᴹ {δᴹ = δᴹ} {xᴹ = xᴹ} i ]Tᴹ) (π₂β {x = x} i)) (π₂ᴹ (δᴹ ▶ᴹ xᴹ)) xᴹ

    Con-elim : ∀ x → Conᴹ x
    Tms-elim : ∀ {Δ Γ} (σ : Tms Δ Γ) → Tmsᴹ (Con-elim Δ) (Con-elim Γ) σ
    Ty-elim  : ∀ {Γ} (A : Ty Γ) → Tyᴹ (Con-elim Γ) A
    Tm-elim  : ∀ {Δ} {A : Ty Δ} (x : Tm Δ A) → Tmᴹ (Con-elim Δ) (Ty-elim A) x

    Con-elim []      = []ᴹ
    Con-elim (Γ , x) = Con-elim Γ ,ᴹ Ty-elim x

    Ty-elim (A [ x ]T)   = Ty-elim A [ Tms-elim x ]Tᴹ
    Ty-elim ([id]T {A = A} i) =
      [id]Tᴹ {Aᴹ = Ty-elim A} i
    Ty-elim ([][]T {A = A} {δ = δ} {σ = σ} i) =
      [][]Tᴹ {Aᴹ = Ty-elim A} {δᴹ = Tms-elim δ} {σᴹ = Tms-elim σ} i
    Ty-elim (squash x y p q i j) = isSet→SquareP (λ i j → Tyᴹ-is-set {A = squash x y p q i j}) (λ i → Ty-elim (p i)) (λ i → Ty-elim (q i)) (λ i → Ty-elim x) (λ i → Ty-elim y) i j

    Tms-elim {Δ} ε    = εᴹ (Con-elim Δ)
    Tms-elim (σ , x)  = Tms-elim σ ▶ᴹ Tm-elim x
    Tms-elim id       = idᴹ
    Tms-elim (σ ∘ ρ) = Tms-elim σ ∘ᴹ Tms-elim ρ
    Tms-elim (π₁ σ)   = π₁ᴹ (Tms-elim σ)
    Tms-elim (idl {σ = σ} i) = idlᴹ (Tms-elim σ) i
    Tms-elim (idr {σ = σ} i) = idrᴹ (Tms-elim σ) i
    Tms-elim (assoc {σ = σ} {δ = δ} {ν = ν} i) = assocᴹ (Tms-elim σ) (Tms-elim δ) (Tms-elim ν) i
    Tms-elim (squash x y p q i j) = isSet→SquareP (λ i j → Tmsᴹ-is-set {ρ = squash x y p q i j}) (λ i → Tms-elim (p i)) (λ i → Tms-elim (q i)) (λ i → Tms-elim x) (λ i → Tms-elim y) i j

    Tms-elim (,∘ σ δ t {x} {y} p i) = ,∘ᴹ (Tms-elim σ) (Tms-elim δ) (Ty-elim t) {Tm-elim x} {Tm-elim y} p p' i where
      p' : PathP (λ i → Tmᴹ (Con-elim _) ([][]Tᴹ i) (p i)) (Tm-elim x [ Tms-elim δ ]tᴹ) (Tm-elim y)
      p' j = Tm-elim (p j)

    Tms-elim (π₁β {δ = δ} {x = x} i) = π₁βᴹ {δᴹ = Tms-elim δ} {Tm-elim x} i
    Tms-elim (πη {δ = δ} i) = πηᴹ {δᴹ = Tms-elim δ} i
    Tms-elim (εη σ i)       = εηᴹ (Tms-elim σ) i

    Tm-elim (x [ δ ]t)  = Tm-elim x [ Tms-elim δ ]tᴹ
    Tm-elim (π₂ δ)      = π₂ᴹ (Tms-elim δ)
    Tm-elim ([id]t {x = x} i) =
      [id]tᴹ {xᴹ = Tm-elim x} i
    Tm-elim ([][]t {δ = δ} {σ} {x} i) = [][]tᴹ {δᴹ = Tms-elim δ} {σᴹ = Tms-elim σ} {xᴹ = Tm-elim x} i
    Tm-elim (π₂β {δ = δ} {x = x} i)   = π₂βᴹ {δᴹ = Tms-elim δ} {xᴹ = Tm-elim x} i
    Tm-elim (squash x y p q i j) = isSet→SquareP (λ i j → Tmᴹ-is-set {x = squash x y p q i j}) (λ i → Tm-elim (p i)) (λ i → Tm-elim (q i)) (λ i → Tm-elim x) (λ i → Tm-elim y) i j

open Motives

module Internal (U : Type ℓ)
         (isSetU : isSet U)
         (El : U → Type ℓ')
         (isSetEl : (a : U) → isSet (El a))
         (Unit : U)
         (UnitTerminal : isContr (El Unit))
         (Sig : (a : U) → (El a → U) → U)
         (SigIso : (a : U) (b : El a → U) → Iso (El (Sig a b)) (Σ[ x ∈ El a ] El (b x)))
         where

  U-modelᴹ : Motives _ _ _ _
  U-modelᴹ .Conᴹ     _ = U
  U-modelᴹ .Tyᴹ  Γ   _ = El Γ → U
  U-modelᴹ .Tmsᴹ Γ Δ _ = El Γ → El Δ
  U-modelᴹ .Tmᴹ  Γ A _ = (x : El Γ) → El (A x)

  open Methods
  open Iso

  U-model : Methods U-modelᴹ
  U-model .Tyᴹ-is-set = isSet→ isSetU
  U-model .Tmᴹ-is-set = isSetΠ (λ _ → isSetEl _)
  U-model .Tmsᴹ-is-set = isSet→ (isSetEl _)
  U-model .[]ᴹ = Unit
  U-model ._,ᴹ_ = Sig
  U-model ._[_]Tᴹ = λ A f γ → A (f γ)
  U-model .εᴹ = λ _ _ → UnitTerminal .fst
  U-model .idᴹ = λ x → x
  U-model ._∘ᴹ_ = λ ρ δ x → ρ (δ x)
  U-model .π₁ᴹ σ γ = SigIso _ _ .fun (σ γ) .fst
  U-model ._▶ᴹ_ δ x y = SigIso _ _ .inv (δ y , x y)
  U-model ._[_]tᴹ x δ γ = x (δ γ)
  U-model .π₂ᴹ σ γ = SigIso _ _ .fun (σ γ) .snd
  U-model .idlᴹ _ = refl
  U-model .idrᴹ _ = refl
  U-model .assocᴹ _ _ _ = refl
  U-model .[id]Tᴹ = refl
  U-model .[][]Tᴹ = refl
  U-model .,∘ᴹ = λ δᴹ σᴹ Aᴹ p x₁ i x₂ → inv (SigIso _ _) (δᴹ (σᴹ x₂) , x₁ i x₂)
  U-model .π₁βᴹ = funExt (λ x → cong fst (SigIso _ _ .sec _))
  U-model .πηᴹ = funExt (λ x → sym (SigIso _ _ .ret _))
  U-model .εηᴹ x = funExt (λ y → UnitTerminal .snd _)
  U-model .[id]tᴹ = refl
  U-model .[][]tᴹ = refl
  U-model .π₂βᴹ {δᴹ = g} {xᴹ = f} = funExt (λ x →  cong snd (SigIso _ _ .sec (g x , f x)))

  Std-con : Con → Type ℓ'
  Std-con Γ = El (Con-elim U-model Γ)

  Std-tms : ∀ {Δ Γ} → Tms Δ Γ → Std-con Δ → Std-con Γ
  Std-tms ρ γ = Tms-elim U-model ρ γ

  Std-ty : ∀ {Γ} (A : Ty Γ) (γ : Std-con Γ) → Type ℓ'
  Std-ty A γ = El (Ty-elim U-model A γ)

  Std-tm : ∀ {Δ} {A : Ty Δ} (x : Tm Δ A) (γ : Std-con Δ) → Std-ty A γ
  Std-tm x γ = Tm-elim U-model x γ
