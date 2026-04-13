module Cubical.Categories.WithFamilies.Universes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Instances.Elements

open import Cubical.Categories.WithFamilies.Base

private
  variable ℓ ℓ' ℓ'' ℓ''' : Level

open Functor

module External (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ)
         (ElSet : (a : U) → isSet (El a))
         where

  UCwF : CwF (SET ℓ) ℓ ℓ
  UCwF .CwF.emptyContext .fst .fst = Unit*
  UCwF .CwF.emptyContext .fst .snd _ _ _ _ = refl
  UCwF .CwF.emptyContext .snd _ .fst _ = tt*
  UCwF .CwF.emptyContext .snd _ .snd _ = refl

  UCwF .CwF.tyPresheaf .F-ob Γ .fst = Γ .fst → U
  UCwF .CwF.tyPresheaf .F-ob Γ .snd = isSet→ USet
  UCwF .CwF.tyPresheaf .F-hom f g = g ∘ f
  UCwF .CwF.tyPresheaf .F-id = refl
  UCwF .CwF.tyPresheaf .F-seq _ _ = refl

  UCwF .CwF.tmPresheaf .F-ob (Γ , A) .fst = (x : Γ .fst) → El (A x)
  UCwF .CwF.tmPresheaf .F-ob (Γ , A) .snd = isSetΠ (λ x → ElSet (A x))
  UCwF .CwF.tmPresheaf .F-hom {Γ , A} {Δ , B} (f , p) x y = subst El (funExt⁻ p y) (x (f y))
  UCwF .CwF.tmPresheaf .F-id {Γ , A} = funExt (λ x → funExt (λ y → substRefl {B = El} (x y)))
  UCwF .CwF.tmPresheaf .F-seq {Γ , A} {Δ , B} {Ε , C} (f , p) (g , q) = funExt (λ x → funExt (λ y → substComposite El (funExt⁻ p (g y)) (funExt⁻ q y) (x (f (g y)))))

  UCwF .CwF.ctxExtFunctor .F-ob (Γ , A) .fst = Σ[ x ∈ Γ .fst ] El (A x)
  UCwF .CwF.ctxExtFunctor .F-ob (Γ , A) .snd = isSetΣ (Γ .snd) (λ x → ElSet (A x))
      
  UCwF .CwF.ctxExtFunctor .F-hom {Γ , A} {Δ , B} (f , p) (a , b) .fst = f a
  UCwF .CwF.ctxExtFunctor .F-hom {Γ , A} {Δ , B} (f , p) (a , b) .snd = subst El (sym (funExt⁻ p a)) b
  UCwF .CwF.ctxExtFunctor .F-id {Γ , A} = funExt (λ (a , b) → cong (λ m → a , m) (substRefl {B = El} b))
  UCwF .CwF.ctxExtFunctor .F-seq {Γ , A} {Δ , B} {Ε , C} (f , p) (g , q) = funExt (λ (a , b) → cong (λ m → g (f a) , m) (let
      p₁ : Path U (A a) (C (g (f a)))
      p₁ i = hcomp (λ i₁ .o → doubleComp-faces (λ i₂ x → C (g (f x))) p (~ i) i₁ o a) (q (~ i) (f a))

      p₂ : Path U (A a) (C (g (f a)))
      p₂ = (sym (funExt⁻ p a)) ∙ (sym (funExt⁻ q (f a)))

      p₂≡p₁ : p₂ ≡ p₁
      p₂≡p₁ = USet (A a) (C (g (f a))) p₂ p₁

      T₁ : Type ℓ
      T₁ = subst El p₁ b ≡ subst⁻ El (funExt⁻ q (f a)) (subst⁻ El (funExt⁻ p a) b)

      T₂ : Type ℓ
      T₂ = subst El p₂ b ≡ subst⁻ El (funExt⁻ q (f a)) (subst⁻ El (funExt⁻ p a) b)

      T₂≡T₁ : T₂ ≡ T₁
      T₂≡T₁ = cong (λ m → subst El m b ≡ subst⁻ El (funExt⁻ q (f a)) (subst⁻ El (funExt⁻ p a) b)) p₂≡p₁
      -- T₂≡T₁ i = subst El (p₂≡p₁ i) b ≡ subst⁻ El (funExt⁻ q (f a)) (subst⁻ El (funExt⁻ p a) b)

      goal' : T₂
      goal' = substComposite {A = U} El (λ i → funExt⁻ p a (~ i)) (λ i → funExt⁻ q (f a) (~ i)) b

      goal : T₁
      goal = transport T₂≡T₁ goal'
    in goal))

  UCwF .CwF.ctxExtEquiv Γ Δ A = {!idEquiv _!}
  UCwF .CwF.special-ty-rev-assoc-proof = {!!}
  UCwF .CwF.ctxExtEquivNat = {!!}

module Internal (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ')
         (ElSet : (a : U) → isSet (El a))
         (Unit : U)
         (UnitTerminal : (a : U) → isContr (El a → El Unit)) -- isContr (El Unit)
         (Sig : (a : U) → (El a → U) → U)
         (SigIso : (a : U) (b : El a → U) → El (Sig a b) ≃ (Σ[ x ∈ El a ] El (b x)))
         where

  UCat : Category ℓ ℓ'
  UCat .Category.ob = U
  UCat .Category.Hom[_,_] x y = El x → El y
  UCat .Category.id x = x
  UCat .Category._⋆_ f g x = g (f x)
  UCat .Category.⋆IdL _ = refl
  UCat .Category.⋆IdR _ = refl
  UCat .Category.⋆Assoc _ _ _ = refl
  UCat .Category.isSetHom = isSet→ (ElSet _)

  UCwF : CwF UCat (ℓ-max ℓ ℓ') ℓ'
  UCwF .CwF.emptyContext .fst = Unit
  UCwF .CwF.emptyContext .snd = UnitTerminal

  UCwF .CwF.tyPresheaf .F-ob x .fst = El x → U
  UCwF .CwF.tyPresheaf .F-ob x .snd = isSet→ USet
  UCwF .CwF.tyPresheaf .F-hom f g = g ∘ f
  UCwF .CwF.tyPresheaf .F-id = refl
  UCwF .CwF.tyPresheaf .F-seq _ _ = refl

  UCwF .CwF.tmPresheaf .F-ob (Γ , A) .fst = (x : El Γ) → El (A x)
  UCwF .CwF.tmPresheaf .F-ob (Γ , A) .snd = isSetΠ (λ x → ElSet (A x))
  UCwF .CwF.tmPresheaf .F-hom {Γ , A} {Σ , B} (f , p) x y = subst El (funExt⁻ p y) (x (f y))
  UCwF .CwF.tmPresheaf .F-id i x y = substRefl {B = El} (x y) i
                                  -- funExt (λ x → funExt (λ y → substRefl {B = El} (x y)))
  UCwF .CwF.tmPresheaf .F-seq {Γ , A} {Σ , B} (f , p) (g , q) i x y = substComposite El (funExt⁻ p (g y)) (funExt⁻ q y) (x (f (g y))) i
                                                                  --  funExt (λ x → funExt (λ y → substComposite El (funExt⁻ p (g y)) (funExt⁻ q y) (x (f (g y)))))

-- ASCII art commutative diagrams code comments (and for own intuition)
  UCwF .CwF.ctxExtFunctor .F-ob (Γ , A) = Sig Γ A
  UCwF .CwF.ctxExtFunctor .F-hom {Γ , A} {Δ , B} (f , p) x = invEq (SigIso Δ B) ((f (SigIso Γ A .fst x .fst)) , subst⁻ El (funExt⁻ p (SigIso Γ A .fst x .fst)) (SigIso Γ A .fst x .snd))
                                                          -- invEq (SigIso Δ B) let (a , b) = SigIso Γ A .fst x in (f a) , (subst⁻ El (funExt⁻ p a) b)
  UCwF .CwF.ctxExtFunctor .F-id {Γ , A} = funExt (λ x → cong
                                                      (λ m → invEq (SigIso Γ A) ((SigIso Γ A .fst x .fst) , m))
                                                      (substRefl {B = El} (SigIso Γ A .fst x .snd)) ∙ retEq (SigIso Γ A) x)
  UCwF .CwF.ctxExtFunctor .F-seq {Γ , A} {Δ , B} {E , C} (f , p) (g , q) = funExt (λ x → let
      (a , b) = SigIso Γ A .fst x

      goal1 : invEq (SigIso E C) (g (f (SigIso Γ A .fst x .fst)) , subst⁻ El (funExt⁻ (cong (λ h → h ∘ f) q ∙ p) (SigIso Γ A .fst x .fst)) (SigIso Γ A .fst x .snd))
              ≡
              invEq (SigIso E C) {!g!}
      goal1 = {!!}

      goal : -- UCwF .CwF.ctxExtFunctor .F-hom
             --  (((Cubical.Categories.Instances.Elements.Contravariant.∫ᴾ
             --     UCwF .CwF.tyPresheaf)
             --    Category.⋆ (f , p))
             --   (g , q))
             --  x
              invEq (SigIso E C) (g (f (SigIso Γ A .fst x .fst)) , subst⁻ El (funExt⁻ (cong (λ h → h ∘ f) q ∙ p) (SigIso Γ A .fst x .fst)) (SigIso Γ A .fst x .snd))
              ≡
              invEq (SigIso E C) ((g (SigIso Δ B .fst (UCwF .CwF.ctxExtFunctor .F-hom (f , p) x) .fst)) , (subst⁻ El (funExt⁻ q (SigIso Δ B .fst (UCwF .CwF.ctxExtFunctor .F-hom (f , p) x) .fst)) (SigIso Δ B .fst (UCwF .CwF.ctxExtFunctor .F-hom (f , p) x) .snd)))
              -- UCwF .CwF.ctxExtFunctor .F-hom (g , q) (invEq (SigIso Δ B) ((f (SigIso Γ A .fst x .fst)) , (subst⁻ El (funExt⁻ p (SigIso Γ A .fst x .fst)) (SigIso Γ A .fst x .snd))))
              -- UCwF .CwF.ctxExtFunctor .F-hom (g , q) (UCwF .CwF.ctxExtFunctor .F-hom (f , p) x)
      goal = {!!} -- cong (λ m → invEq (SigIso E C) (g m , {!!})) {!!} ∙ {!!}
    in goal)

  UCwF .CwF.ctxExtEquiv = {!!}

  UCwF .CwF.special-ty-rev-assoc-proof = {!!}

  UCwF .CwF.ctxExtEquivNat = {!!}
