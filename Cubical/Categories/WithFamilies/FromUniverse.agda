module Cubical.Categories.WithFamilies.FromUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Instances.Sets

import Cubical.Categories.Instances.Elements as Els
open Els.Contravariant

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
  UCwF .CwF.ctxExtFunctor .F-hom {Γ , A} {Δ , B} (f , p) (a , b) .snd = subst⁻ El (funExt⁻ p a) b
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

  UCwF .CwF.ctxExtEquiv Γ Δ A = isoToEquiv Σ-Π-Iso
    -- where
    --   isom : Iso (Γ .fst → Σ (Δ .fst) (λ x → El (A x))) (Σ (Γ .fst → Δ .fst) (λ σ → (x : Γ .fst) → El (A (σ x))))
    --   isom .Iso.fun F .fst x = F x .fst
    --   isom .Iso.fun F .snd x = F x .snd
    --   isom .Iso.inv (f₁ , f₂) x .fst = f₁ x
    --   isom .Iso.inv (f₁ , f₂) x .snd = f₂ x
    --   isom .Iso.sec _ = refl
    --   isom .Iso.ret _ = refl

  UCwF .CwF.special-ty-rev-assoc-proof _ _ _ _ _ _ x = x
  UCwF .CwF.ctxExtEquivNat _ _ _ _ σ τ = ΣPathP (refl , (funExt (λ x → sym (substRefl {B = El} (snd (τ (σ x)))))))

module Internal (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ')
         (ElSet : (a : U) → isSet (El a))
         (Unit : U)
         (UnitTerminal : isContr (El Unit))
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

  ctxExtFunctorHomDestructured : (Γ Δ : U) (A : El Γ → U) (B : El Δ → U) → (Σ[ f ∈ (El Γ → El Δ) ] (λ a → B (f a)) ≡ A) → (Σ[ x ∈ El Γ ] El (A x)) → (Σ[ x ∈ El Δ ] El (B x))
  ctxExtFunctorHomDestructured Γ Δ A B (f , p) (x , a) .fst = f x
  ctxExtFunctorHomDestructured Γ Δ A B (f , p) (x , a) .snd = subst⁻ El (funExt⁻ p x) a

  UCwF : CwF UCat (ℓ-max ℓ ℓ') ℓ'
  UCwF .CwF.emptyContext .fst = Unit
  UCwF .CwF.emptyContext .snd Γ .fst _ = UnitTerminal .fst
  UCwF .CwF.emptyContext .snd Γ .snd σ = funExt (λ x → UnitTerminal .snd (σ x))

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
  --                         f , p                       g , q
  --           Γ , A  ------------------>  Δ , B  -------------------->  Ε , C
  --
  --       El (Sig Γ A)  ----------->  El (Sig Δ B)  -------------->  El (Sig Ε C)
  --
  --             |                           |                             |
  --           ≃ |                         ≃ |                           ≃ |
  --             |                           |                             |
  --             V                           V                             V
  --
  -- Σ[ x ∈ El Γ ] El (A x)  --->  Σ[ x ∈ El Δ ] El (B x)  --->  Σ[ x ∈ El Ε ] El (C x)

  UCwF .CwF.ctxExtFunctor .F-ob (Γ , A) = Sig Γ A
  UCwF .CwF.ctxExtFunctor .F-hom {Γ , A} {Δ , B} (f , p) x = invEq (SigIso Δ B) (ctxExtFunctorHomDestructured Γ Δ A B (f , p) (SigIso Γ A .fst x))
  UCwF .CwF.ctxExtFunctor .F-id {Γ , A} = funExt (λ x → cong (invEq (SigIso Γ A)) (ΣPathP (refl , (substRefl {B = El} (SigIso Γ A .fst x .snd)))) ∙ retEq (SigIso Γ A) x)
  UCwF .CwF.ctxExtFunctor .F-seq {Γ , A} {Δ , B} {Ε , C} (f , p) (g , q) = funExt (λ x → (let
      r : (Σ[ x ∈ El Γ ] El (A x)) → (Σ[ x ∈ El Ε ] El (C x))
      r y = g (f (y .fst)) , subst⁻ El (funExt⁻ q (f (y .fst)) ∙ funExt⁻ p (y .fst)) (y .snd)
      
      s : (Σ[ x ∈ El Γ ] El (A x)) → (Σ[ x ∈ El Ε ] El (C x))
      s = ctxExtFunctorHomDestructured Δ Ε B C (g , q) ∘ (SigIso Δ B .fst ∘ invEq (SigIso Δ B)) ∘ ctxExtFunctorHomDestructured Γ Δ A B (f , p)
      
      t : (Σ[ x ∈ El Γ ] El (A x)) → (Σ[ x ∈ El Ε ] El (C x))
      t y = g (f (y .fst)) , subst⁻ El (funExt⁻ q (f (y .fst))) (subst⁻ El (funExt⁻ p (y .fst)) (y .snd))

      t' : (Σ[ x ∈ El Γ ] El (A x)) → (Σ[ x ∈ El Ε ] El (C x))
      t' y = g (f (y .fst)) , subst⁻ El (sym (sym (funExt⁻ p (y .fst)) ∙ sym (funExt⁻ q (f (y .fst))))) (y .snd)

      s≡t : s ≡ t
      s≡t = cong (λ m → ctxExtFunctorHomDestructured Δ Ε B C (g , q) ∘ m ∘ ctxExtFunctorHomDestructured Γ Δ A B (f , p)) (funExt (secEq (SigIso Δ B)))

      r≡t' : r ≡ t'
      r≡t' = funExt (λ y → cong (λ m → g (f (y .fst)) , subst⁻ El m (y .snd)) (sym (symDistr (sym (funExt⁻ p (y .fst))) (sym (funExt⁻ q (f (y .fst)))))))

      t'≡t : t' ≡ t
      t'≡t = funExt (λ y → cong (λ m → g (f (y .fst)) , m) (substComposite El (sym (funExt⁻ p (y .fst))) (sym (funExt⁻ q (f (y .fst)))) (y .snd)))

      r≡s : r ≡ s
      r≡s = r≡t' ∙∙ t'≡t ∙∙ sym s≡t
    in cong (λ m → invEq (SigIso Ε C) (m (SigIso Γ A .fst x))) r≡s))

  UCwF .CwF.ctxExtEquiv Γ Δ B = goal
    where
      goal' : (El Γ → Σ[ x ∈ El Δ ] El (B x)) ≃ (Σ[ σ ∈ (El Γ → El Δ) ] ((x : El Γ) → El (B (σ x))))
      goal' = isoToEquiv Σ-Π-Iso

      helper : (El Γ → El (Sig Δ B)) ≃ (El Γ → Σ[ x ∈ El Δ ] El (B x))
      helper = isoToEquiv isom
        where
          isom : Iso (El Γ → El (Sig Δ B)) (El Γ → Σ[ x ∈ El Δ ] El (B x))
          isom .Iso.fun f = SigIso Δ B .fst ∘ f
          isom .Iso.inv f = invEq (SigIso Δ B) ∘ f
          isom .Iso.sec f = cong (λ m → m ∘ f) (funExt (secEq (SigIso Δ B)))
          isom .Iso.ret f = cong (λ m → m ∘ f) (funExt (retEq (SigIso Δ B)))
      
      goal : (El Γ → El (Sig Δ B)) ≃ (Σ[ σ ∈ (El Γ → El Δ) ] ((x : El Γ) → El (B (σ x))))
      goal = compEquiv helper goal'

  UCwF .CwF.special-ty-rev-assoc-proof _ _ _ _ _ _ a = a

  UCwF .CwF.ctxExtEquivNat _ _ Δ A σ τ = ΣPathP (refl , funExt (λ x → sym (substRefl {B = El} (SigIso Δ A .fst (τ (σ x)) .snd))))
