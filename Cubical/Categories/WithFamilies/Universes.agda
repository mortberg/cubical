module Cubical.Categories.WithFamilies.Universes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.WithFamilies.Base

private
  variable ℓ ℓ' ℓ'' ℓ''' : Level

open Functor

module _ (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ')
         (ElSet : (a : U) → isSet (El a))
         (Unit : U)
         (UnitTerminal : (a : U) → isContr (El a → El Unit))
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
  UCwF .CwF.tyPresheaf .F-hom f g x = g (f x)
  UCwF .CwF.tyPresheaf .F-id = refl
  UCwF .CwF.tyPresheaf .F-seq _ _ = refl

  UCwF .CwF.tmPresheaf .F-ob (Γ , A) .fst = (x : El Γ) → El (A x)
  UCwF .CwF.tmPresheaf .F-ob (Γ , A) .snd = isSetΠ (λ x → ElSet (A x))
  UCwF .CwF.tmPresheaf .F-hom {Γ , A} {Σ , B} (f , p) x y = subst El (funExt⁻ p y) (x (f y))
  UCwF .CwF.tmPresheaf .F-id i x y = substRefl {B = El} (x y) i
                                  -- funExt (λ x → funExt (λ y → substRefl {B = El} (x y)))
  UCwF .CwF.tmPresheaf .F-seq {Γ , A} {Σ , B} (f , p) (g , q) i x y = substComposite El (funExt⁻ p (g y)) (funExt⁻ q y) (x (f (g y))) i
                                                                  --  funExt (λ x → funExt (λ y → substComposite El (funExt⁻ p (g y)) (funExt⁻ q y) (x (f (g y)))))

  UCwF .CwF.ctxExtFunctor .F-ob (Γ , A) = Sig Γ A
  UCwF .CwF.ctxExtFunctor .F-hom {Γ , A} {Σ , B} (f , p) x = invEq (SigIso Σ B) ((f (SigIso Γ A .fst x .fst)) , subst⁻ El (funExt⁻ p (SigIso Γ A .fst x .fst)) (SigIso Γ A .fst x .snd))
                                                          -- invEq (SigIso Σ B) let (a , b) = SigIso Γ A .fst x in (f a) , (subst⁻ El (funExt⁻ p a) b)
  UCwF .CwF.ctxExtFunctor .F-id {Γ , A} = funExt (λ x → cong
                                                      (λ m → invEq (SigIso Γ A) ((SigIso Γ A .fst x .fst) , m))
                                                      (substRefl {B = El} (SigIso Γ A .fst x .snd)) ∙ retEq (SigIso Γ A) x)
  UCwF .CwF.ctxExtFunctor .F-seq {Γ , A} {Δ , B} {E , C} (f , p) (g , q) = funExt (λ x → {!cong (invEq (SigIso E C)) ?!})

  UCwF .CwF.ctxExtEquiv = {!!}

  UCwF .CwF.special-ty-rev-assoc-proof = {!!}

  UCwF .CwF.ctxExtEquivNat = {!!}
