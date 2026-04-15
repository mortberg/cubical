module Cubical.Categories.WithFamilies.Structure.Sigma.FromUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.WithFamilies.Base
import Cubical.Categories.WithFamilies.FromUniverse as FU
open import Cubical.Categories.WithFamilies.Structure.Sigma.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module Internal (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ')
         (ElSet : (Γ : U) → isSet (El Γ))
         (Unit : U)
         (UnitTerminal : isContr (El Unit))
         (Sig : (Γ : U) → (El Γ → U) → U)
         (SigIso : (Γ : U) (A : El Γ → U) → El (Sig Γ A) ≃ (Σ[ x ∈ El Γ ] El (A x)))
         where
  open FU.Internal U USet El ElSet Unit UnitTerminal Sig SigIso

  U-Σ : Σ-Structure-CwF UCwF
  U-Σ .Σ-Structure-CwF.idsubst-action _ x = x
  U-Σ .Σ-Structure-CwF.sig Γ A B x = Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))

  U-Σ .Σ-Structure-CwF.sig-nat {Γ} {Δ} A B σ = funExt (λ x → cong (Sig (A (σ x))) (funExt (λ y → cong (λ m → B (invEq (SigIso Γ A) m)) (let
      r : Σ[ v ∈ El Γ ] El (A v)
      r = (σ x , y)
      
      s : Σ[ v ∈ El Γ ] El (A v)
      s = σ x , subst⁻ El refl y

      t : Σ[ v ∈ El Γ ] El (A v)
      t = ctxExtFunctorHomDestructured Δ Γ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y)))

      s≡r : s ≡ r
      s≡r = cong (λ m → σ x , m) (substRefl {B = El} y)
      
      t≡s : t ≡ s
      t≡s = cong (ctxExtFunctorHomDestructured Δ Γ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁)))) (secEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y))
      
      goal : r ≡ t
      goal = sym (t≡s ∙ s≡r)
    in goal))))

  U-Σ .Σ-Structure-CwF.sig-iso {Γ} A B = isoToEquiv isom
    where
      isom : Iso ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
                 (Σ ((x : El Γ) → El (A x)) (λ a → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , a x)))))
      isom .Iso.fun F .fst x = SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .fst
      isom .Iso.fun F .snd x = SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .snd
      isom .Iso.inv (a , b) x = invEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (a x , b x)
      isom .Iso.sec (a , b) = goal
        where
          f : (a₁ : El Γ) → Σ (El (A a₁)) (λ x → El (B (invEq (SigIso Γ A) (a₁ , x))))
          f x = SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁))) .fst (invEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

          p : f ≡ (λ x → (a x , b x))
          p = funExt (λ x → secEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

          goal : (fst ∘ f , snd ∘ f) ≡ (a , b)
          goal i .fst = fst ∘ (p i)
          goal i .snd = snd ∘ (p i)
      isom .Iso.ret F = funExt goal
        where
          goal : (x : El Γ) →
                  invEq
                  (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))))
                  (SigIso (A x)
                   (λ a → B (invEq (SigIso Γ A) (x , a))) .fst
                   (F x))
                  ≡ F x
          goal x = retEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (F x)

  U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq {Γ} {Δ} A B a σ = funExt goal
    where
      r : El Γ → U
      r x = B (invEq (SigIso Δ A) (σ x , a (σ x)))

      s : El Γ → U
      s x = B (invEq (SigIso Δ A) (σ x , subst⁻ El refl (a (σ x))))

      s' : El Γ → U
      s' x = B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) ((x , a (σ x)))))

      s≡s' : s ≡ s'
      s≡s' = refl

      t : El Γ → U
      t x = B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , a (σ x))))))

      u : El Γ → U
      u x = B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , subst⁻ El refl (a (σ x)))))))

      s≡r : (x : El Γ) → s x ≡ r x
      s≡r x = cong (λ m → B (invEq (SigIso Δ A) (σ x , m))) (substRefl {B = El} (a (σ x)))

      t≡s : (x : El Γ) → t x ≡ s x
      t≡s x = cong (λ m → B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) m))) (secEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , a (σ x)))

      u≡t : (x : El Γ) → u x ≡ t x
      u≡t x = cong (λ m → B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , m)))))) (substRefl {B = El} (a (σ x)))
      
      goal : (x : El Γ) → r x ≡ u x
      goal x = sym (u≡t x ∙∙ t≡s x ∙∙ s≡r x)
      
  U-Σ .Σ-Structure-CwF.sig-iso-nat {Γ} {Δ} A B a σ = goal
    where
      goal : U-Σ .Σ-Structure-CwF.sig-iso ((UCwF CwF.∘Ty A) σ)
              ((UCwF CwF.∘Ty B) (CwF.⟨ UCwF , σ ⟩ A)) .fst
              (subst (CwF.Tm UCwF Γ) (U-Σ .Σ-Structure-CwF.sig-nat A B σ)
               ((UCwF CwF.[ a ]) σ))
              ≡
              ((UCwF CwF.[ U-Σ .Σ-Structure-CwF.sig-iso A B .fst a .fst ]) σ ,
               subst (CwF.Tm UCwF Γ)
               (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B
                (U-Σ .Σ-Structure-CwF.sig-iso A B .fst a .fst) σ)
               ((UCwF CwF.[ U-Σ .Σ-Structure-CwF.sig-iso A B .fst a .snd ]) σ))
      goal = {!!}

