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

  U-Σ .Σ-Structure-CwF.sig-iso {Γ} A B = let
      fun : ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
            → Σ ((x : El Γ) → El (A x)) (λ v → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x))))
      fun F = (λ x → SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .fst) , λ x → SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .snd

      inv : Σ ((x : El Γ) → El (A x)) (λ v → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x))))
            → ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
      inv (a , b) x = invEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (a x , b x)

      sec : (s : Σ ((x : El Γ) → El (A x)) (λ v → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x))))) → fun (inv s) ≡ s
      sec (a , b) = let
          f : (a₁ : El Γ) → Σ (El (A a₁)) (λ x → El (B (invEq (SigIso Γ A) (a₁ , x))))
          f x = SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁))) .fst (invEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

          p : f ≡ (λ x → (a x , b x))
          p = funExt (λ x → secEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

          goal : (fst ∘ f , snd ∘ f) ≡ (a , b)
          goal i = fst ∘ (p i) , snd ∘ (p i)
        in goal

      ret : (F : (x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a))))) → inv (fun F) ≡ F
      ret F = funExt (λ x → retEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (F x))
    in isoToEquiv (iso fun inv sec ret)

  -- U-Σ .Σ-Structure-CwF.sig-iso {Γ} A B = isoToEquiv isom
  --   where
  --     isom : Iso ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
  --                (Σ ((x : El Γ) → El (A x)) (λ a → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , a x)))))
  --     isom .Iso.fun F .fst x = SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .fst
  --     isom .Iso.fun F .snd x = SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .snd
  --     isom .Iso.inv (a , b) x = invEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (a x , b x)
  --     isom .Iso.sec (a , b) = goal
  --       where
  --         f : (a₁ : El Γ) → Σ (El (A a₁)) (λ x → El (B (invEq (SigIso Γ A) (a₁ , x))))
  --         f x = SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁))) .fst (invEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

  --         p : f ≡ (λ x → (a x , b x))
  --         p = funExt (λ x → secEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

  --         goal : (fst ∘ f , snd ∘ f) ≡ (a , b)
  --         goal i .fst = fst ∘ (p i)
  --         goal i .snd = snd ∘ (p i)
  --     isom .Iso.ret F = funExt goal
  --       where
  --         goal : (x : El Γ) →
  --                 invEq
  --                 (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))))
  --                 (SigIso (A x)
  --                  (λ a → B (invEq (SigIso Γ A) (x , a))) .fst
  --                  (F x))
  --                 ≡ F x
  --         goal x = retEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (F x)

  U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq {Γ} {Δ} A B a σ = funExt (λ x → let
      r : U
      r = B (invEq (SigIso Δ A) (σ x , a (σ x)))

      s : U
      s = B (invEq (SigIso Δ A) (σ x , subst⁻ El refl (a (σ x))))

      s' : U
      s' = B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) ((x , a (σ x)))))

      s≡s' : s ≡ s'
      s≡s' = refl

      t : U
      t = B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , a (σ x))))))

      u : U
      u = B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , subst⁻ El refl (a (σ x)))))))

      s≡r : s ≡ r
      s≡r = cong (λ m → B (invEq (SigIso Δ A) (σ x , m))) (substRefl {B = El} (a (σ x)))

      t≡s : t ≡ s
      t≡s = cong (λ m → B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) m))) (secEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , a (σ x)))

      u≡t : u ≡ t
      u≡t = cong (λ m → B (invEq (SigIso Δ A) (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , m)))))) (substRefl {B = El} (a (σ x)))

      goal : r ≡ u
      goal = sym (u≡t ∙∙ t≡s ∙∙ s≡r)
    in goal)

  U-Σ .Σ-Structure-CwF.sig-iso-nat {Γ} {Δ} A B a σ = goal
    where
      -- goal : ((λ x →
      --             SigIso ((UCwF CwF.∘Ty A) σ x)
      --             (λ a₁ →
      --                (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , σ ⟩ A)
      --                (invEq (SigIso Γ ((UCwF CwF.∘Ty A) σ)) (x , a₁)))
      --             .fst
      --             (subst (CwF.Tm UCwF Γ)
      --              (funExt
      --               (λ x₁ i →
      --                  Sig (A (σ x₁))
      --                  (funExt
      --                   (λ y i₁ →
      --                      B
      --                      (invEq (SigIso Δ A)
      --                       (((λ i₂ →
      --                            ctxExtFunctorHomDestructured Γ Δ (λ x₂ → A (σ x₂)) A
      --                            (σ , (λ _ x₂ → A (σ x₂)))
      --                            (secEq (SigIso Γ (λ x₂ → A (σ x₂))) (x₁ , y) i₂))
      --                         ∙ (λ i₂ → σ x₁ , substRefl y i₂))
      --                        (~ i₁))))
      --                   i)))
      --              ((UCwF CwF.[ a ]) σ) x)
      --             .fst)
      --          ,
      --          (λ x →
      --             SigIso ((UCwF CwF.∘Ty A) σ x)
      --             (λ a₁ →
      --                (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , σ ⟩ A)
      --                (invEq (SigIso Γ ((UCwF CwF.∘Ty A) σ)) (x , a₁)))
      --             .fst
      --             (subst (CwF.Tm UCwF Γ)
      --              (funExt
      --               (λ x₁ i →
      --                  Sig (A (σ x₁))
      --                  (funExt
      --                   (λ y i₁ →
      --                      B
      --                      (invEq (SigIso Δ A)
      --                       (((λ i₂ →
      --                            ctxExtFunctorHomDestructured Γ Δ (λ x₂ → A (σ x₂)) A
      --                            (σ , (λ _ x₂ → A (σ x₂)))
      --                            (secEq (SigIso Γ (λ x₂ → A (σ x₂))) (x₁ , y) i₂))
      --                         ∙ (λ i₂ → σ x₁ , substRefl y i₂))
      --                        (~ i₁))))
      --                   i)))
      --              ((UCwF CwF.[ a ]) σ) x)
      --             .snd))
      --         ≡
      --         ((UCwF CwF.[
      --           (λ x →
      --              SigIso (A x) (λ a₁ → B (invEq (SigIso Δ A) (x , a₁))) .fst (a x)
      --              .fst)
      --           ])
      --          σ
      --          ,
      --          subst (CwF.Tm UCwF Γ)
      --          (funExt
      --           (λ x i →
      --              ((λ i₁ →
      --                  B
      --                  (invEq (SigIso Δ A)
      --                   (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A
      --                    (σ , (λ _ x₁ → A (σ x₁)))
      --                    (SigIso Γ (λ x₁ → A (σ x₁)) .fst
      --                     (invEq (SigIso Γ (λ x₁ → A (σ x₁)))
      --                      (x ,
      --                       substRefl
      --                       (SigIso (A (σ x)) (λ a₁ → B (invEq (SigIso Δ A) (σ x , a₁))) .fst
      --                        (a (σ x)) .fst)
      --                       i₁))))))
      --               ∙∙
      --               (λ i₁ →
      --                  B
      --                  (invEq (SigIso Δ A)
      --                   (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A
      --                    (σ , (λ _ x₁ → A (σ x₁)))
      --                    (secEq (SigIso Γ (λ x₁ → A (σ x₁)))
      --                     (x ,
      --                      SigIso (A (σ x)) (λ a₁ → B (invEq (SigIso Δ A) (σ x , a₁))) .fst
      --                      (a (σ x)) .fst)
      --                     i₁))))
      --               ∙∙
      --               (λ i₁ →
      --                  B
      --                  (invEq (SigIso Δ A)
      --                   (σ x ,
      --                    substRefl
      --                    (SigIso (A (σ x)) (λ a₁ → B (invEq (SigIso Δ A) (σ x , a₁))) .fst
      --                     (a (σ x)) .fst)
      --                    i₁))))
      --              (~ i)))
      --          ((UCwF CwF.[
      --            (λ x →
      --               SigIso (A x) (λ a₁ → B (invEq (SigIso Δ A) (x , a₁))) .fst (a x)
      --               .snd)
      --            ])
      --           σ))

      -- goal : ((λ x →
      --             SigIso (A (σ x))
      --             (λ a₁ →
      --                B
      --                (snd (SigIso Δ A) .equiv-proof
      --                 (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A
      --                  (σ , (λ _ x₁ → A (σ x₁)))
      --                  (SigIso Γ (λ x₁ → A (σ x₁)) .fst
      --                   (snd (SigIso Γ (λ x₁ → A (σ x₁))) .equiv-proof (x , a₁) .fst
      --                    .fst)))
      --                 .fst .fst))
      --             .fst
      --             (transp
      --              (λ i →
      --                 El
      --                 (Sig (A (σ (transp (λ j → El Γ) i x)))
      --                  (λ x₁ →
      --                     B
      --                     (snd (SigIso Δ A) .equiv-proof
      --                      (hcomp
      --                       (doubleComp-faces
      --                        (λ _ →
      --                           ctxExtFunctorHomDestructured Γ Δ (λ x₂ → A (σ x₂)) A
      --                           (σ , (λ _ x₂ → A (σ x₂)))
      --                           (SigIso Γ (λ x₂ → A (σ x₂)) .fst
      --                            (snd (SigIso Γ (λ x₂ → A (σ x₂))) .equiv-proof
      --                             (transp (λ j → El Γ) i x , x₁) .fst .fst)))
      --                        (λ i₁ →
      --                           σ (transp (λ j → El Γ) i x) ,
      --                           transp (λ _ → El (A (σ (transp (λ j → El Γ) i x)))) i₁ x₁)
      --                        (~ i))
      --                       (ctxExtFunctorHomDestructured Γ Δ (λ x₂ → A (σ x₂)) A
      --                        (σ , (λ _ x₂ → A (σ x₂)))
      --                        (snd (SigIso Γ (λ x₂ → A (σ x₂))) .equiv-proof
      --                         (transp (λ j → El Γ) i x , x₁) .fst .snd (~ i))))
      --                      .fst .fst))))
      --              i0
      --              (transp
      --               (λ i →
      --                  El
      --                  (Sig (A (σ (transp (λ j → El Γ) i0 x)))
      --                   (λ a₁ →
      --                      B
      --                      (snd (SigIso Δ A) .equiv-proof (σ (transp (λ j → El Γ) i0 x) , a₁)
      --                       .fst .fst))))
      --               i0 (a (σ (transp (λ j → El Γ) i0 x)))))
      --             .fst)
      --          ,
      --          (λ x →
      --             SigIso (A (σ x))
      --             (λ a₁ →
      --                B
      --                (snd (SigIso Δ A) .equiv-proof
      --                 (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A
      --                  (σ , (λ _ x₁ → A (σ x₁)))
      --                  (SigIso Γ (λ x₁ → A (σ x₁)) .fst
      --                   (snd (SigIso Γ (λ x₁ → A (σ x₁))) .equiv-proof (x , a₁) .fst
      --                    .fst)))
      --                 .fst .fst))
      --             .fst
      --             (transp
      --              (λ i →
      --                 El
      --                 (Sig (A (σ (transp (λ j → El Γ) i x)))
      --                  (λ x₁ →
      --                     B
      --                     (snd (SigIso Δ A) .equiv-proof
      --                      (hcomp
      --                       (doubleComp-faces
      --                        (λ _ →
      --                           ctxExtFunctorHomDestructured Γ Δ (λ x₂ → A (σ x₂)) A
      --                           (σ , (λ _ x₂ → A (σ x₂)))
      --                           (SigIso Γ (λ x₂ → A (σ x₂)) .fst
      --                            (snd (SigIso Γ (λ x₂ → A (σ x₂))) .equiv-proof
      --                             (transp (λ j → El Γ) i x , x₁) .fst .fst)))
      --                        (λ i₁ →
      --                           σ (transp (λ j → El Γ) i x) ,
      --                           transp (λ _ → El (A (σ (transp (λ j → El Γ) i x)))) i₁ x₁)
      --                        (~ i))
      --                       (ctxExtFunctorHomDestructured Γ Δ (λ x₂ → A (σ x₂)) A
      --                        (σ , (λ _ x₂ → A (σ x₂)))
      --                        (snd (SigIso Γ (λ x₂ → A (σ x₂))) .equiv-proof
      --                         (transp (λ j → El Γ) i x , x₁) .fst .snd (~ i))))
      --                      .fst .fst))))
      --              i0
      --              (transp
      --               (λ i →
      --                  El
      --                  (Sig (A (σ (transp (λ j → El Γ) i0 x)))
      --                   (λ a₁ →
      --                      B
      --                      (snd (SigIso Δ A) .equiv-proof (σ (transp (λ j → El Γ) i0 x) , a₁)
      --                       .fst .fst))))
      --               i0 (a (σ (transp (λ j → El Γ) i0 x)))))
      --             .snd))
      --         ≡
      --         ((λ y →
      --             transp (λ i → El (A (σ y))) i0
      --             (SigIso (A (σ y))
      --              (λ a₁ → B (snd (SigIso Δ A) .equiv-proof (σ y , a₁) .fst .fst))
      --              .fst (a (σ y)) .fst))
      --          ,
      --          transp
      --          (λ i →
      --             (x : El Γ) →
      --             El
      --             (hcomp
      --              (doubleComp-faces
      --               (λ i₁ →
      --                  B
      --                  (snd (SigIso Δ A) .equiv-proof
      --                   (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A
      --                    (σ , (λ _ x₁ → A (σ x₁)))
      --                    (SigIso Γ (λ x₁ → A (σ x₁)) .fst
      --                     (snd (SigIso Γ (λ x₁ → A (σ x₁))) .equiv-proof
      --                      (x ,
      --                       transp (λ _ → El (A (σ x))) i₁
      --                       (SigIso (A (σ x))
      --                        (λ a₁ → B (snd (SigIso Δ A) .equiv-proof (σ x , a₁) .fst .fst))
      --                        .fst (a (σ x)) .fst))
      --                      .fst .fst)))
      --                   .fst .fst))
      --               (λ i₁ →
      --                  B
      --                  (snd (SigIso Δ A) .equiv-proof
      --                   (σ x ,
      --                    transp (λ _ → El (A (σ x))) i₁
      --                    (SigIso (A (σ x))
      --                     (λ a₁ → B (snd (SigIso Δ A) .equiv-proof (σ x , a₁) .fst .fst))
      --                     .fst (a (σ x)) .fst))
      --                   .fst .fst))
      --               (~ i))
      --              (B
      --               (snd (SigIso Δ A) .equiv-proof
      --                (ctxExtFunctorHomDestructured Γ Δ (λ x₁ → A (σ x₁)) A
      --                 (σ , (λ _ x₁ → A (σ x₁)))
      --                 (snd (SigIso Γ (λ x₁ → A (σ x₁))) .equiv-proof
      --                  (x ,
      --                   SigIso (A (σ x))
      --                   (λ a₁ → B (snd (SigIso Δ A) .equiv-proof (σ x , a₁) .fst .fst))
      --                   .fst (a (σ x)) .fst)
      --                  .fst .snd (~ i)))
      --                .fst .fst))))
      --          i0
      --          (λ y →
      --             transp
      --             (λ i →
      --                El
      --                (B
      --                 (snd (SigIso Δ A) .equiv-proof
      --                  (σ y ,
      --                   SigIso (A (σ y))
      --                   (λ a₁ → B (snd (SigIso Δ A) .equiv-proof (σ y , a₁) .fst .fst))
      --                   .fst (a (σ y)) .fst)
      --                  .fst .fst)))
      --             i0
      --             (SigIso (A (σ y))
      --              (λ a₁ → B (snd (SigIso Δ A) .equiv-proof (σ y , a₁) .fst .fst))
      --              .fst (a (σ y)) .snd)))

      LEFT : Σ-syntax (CwF.Tm UCwF Γ ((UCwF CwF.∘Ty A) σ))
              (λ a₁ →
                 CwF.Tm UCwF Γ
                 ((UCwF CwF.∘Ty (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , σ ⟩ A))
                  (CwF.ctxExtSubst UCwF ((UCwF CwF.∘Ty A) σ) (CwF.IdSubst UCwF)
                   (U-Σ .Σ-Structure-CwF.idsubst-action ((UCwF CwF.∘Ty A) σ) a₁))))
      LEFT = (U-Σ .Σ-Structure-CwF.sig-iso ((UCwF CwF.∘Ty A) σ)
                ((UCwF CwF.∘Ty B) (CwF.⟨ UCwF , σ ⟩ A)) .fst
                (subst (CwF.Tm UCwF Γ) (U-Σ .Σ-Structure-CwF.sig-nat A B σ)
                 ((UCwF CwF.[ a ]) σ)))
                 
      goal : Path {!!}
              LEFT
              (((UCwF CwF.[ U-Σ .Σ-Structure-CwF.sig-iso A B .fst a .fst ]) σ ,
                 subst (CwF.Tm UCwF Γ)
                 (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B
                  (U-Σ .Σ-Structure-CwF.sig-iso A B .fst a .fst) σ)
                 ((UCwF CwF.[ U-Σ .Σ-Structure-CwF.sig-iso A B .fst a .snd ]) σ)))
      goal = {!!}
      -- ΣPathP ((funExt (λ x → {!!} ∙ sym (transportRefl _))) , {!!})
