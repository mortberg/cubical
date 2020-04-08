-- Check that we can define some (weak) equivariant coe operations
-- using connections. Inspired by a formalization by Evan Cavallo.
{-# OPTIONS --cubical #-}
module Cubical.Experiments.Equivariant where

open import Cubical.Foundations.Prelude

-- Binary equivariant coe
module Binary where

  coe₂ : ∀ {ℓ} (A : I → I → Type ℓ) (r₀ r₁ : I) (a : A r₀ r₁) (s₀ s₁ : I) → A s₀ s₁
  coe₂ A r₀ r₁ a s₀ s₁ =
    transport (λ i → A (s₀ ∧ i) (s₁ ∧ i))
      (transport (λ i → A (r₀ ∧ ~ i) (r₁ ∧ ~ i)) a)

  -- This doesn't hold strictly, but with diagonal cofibrations we
  -- could easily fix it
  coe₂Cap : ∀ {ℓ} (A : I → I → Type ℓ) (r₀ r₁ : I) (a : A r₀ r₁)
         → coe₂ A r₀ r₁ a r₀ r₁ ≡ a
  coe₂Cap A r₀ r₁ a j =
    transp (λ i → A (r₀ ∧ (i ∨ j)) (r₁ ∧ i ∨ j)) j
      (transp (λ i → A (r₀ ∧ (~ i ∨ j)) (r₁ ∧ (~ i ∨ j))) j a)

  -- this needs to hold by reflexivity
  equivariance : ∀ {ℓ} (A : I → I → Type ℓ) (r₀ r₁ : I) (a : A r₀ r₁) (s₀ s₁ : I)
               → coe₂ A r₀ r₁ a s₀ s₁ ≡ coe₂ (λ i₀ i₁ → A i₁ i₀) r₁ r₀ a s₁ s₀
  equivariance A r₀ r₁ a s₀ s₁ = refl

  capEquivariance : ∀ {ℓ} (A : I → I → Type ℓ) (r₀ r₁ : I) (a : A r₀ r₁)
                  → coe₂Cap A r₀ r₁ a ≡ coe₂Cap (λ x₀ x₁ → A x₁ x₀) r₁ r₀ a
  capEquivariance A r₀ r₁ a = refl


-- Ternary equivariant coe
module Ternary where

  coe₃ : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂) (s₀ s₁ s₂ : I) → A s₀ s₁ s₂
  coe₃ A r₀ r₁ r₂ a s₀ s₁ s₂ =
    transport (λ i → A (s₀ ∧ i) (s₁ ∧ i) (s₂ ∧ i))
      (transport (λ i → A (r₀ ∧ ~ i) (r₁ ∧ ~ i) (r₂ ∧ ~ i)) a)

  coe₃Cap : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂)
         → coe₃ A r₀ r₁ r₂ a r₀ r₁ r₂ ≡ a
  coe₃Cap A r₀ r₁ r₂ a j =
    transp (λ i → A (r₀ ∧ (i ∨ j)) (r₁ ∧ (i ∨ j)) (r₂ ∧ (i ∨ j))) j
      (transp (λ i → A (r₀ ∧ (~ i ∨ j)) (r₁ ∧ (~ i ∨ j)) (r₂ ∧ (~ i ∨ j))) j a)

  -- We now have to check five equivariance equations:

  -- (021)
  equivariance₁ : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂) (s₀ s₁ s₂ : I)
                → coe₃ A r₀ r₁ r₂ a s₀ s₁ s₂ ≡ coe₃ (λ i₀ i₁ i₂ → A i₀ i₂ i₁) r₀ r₂ r₁ a s₀ s₂ s₁
  equivariance₁ A r₀ r₁ r₂ a s₀ s₁ s₂ = refl

  -- (102)
  equivariance₂ : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂) (s₀ s₁ s₂ : I)
                → coe₃ A r₀ r₁ r₂ a s₀ s₁ s₂ ≡ coe₃ (λ i₀ i₁ i₂ → A i₁ i₀ i₂) r₁ r₀ r₂ a s₁ s₀ s₂
  equivariance₂ A r₀ r₁ r₂ a s₀ s₁ s₂ = refl

  -- (210)
  equivariance₃ : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂) (s₀ s₁ s₂ : I)
                → coe₃ A r₀ r₁ r₂ a s₀ s₁ s₂ ≡ coe₃ (λ i₀ i₁ i₂ → A i₂ i₁ i₀) r₂ r₁ r₀ a s₂ s₁ s₀
  equivariance₃ A r₀ r₁ r₂ a s₀ s₁ s₂ = refl

  -- (120)
  equivariance₄ : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂) (s₀ s₁ s₂ : I)
                → coe₃ A r₀ r₁ r₂ a s₀ s₁ s₂ ≡ coe₃ (λ i₀ i₁ i₂ → A i₁ i₂ i₀) r₂ r₀ r₁ a s₂ s₀ s₁
  equivariance₄ A r₀ r₁ r₂ a s₀ s₁ s₂ = refl

  -- (201)
  equivariance₅ : ∀ {ℓ} (A : I → I → I → Type ℓ) (r₀ r₁ r₂ : I) (a : A r₀ r₁ r₂) (s₀ s₁ s₂ : I)
                → coe₃ A r₀ r₁ r₂ a s₀ s₁ s₂ ≡ coe₃ (λ i₀ i₁ i₂ → A i₂ i₀ i₁) r₁ r₂ r₀ a s₁ s₂ s₀
  equivariance₅ A r₀ r₁ r₂ a s₀ s₁ s₂ = refl
