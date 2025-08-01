{-

Based on Nicolai Kraus' blog post:
  The Truncation Map |_| : ℕ -> ‖ℕ‖ is nearly Invertible
  https://homotopytypetheory.org/2013/10/28/the-truncation-map-_-ℕ-‖ℕ‖-is-nearly-invertible/

Defines [recover], which definitionally satisfies `recover ∣ x ∣ ≡ x` ([recover∣∣]) for homogeneous types

Also see the follow-up post by Jason Gross:
  Composition is not what you think it is! Why “nearly invertible” isn’t.
  https://homotopytypetheory.org/2014/02/24/composition-is-not-what-you-think-it-is-why-nearly-invertible-isnt/

-}

module Cubical.HITs.PropositionalTruncation.MagicTrick where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

module Recover {ℓ} (A∙ : Pointed ℓ) (h : isHomogeneous A∙) where
  private
    A = typ A∙
    a = pt A∙

  toEquivPtd : ∥ A ∥₁ → Σ[ B∙ ∈ Pointed ℓ ] (A , a) ≡ B∙
  toEquivPtd = rec isPropSingl (λ x → (A , x) , h x)
  private
    B∙ : ∥ A ∥₁ → Pointed ℓ
    B∙ tx = fst (toEquivPtd tx)

  -- the key observation is that B∙ ∣ x ∣₁ is definitionally equal to (A , x)
  private
    obvs : ∀ x → B∙ ∣ x ∣₁ ≡ (A , x)
    obvs x = refl -- try it: `C-c C-n B∙ ∣ x ∣₁` gives `(A , x)`

  -- thus any truncated element (of a homogeneous type) can be recovered by agda's normalizer!

  recover : ∀ (tx : ∥ A ∥₁) → typ (B∙ tx)
  recover tx = pt (B∙ tx)

  recover∣∣ : ∀ (x : A) → recover ∣ x ∣₁ ≡ x
  recover∣∣ x = refl -- try it: `C-c C-n recover ∣ x ∣₁` gives `x`

  private
    -- notice that the following typechecks because typ (B∙ ∣ x ∣₁) is definitionally equal to to A, but
    --  `recover : ∥ A ∥₁ → A` does not because typ (B∙ tx) is not definitionally equal to A (though it is
    --  judegmentally equal to A by cong typ (snd (toEquivPtd tx)) : A ≡ typ (B∙ tx))
    obvs2 : A → A
    obvs2 = recover ∘ ∣_∣₁

    -- one might wonder if (cong recover (squash₁ ∣ x ∣₁ ∣ y ∣₁)) therefore has type x ≡ y, but thankfully
    --  typ (B∙ (squash₁ ∣ x ∣₁ ∣ y ∣₁ i)) is *not* A (it's a messy hcomp involving h x and h y)
    recover-squash₁ : ∀ x y → -- x ≡ y -- this raises an error
                             PathP (λ i → typ (B∙ (squash₁ ∣ x ∣₁ ∣ y ∣₁ i))) x y
    recover-squash₁ x y = cong recover (squash₁ ∣ x ∣₁ ∣ y ∣₁)


-- Demo, adapted from:
-- https://bitbucket.org/nicolaikraus/agda/src/e30d70c72c6af8e62b72eefabcc57623dd921f04/trunc-inverse.lagda

private
  open import Cubical.Data.Nat
  open Recover (ℕ , zero) (isHomogeneousDiscrete discreteℕ)

  -- only `∣hidden∣` is exported, `hidden` is no longer in scope
  module _ where
    private
      hidden : ℕ
      hidden = 17

    ∣hidden∣ : ∥ ℕ ∥₁
    ∣hidden∣ = ∣ hidden ∣₁

  -- we can still recover the value, even though agda can no longer see `hidden`!
  test : recover ∣hidden∣ ≡ 17
  test = refl -- try it: `C-c C-n recover ∣hidden∣` gives `17`
              --         `C-c C-n hidden` gives an error

  -- Finally, note that the definition of recover is independent of the proof that A is homogeneous. Thus we
  --  still can definitionally recover information hidden by ∣_∣₁ as long as we permit holes. Try replacing
  --  `isHomogeneousDiscrete discreteℕ` above with a hole (`?`) and notice that everything still works
