-- Jasper Hugunin's construction of natural numbers
-- Carlo Angiuli
-- October 26, 2020

{-# OPTIONS --without-K --safe #-}
module Cubical.JasperNats where

open import Agda.Primitive
-- open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}

data ⊥ : Set where

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (f : B a → W A B) → W A B

J : {A : Set} {x y : A} (P : (y : A) → x ≡ y → Set) → (p : x ≡ y) → P x refl → P y p
J P refl px = px

-- Ordinary definition.

ℕ̃ : Set
ℕ̃ = W Bool (λ {true → ⊥ ; false → ⊤})

z̃ : ℕ̃
z̃ = sup true λ ()

s̃ : ℕ̃ → ℕ̃
s̃ ñ = sup false (λ _ → ñ)

-- Fixing it up.

canonical : ℕ̃ → Set
canonical (sup true f) = (λ ()) ≡ f
canonical (sup false f) = canonical (f tt)

ℕ : Set
ℕ = Σ ℕ̃ canonical

z : ℕ
z = z̃ , refl

s : ℕ → ℕ
s x = s̃ (fst x) , snd x

indℕ : (P : ℕ → Set) → P z → ((n : ℕ) → P n → P (s n)) → (n : ℕ) → P (fst n , snd n)
indℕ P pz ps x = foo (fst x) (snd x)
  where
  foo : (n : ℕ̃) → (p : canonical n) → P (n , p)
  foo (sup true f) pf = J {x = λ ()} (λ y p → P (sup true y , p)) pf pz
  foo (sup false f) pf = ps (f tt , pf) (foo (f tt) pf)

compZ : (P : ℕ → Set) (pz : P z) (ps : (n : ℕ) → P n → P (s n))
        → indℕ P pz ps z ≡ pz
compZ _ _ _ = refl

compS : (P : ℕ → Set) (pz : P z) (ps : (n : ℕ) → P n → P (s n)) (n : ℕ)
        → indℕ P pz ps (s n) ≡ ps n (indℕ P pz ps n)
compS _ _ _ _ = refl
