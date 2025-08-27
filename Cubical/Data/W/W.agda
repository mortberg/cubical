
module Cubical.Data.W.W where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level

data W (S : Type ℓ) (P : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  sup-W : (s : S) → (P s → W S P) → W S P

WInd : (S : Type ℓ) (P : S → Type ℓ') (M : W S P → Type ℓ'') →
       (e : {s : S} {f : P s → W S P} → ((p : P s) → M (f p)) → M (sup-W s f)) →
       (w : W S P) → M w
WInd S P M e (sup-W s f) = e (λ p → WInd S P M e (f p))

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

overline-W : {A : Type ℓ} {B : A → Type ℓ'} (x : W A B) → A
overline-W (sup-W x f) = x

tilde-W : {A : Type ℓ} {B : A → Type ℓ'} (x : W A B) → B (overline-W x) → W A B
tilde-W (sup-W x f) = f

thm3 : 
  (x y : W Type (λ x → x)) →
  (x ≡ y) ≃ (Σ[ e ∈ overline-W x ≃ overline-W y ]
               ((b : overline-W x) → tilde-W x b ≡ tilde-W y (e .fst b)))
thm3 x y = isoToEquiv (iso (f x y) (g x y) (p1 x y) (p2 x y))
  where
  f : (x y : W Type (λ x → x)) →
      (x ≡ y) → Σ[ e ∈ overline-W x ≃ overline-W y ]
                 ((b : overline-W x) → tilde-W x b ≡ tilde-W y (e .fst b))
  f x y = J (λ (z : _) (p : x ≡ z) → Σ[ e ∈ overline-W x ≃ overline-W z ]
                 ((b : overline-W x) → tilde-W x b ≡ tilde-W z (e .fst b)))
        (idEquiv _ , λ _ → refl)

  g : (x y : W Type (λ x → x))
    → Σ[ e ∈ overline-W x ≃ overline-W y ]
       ((b : overline-W x) → tilde-W x b ≡ tilde-W y (e .fst b))
    → x ≡ y
  g (sup-W x f) (sup-W y g) (e , p) = cong₂ sup-W (ua e) (ua→ p)

  p1 : (x y : W Type (λ x → x)) → section (f x y) (g x y)
  p1 (sup-W x f) (sup-W y g) (e , p) = ΣPathP (equivEq (transportRefl _) , funExt (λ foo → {!!}))

  p2 : (x y : W Type (λ x → x)) → retract (f x y) (g x y)
  p2 x = J> cong (g x x) (transportRefl _) ∙ rem x 
    where
    rem : (x : W Type (λ x → x)) → g x x (idEquiv (overline-W x) , (λ z _ → tilde-W x z)) ≡  (λ _ → x)
    rem (sup-W x f) i j = {!!}

open Iso

thm4 : 
  (x y : W Type (λ x → x)) →
  (x ≡ y) ≃ ((z : W Type (λ x → x)) → fiber (tilde-W x) z ≃ fiber (tilde-W y) z)
thm4 x y = isoToEquiv (iso (f x y) (g x y) (p1 x y) (p2 x y))
  where
  f : (x y : W Type (λ x → x)) →
      (x ≡ y) →
      ((z : W Type (λ x → x)) → fiber (tilde-W x) z ≃ fiber (tilde-W y) z)
  f x y p z = {!!} -- Σ-cong' (cong overline-W p) λ i w → {!cong tilde-W p!}
  
  g : (x y : W Type (λ x → x))
    → ((z : W Type (λ x → x)) → fiber (tilde-W x) z ≃ fiber (tilde-W y) z)
    → x ≡ y
  g (sup-W x f) (sup-W y g) h = {! f!} -- cong₂ sup-W {!ua (h (sup-W y g))!} {!!}
    where
    rem1 : (Σ[ z ∈ x ] f z ≡ sup-W x f) ≃ (Σ[ z ∈ y ] g z ≡ sup-W x f)
    rem1 = h (sup-W x f)

    rem2 : fiber f (sup-W y g) ≃ fiber g (sup-W y g)
    rem2 = h (sup-W y g)

    rem3 : (a : W Type (λ x₁ → x₁)) → fiber f a → fiber g a
    rem3 = Σ-Π-Iso .fun h .fst

    rem4 : (a : W Type (λ x₁ → x₁)) → isEquiv (fun Σ-Π-Iso h .fst a)
    rem4 = Σ-Π-Iso .fun h .snd

  p1 : (x y : W Type (λ x → x)) → section (f x y) (g x y)
  p1 x y = {!!}

  p2 : (x y : W Type (λ x → x)) → retract (f x y) (g x y)
  p2 x y = {!!}

_≡W_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → W A B → W A B → Type (ℓ-max ℓ ℓ')
_≡W_ {A = A} {B = B} x y = Σ[ p ∈ overline-W x ≡ overline-W y ]
                              PathP (λ i → B (p i) → W A B) (tilde-W x) (tilde-W y)

f : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → x ≡ y → x ≡W y
f x y p = (cong overline-W p) , (cong tilde-W p)

g : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → x ≡W y → x ≡ y
g (sup-W _ _) (sup-W _ _) (p , q) = cong₂ sup-W p q

sec : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → section (f x y) (g x y)
sec (sup-W _ _) (sup-W _ _) (p , q) = refl

ret : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → retract (f x y) (g x y)
ret (sup-W _ _) = J> refl

firstGoal : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → (x ≡ y) ≃ (x ≡W y)
firstGoal x y = isoToEquiv (iso (f x y) (g x y) (sec x y) (ret x y))

_≡W'_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → W A B → W A B → Type (ℓ-max ℓ ℓ')
_≡W'_ {A = A} {B = B} x y = Σ[ p ∈ overline-W x ≡ overline-W y ]
                            ((a : B (overline-W x)) → tilde-W x a ≡ tilde-W y (subst B p a))

≡W≃≡W' : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → (x ≡W y) ≃ (x ≡W' y)
≡W≃≡W' {A = A} {B = B} x y = {!!}

goal : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → (x ≡ y) ≃ (x ≡W' y)
goal x y = compEquiv (firstGoal x y) (≡W≃≡W' x y)


  -- Σ[ p ∈ overline-W x ≡ overline-W y ]
  --   let -- rem1 : PathP (λ i₁ → B (p i₁) → W A B) (tilde-W x) (tilde-W y) ≡ Path (B (overline-W y) → W A B) (transport (λ i₁ → B (p i₁) → W A B) (tilde-W x)) (tilde-W y)
  --       -- rem1 = PathP≡Path (λ i → B (p i) → W A B) (tilde-W x) (tilde-W y)
  --       -- rem2 : (transport (λ i₁ → B (p i₁) → W A B) (tilde-W x) ≡ tilde-W y) ≡
  --       --        ({a : B (overline-W y)} → transport (λ i → B (p i) → W A B) (tilde-W x) a ≡ tilde-W y a)
  --       -- rem2 = {!sym funExtPath!}
  --       -- rem3 : PathP (λ i₁ → B (p i₁) → W A B) (tilde-W x) (tilde-W y) ≡ ({x₀ : B (p i0)} {x₁ : B (p i1)} →
  --       --                                                                   PathP (λ z → B (p z)) x₀ x₁ → tilde-W x x₀ ≡ tilde-W y x₁)
  --       -- rem3 = sym funExtNonDepPath
  --       goal : PathP (λ i₁ → B (p i₁) → W A B) (tilde-W x) (tilde-W y) ≡ ((a : B (overline-W x)) → tilde-W x a ≡ tilde-W y (subst B p a))
  --       goal = isoToPath (iso (λ q a i → q i (subst-filler B p a i)) (λ q → {!toPathP!}) {!!} {!!})
  --   in goal i




-- sec {A = A} {B = B} (sup-W x α) (sup-W y β) (p , q) = rem y p β q
--   where
--   rem : (y : A) (p : x ≡ y) (β  : B y → W A B) (q : PathP (λ i → B (p i) → W A B) α β) →
--         f (sup-W x α) (sup-W y β) (λ i → sup-W (p i) (q i)) ≡ (p , q)
--   rem = J> (J> transportRefl _)

-- ret : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → retract (f x y) (g x y)
-- ret (sup-W x α) =
--   J> λ i j → hcomp (λ k → λ { (i = i0) → sup-W (f-refl (sup-W x α) (~ k) .fst j) (f-refl (sup-W x α) (~ k) .snd j)
--                             ; (i = i1) → sup-W x α
--                             ; (j = i0) → sup-W x α
--                             ; (j = i1) → sup-W x α })
--                    (sup-W x α)


-- sec : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → section (f x y) (g x y)
-- sec {A = A} {B = B} (sup-W x α) (sup-W y β) (p , q) = rem y p β q
--   where
--   rem : (y : A) (p : x ≡ y) (β  : B y → W A B) (q : PathP (λ i → B (p i) → W A B) α β) →
--         f (sup-W x α) (sup-W y β) (λ i → sup-W (p i) (q i)) ≡ (p , q)
--   rem = J> (J> transportRefl _)

-- ret : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → retract (f x y) (g x y)
-- ret (sup-W x α) =
--   J> λ i j → hcomp (λ k → λ { (i = i0) → sup-W (f-refl (sup-W x α) (~ k) .fst j) (f-refl (sup-W x α) (~ k) .snd j)
--                             ; (i = i1) → sup-W x α
--                             ; (j = i0) → sup-W x α
--                             ; (j = i1) → sup-W x α })
--                    (sup-W x α)
