{-# OPTIONS --cubical #-}
module Cubical.Experiments.Brunerie where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.HomotopyGroup
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Hopf
open import Cubical.HITs.SetTruncation as SetTrunc
open import Cubical.HITs.GroupoidTruncation as GroupoidTrunc
open import Cubical.HITs.2GroupoidTruncation as 2GroupoidTrunc

-- This code is adapted from examples/brunerie3.ctt on the pi4s3_nobug branch of cubicaltt

Bool∙ S¹∙ S²∙ S³∙ : Pointed₀
Bool∙ = (Bool , true)
S¹∙ = (S¹ , base)
S²∙ = (S² , base)
S³∙ = (S³ , base)

∥_∥₁∙ ∥_∥₂∙ : Pointed₀ → Pointed₀
∥ A , a ∥₁∙ = ∥ A ∥₁ , ∣ a ∣₁
∥ A , a ∥₂∙ = ∥ A ∥₂ , ∣ a ∣₂

join∙ : Pointed₀ → Type₀ → Pointed₀
join∙ (A , a) B = join A B , inl a

Ω² Ω³ : Pointed₀ → Pointed₀
Ω² = Ω^ 2
Ω³ = Ω^ 3

mapΩrefl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω A .fst → Ω (B , f (pt A)) .fst
mapΩrefl f p i = f (p i)

mapΩ²refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω² A .fst → Ω² (B , f (pt A)) .fst
mapΩ²refl f p i j = f (p i j)

mapΩ³refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω³ A .fst → Ω³ (B , f (pt A)) .fst
mapΩ³refl f p i j k = f (p i j k)

meridS² : S¹ → Path S² base base
meridS² base _ = base
meridS² (loop i) j = surf i j

alpha : join S¹ S¹ → S²
alpha (inl x) = base
alpha (inr y) = base
alpha (push x y i) = (meridS² y ∙ meridS² x) i

connectionBoth : {A : Type₀} {a : A} (p : Path A a a) → PathP (λ i → Path A (p i) (p i)) p p
connectionBoth {a = a} p i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → p (j ∧ k)
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → p (i ∧ k)
      })
    a

data PostTotalHopf : Type₀ where
  base : S¹ → PostTotalHopf
  loop : (x : S¹) → PathP (λ i → Path PostTotalHopf (base x) (base (rotLoop x (~ i)))) refl refl

tee12 : (x : S²) → HopfS² x → PostTotalHopf
tee12 base y = base y
tee12 (surf i j) y =
  hcomp
    (λ k → λ
      { (i = i0) → base y
      ; (i = i1) → base y
      ; (j = i0) → base y
      ; (j = i1) → base (rotLoopInv y (~ i) k)
      })
    (loop (unglue (i ∨ ~ i ∨ j ∨ ~ j) y) i j)

tee34 : PostTotalHopf → join S¹ S¹
tee34 (base x) = inl x
tee34 (loop x i j) =
  hcomp
    (λ k → λ
      { (i = i0) → push x x (j ∧ ~ k)
      ; (i = i1) → push x x (j ∧ ~ k)
      ; (j = i0) → inl x
      ; (j = i1) → push (rotLoop x (~ i)) x (~ k)
      })
    (push x x j)

tee : (x : S²) → HopfS² x → join S¹ S¹
tee x y = tee34 (tee12 x y)

fibΩ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω B .fst → Type₀
fibΩ P f p = PathP (λ i → P (p i)) f f

fibΩ² : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω² B .fst → Type₀
fibΩ² P f = fibΩ (fibΩ P f) refl

fibΩ³ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω³ B .fst → Type₀
fibΩ³ P f = fibΩ² (fibΩ P f) refl

Ω³Hopf : Ω³ S²∙ .fst → Type₀
Ω³Hopf = fibΩ³ HopfS² base

fibContrΩ³Hopf : ∀ p → Ω³Hopf p
fibContrΩ³Hopf p i j k =
  hcomp
    (λ m → λ
      { (i = i0) → base
      ; (i = i1) → base
      ; (j = i0) → base
      ; (j = i1) → base
      ; (k = i0) → base
      ; (k = i1) →
        isSetΩS¹ refl refl
          (λ i j → transp (λ n → HopfS² (p i j n)) (i ∨ ~ i ∨ j ∨ ~ j) base)
          (λ _ _ → base)
          m i j
      })
    (transp (λ n → HopfS² (p i j (k ∧ n))) (i ∨ ~ i ∨ j ∨ ~ j ∨ ~ k) base)

h : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
h p i j k = tee (p i j k) (fibContrΩ³Hopf p i j k)

multTwoAux : (x : S²) → Path (Path ∥ S² ∥₂ ∣ x ∣₂ ∣ x ∣₂) refl refl
multTwoAux base i j = ∣ surf i j ∣₂
multTwoAux (surf k l) i j =
  hcomp
    (λ m → λ
      { (i = i0) → ∣ surf k l ∣₂
      ; (i = i1) → ∣ surf k l ∣₂
      ; (j = i0) → ∣ surf k l ∣₂
      ; (j = i1) → ∣ surf k l ∣₂
      ; (k = i0) → ∣ surf i j ∣₂
      ; (k = i1) → ∣ surf i j ∣₂
      ; (l = i0) → ∣ surf i j ∣₂
      ; (l = i1) → squash₂ _ _ _ _ _ _ (λ k i j → step₁ k i j) refl m k i j
      })
    (step₁ k i j)

  where
  step₁ : I → I → I → ∥ S² ∥₂
  step₁ k i j =
    hcomp {A = ∥ S² ∥₂}
      (λ m → λ
        { (i = i0) → ∣ surf k (l ∧ m) ∣₂
        ; (i = i1) → ∣ surf k (l ∧ m) ∣₂
        ; (j = i0) → ∣ surf k (l ∧ m) ∣₂
        ; (j = i1) → ∣ surf k (l ∧ m) ∣₂
        ; (k = i0) → ∣ surf i j ∣₂
        ; (k = i1) → ∣ surf i j ∣₂
        ; (l = i0) → ∣ surf i j ∣₂
        })
     ∣ surf i j ∣₂

multTwoTildeAux : (t : ∥ S² ∥₂) → Path (Path ∥ S² ∥₂ t t) refl refl
multTwoTildeAux ∣ x ∣₂ = multTwoAux x
multTwoTildeAux (squash₂ _ _ _ _ _ _ t u k l m n) i j =
  squash₂ _ _ _ _ _ _
    (λ k l m → multTwoTildeAux (t k l m) i j)
    (λ k l m → multTwoTildeAux (u k l m) i j)
    k l m n

multTwoEquivAux : Path (Path (∥ S² ∥₂ ≃ ∥ S² ∥₂) (idEquiv _) (idEquiv _)) refl refl
multTwoEquivAux i j =
  ( f i j
  , hcomp
      (λ l → λ
        { (i = i0) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (i = i1) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (j = i0) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (j = i1) →
          isPropIsEquiv _
            (transp (λ k → isEquiv (f i k)) (i ∨ ~ i) (idIsEquiv _))
            (idIsEquiv _)
            l
        })
      (transp (λ k → isEquiv (f i (j ∧ k))) (i ∨ ~ i ∨ ~ j) (idIsEquiv _))
  )
  where
  f : I → I → ∥ S² ∥₂ → ∥ S² ∥₂
  f i j t = multTwoTildeAux t i j

tHopf³ : S³ → Type₀
tHopf³ base = ∥ S² ∥₂
tHopf³ (surf i j k) =
  Glue ∥ S² ∥₂
    (λ { (i = i0) → (∥ S² ∥₂ , idEquiv _)
       ; (i = i1) → (∥ S² ∥₂ , idEquiv _)
       ; (j = i0) → (∥ S² ∥₂ , idEquiv _)
       ; (j = i1) → (∥ S² ∥₂ , idEquiv _)
       ; (k = i0) → (∥ S² ∥₂ , multTwoEquivAux i j)
       ; (k = i1) → (∥ S² ∥₂ , idEquiv _)
       })

π₃S³ : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₂∙ .fst
π₃S³ p i j = transp (λ k → tHopf³ (p j k i)) i0 ∣ base ∣₂

codeS² : S² → hGroupoid _
codeS² s = ∥ HopfS² s ∥₁ , squash₁

codeTruncS² : ∥ S² ∥₂ → hGroupoid _
codeTruncS² = 2GroupoidTrunc.rec (isOfHLevelHLevel 3) codeS²

encodeTruncS² : Ω ∥ S²∙ ∥₂∙ .fst → ∥ S¹ ∥₁
encodeTruncS² p = transp (λ i → codeTruncS² (p i) .fst) i0 ∣ base ∣₁

codeS¹ : S¹ → hSet _
codeS¹ s = ∥ helix s ∥₀ , squash₀

codeTruncS¹ : ∥ S¹ ∥₁ → hSet _
codeTruncS¹ = GroupoidTrunc.rec (isOfHLevelHLevel 2) codeS¹

encodeTruncS¹ : Ω ∥ S¹∙ ∥₁∙ .fst → ∥ Int ∥₀
encodeTruncS¹ p = transp (λ i → codeTruncS¹ (p i) .fst) i0 ∣ pos zero ∣₀


-- THE BIG GAME

f3 : Ω³ S³∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f3 = mapΩ³refl S³→joinS¹S¹

f4 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S²∙ .fst
f4 = mapΩ³refl alpha

f5 : Ω³ S²∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f5 = h

f6 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S³∙ .fst
f6 = mapΩ³refl joinS¹S¹→S³

f7 : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₂∙ .fst
f7 = π₃S³

g8 : Ω² ∥ S²∙ ∥₂∙ .fst → Ω ∥ S¹∙ ∥₁∙ .fst
g8 = mapΩrefl encodeTruncS²

g9 : Ω ∥ S¹∙ ∥₁∙ .fst → ∥ Int ∥₀
g9 = encodeTruncS¹

g10 : ∥ Int ∥₀ → Int
g10 = SetTrunc.elim (λ _ → isSetInt) (idfun Int)

-- don't run me
brunerie : Int
brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))

-- simpler tests

test63 : ℕ → Int
test63 n = g10 (g9 (g8 (f7 (63n n))))
  where
  63n : ℕ → Ω³ S³∙ .fst
  63n zero i j k = surf i j k
  63n (suc n) = f6 (f3 (63n n))

foo : Ω³ S²∙ .fst
foo i j k =
  hcomp
    (λ l → λ
      { (i = i0) → surf l l
      ; (i = i1) → surf l l
      ; (j = i0) → surf l l
      ; (j = i1) → surf l l
      ; (k = i0) → surf l l
      ; (k = i1) → surf l l
      })
    base

sorghum : Ω³ S²∙ .fst
sorghum i j k =
  hcomp
    (λ l → λ
      { (i = i0) → surf j l
      ; (i = i1) → surf k (~ l)
      ; (j = i0) → surf k (i ∧ ~ l)
      ; (j = i1) → surf k (i ∧ ~ l)
      ; (k = i0) → surf j (i ∨ l)
      ; (k = i1) → surf j (i ∨ l)
      })
    (hcomp
      (λ l → λ
        { (i = i0) → base
        ; (i = i1) → surf j l
        ; (j = i0) → surf k i
        ; (j = i1) → surf k i
        ; (k = i0) → surf j (i ∧ l)
        ; (k = i1) → surf j (i ∧ l)
        })
      (surf k i))

goo : Ω³ S²∙ .fst → Int
goo x = g10 (g9 (g8 (f7 (f6 (f5 x)))))




-- Marc's tests (with some rotations):

fun : Ω² ∥ S²∙ ∥₂∙ .fst → Int
fun x = g10 (g9 (g8 x))

inv1 : Ω² ∥ S²∙ ∥₂∙ .fst
inv1 i j = ∣ surf i j ∣₂

inv1' : Ω² ∥ S²∙ ∥₂∙ .fst
inv1' i j = ∣ surf (~ i) j ∣₂

inv1'' : Ω² ∥ S²∙ ∥₂∙ .fst
inv1'' i j = ∣ surf i (~ j) ∣₂

inv1''' : Ω² ∥ S²∙ ∥₂∙ .fst
inv1''' i j = ∣ surf (~ i) (~ j) ∣₂

test1 : fun inv1 ≡ neg 1
test1 = refl

test1' : fun inv1' ≡ pos 1
test1' = refl

test1'' : fun inv1'' ≡ pos 1
test1'' = refl

test1''' : fun inv1''' ≡ neg 1
test1''' = refl



-- Degrees of maps experiment

-- The eᵢ maps from the paper. We only use the underlying functions,
-- but it's easy to prove that they're all equivalences.

e₀ : Susp S¹ ≃ Susp S¹
e₀ = idEquiv _

e₁ : Susp S¹ ≃ Susp S¹
e₁ = isoToEquiv (iso f f Hf Hf)
  where
  f : Susp S¹ → Susp S¹
  f north = north
  f south = south
  f (merid base i) = merid base i
  f (merid (loop j) i) = merid (loop (~ j)) i

  Hf : (x : Susp S¹) → f (f x) ≡ x
  Hf north = refl
  Hf south = refl
  Hf (merid base i) = refl
  Hf (merid (loop j) i) = refl

e₂ : Susp S¹ ≃ Susp S¹
e₂ = isoToEquiv (iso f f Hf Hf)
  where
  f : Susp S¹ → Susp S¹
  f north = south
  f south = north
  f (merid x i) = merid x (~ i)

  Hf : (x : Susp S¹) → f (f x) ≡ x
  Hf north = refl
  Hf south = refl
  Hf (merid a i) = refl

e₃ : Susp S¹ ≃ Susp S¹
e₃ = isoToEquiv (iso f f Hf Hf)
  where
  f : Susp S¹ → Susp S¹
  f north = south
  f south = north
  f (merid base i) = merid base (~ i)
  f (merid (loop j) i) = merid (loop (~ j)) (~ i)

  Hf : (x : Susp S¹) → f (f x) ≡ x
  Hf north = refl
  Hf south = refl
  Hf (merid base i) = refl
  Hf (merid (loop j) i) = refl

-- Use univalence to turn these into paths (not used anywhere)
p₀ : Susp S¹ ≡ Susp S¹
p₀ = ua e₀

p₁ : Susp S¹ ≡ Susp S¹
p₁ = ua e₁

p₂ : Susp S¹ ≡ Susp S¹
p₂ = ua e₂

p₃ : Susp S¹ ≡ Susp S¹
p₃ = ua e₃


-- The map h from Marc's email
f1 : ∥ Ω² S²∙ .fst ∥₀ → Ω ∥ Ω S²∙ ∥₁∙ .fst
f1 x = SetTrunc.elim (λ _ → squash₁ _ _) (λ p i → ∣ p i ∣₁) x

-- The map one level up
f2 : Ω ∥ Ω S²∙ ∥₁∙ .fst → Ω² ∥ S²∙ ∥₂∙ .fst
f2 p i = GroupoidTrunc.elim (λ x → squash₂ _ _) (λ x j → ∣ x j ∣₂) (p i)

-- Two versions of Susp S¹ as pointed types
SuspS¹∙_south : Pointed₀
SuspS¹∙_south = (Susp S¹) , south

SuspS¹∙ : Pointed₀
SuspS¹∙ = (Susp S¹) , north

-- A small sanity check (and nice use of ua-gluePath)
S²∙≡SuspS¹∙ : S²∙ ≡ SuspS¹∙
S²∙≡SuspS¹∙ i = S²≡SuspS¹ i , ua-gluePath S²≃SuspS¹ {x = base} refl i

-- Two versions of the function we want to use depending on whether we
-- use north or south
fun_north : Ω² SuspS¹∙ .fst → Int
fun_north p = fun (f2 (f1 ∣ (λ i j → SuspS¹→S² (p i j)) ∣₀))

fun_south : Ω² SuspS¹∙_south .fst → Int
fun_south p = fun (f2 (f1 ∣ (λ i j → SuspS¹→S² (p i j)) ∣₀))


-- Tests:

test_e₀ : fun_north (λ i j → e₀ .fst (S²→SuspS¹ (surf i j))) ≡ neg 1
test_e₀ = refl

test_e₁ : fun_north (λ i j → e₁ .fst (S²→SuspS¹ (surf i j))) ≡ pos 1
test_e₁ = refl

test_e₂ : fun_south (λ i j → e₂ .fst (S²→SuspS¹ (surf i j))) ≡ pos 1
test_e₂ = refl

test_e₃ : fun_south (λ i j → e₃ .fst (S²→SuspS¹ (surf i j))) ≡ neg 1
test_e₃ = refl
