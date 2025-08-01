{-

Definition of the integers as a HIT ported from the redtt library:

  https://github.com/RedPRL/redtt/blob/master/library/cool/biinv-int.red

For the naive, but incorrect, way to define the integers as a HIT, see HITs.IsoInt

This file contains:
- definition of BiInvInt
- proof that Int ≡ BiInvInt
- [discreteBiInvInt] and [isSetBiInvInt]
- versions of the point constructors of BiInvInt which satisfy the path constructors judgmentally

-}
module Cubical.Data.Int.MoreInts.BiInvInt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.Relation.Nullary


data BiInvℤ : Type₀ where
  zero : BiInvℤ
  suc : BiInvℤ -> BiInvℤ

  -- suc is a bi-invertible equivalence:
  predr : BiInvℤ -> BiInvℤ
  suc-predr : ∀ z -> suc (predr z) ≡ z
  predl : BiInvℤ -> BiInvℤ
  predl-suc : ∀ z -> predl (suc z) ≡ z


suc-biinvequiv : BiInvEquiv BiInvℤ BiInvℤ
suc-biinvequiv = record { fun = suc ; invr = predr ; invr-rightInv = suc-predr
                                    ; invl = predl ; invl-leftInv  = predl-suc }

predr-suc : ∀ z -> predr (suc z) ≡ z
predr-suc = BiInvEquiv.invr-leftInv suc-biinvequiv

-- since we want to use suc-adj and pred-adj (defined below) later on, we will need the
--  definition of suc-predl taken from HAEquiv instead of from BiInvEquiv

suc-haequiv : HAEquiv BiInvℤ BiInvℤ
suc-haequiv = biInvEquiv→HAEquiv suc-biinvequiv

suc-predl : ∀ z -> suc (predl z) ≡ z
suc-predl = isHAEquiv.rinv (snd suc-haequiv)

-- predr and predl (as well as suc-predr and suc-predl - up to a path) are indistinguishable,
--  so we can safely define 'pred' to just be predl

predl≡predr : ∀ z -> predl z ≡ predr z
predl≡predr z i = cong fst (isContr→isProp (isContr-hasSection (biInvEquiv→Equiv-left suc-biinvequiv))
                                           (predl , suc-predl) (predr , suc-predr)) i z

suc-predl≡predr : ∀ z -> PathP (λ j → suc (predl≡predr z j) ≡ z) (suc-predl z) (suc-predr z)
suc-predl≡predr z i = cong snd (isContr→isProp (isContr-hasSection (biInvEquiv→Equiv-left suc-biinvequiv))
                                               (predl , suc-predl) (predr , suc-predr)) i z

pred : BiInvℤ -> BiInvℤ
pred = predl

suc-pred = suc-predl
pred-suc = predl-suc

-- these paths from HAEquiv will be useful later
suc-adj  : ∀ z → (λ i → suc (pred-suc z i)) ≡ suc-pred (suc z)
pred-adj : ∀ z → (λ i → pred (suc-pred z i)) ≡ pred-suc (pred z)
suc-adj  z = isHAEquiv.com (snd suc-haequiv) z
pred-adj z = isHAEquiv.com-op (snd suc-haequiv) z



-- ℤ ≡ BiInvℤ

fwd : ℤ -> BiInvℤ
fwd (pos zero)       = zero
fwd (pos (suc n))    = suc (fwd (pos n))
fwd (negsuc zero)    = pred zero
fwd (negsuc (suc n)) = pred (fwd (negsuc n))

bwd : BiInvℤ -> ℤ
bwd zero            = pos zero
bwd (suc z)         = sucℤ (bwd z)
bwd (predr z)       = predℤ (bwd z)
bwd (suc-predr z i) = sucPred (bwd z) i
bwd (predl z)       = predℤ (bwd z)
bwd (predl-suc z i) = predSuc (bwd z) i

bwd-fwd : ∀ (x : ℤ) -> bwd (fwd x) ≡ x
bwd-fwd (pos zero)       = refl
bwd-fwd (pos (suc n))    = cong sucℤ (bwd-fwd (pos n))
bwd-fwd (negsuc zero)    = refl
bwd-fwd (negsuc (suc n)) = cong predℤ (bwd-fwd (negsuc n))


fwd-sucℤ : ∀ (x : ℤ) → fwd (sucℤ x) ≡ suc (fwd x)
fwd-sucℤ (pos n)          = refl
fwd-sucℤ (negsuc zero)    = sym (suc-pred (fwd (pos zero)))
fwd-sucℤ (negsuc (suc n)) = sym (suc-pred (fwd (negsuc n)))

fwd-predℤ : ∀ (x : ℤ) → fwd (predℤ x) ≡ pred (fwd x)
fwd-predℤ (pos zero)    = refl
fwd-predℤ (pos (suc n)) = sym (predl-suc (fwd (pos n)))
fwd-predℤ (negsuc n)    = refl

private
  sym-filler : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
                → Square {- (i = i0) -} (sym p)
                         {- (i = i1) -} refl
                         {- (j = i0) -} refl
                         {- (j = i1) -} p
  sym-filler {y = y} p i j = hcomp (λ k → λ { (j = i0) → y
                                            ; (i = i0) → p ((~ j) ∨ (~ k))
                                            ; (i = i1) → y
                                            ; (j = i1) → p (i ∨ (~ k)) }) y

fwd-sucPred : ∀ (x : ℤ)
              → Square {- (i = i0) -} (fwd-sucℤ (predℤ x) ∙ (λ i → suc (fwd-predℤ x i)))
                       {- (i = i1) -} (λ _ → fwd x)
                       {- (j = i0) -} (λ i → fwd (sucPred x i))
                       {- (j = i1) -} (suc-pred (fwd x))


fwd-sucPred (pos zero) i j
  = hcomp (λ k → λ { (j = i0) → fwd (pos zero)
                   ; (i = i0) → rUnit (sym (suc-pred (fwd (pos zero)))) k j
                                -- because fwd-sucℤ (predℤ (pos zero)) ≡ sym (suc-pred (fwd (pos zero)))
                   ; (i = i1) → fwd (pos zero)
                   ; (j = i1) → suc-pred (fwd (pos zero)) i
                   })
          (sym-filler (suc-pred (fwd (pos zero))) i j)

fwd-sucPred (pos (suc n)) i j
  = hcomp (λ k → λ { (j = i0) → suc (fwd (pos n))
                   ; (i = i0) → lUnit (λ i → suc (sym (predl-suc (fwd (pos n))) i)) k j
                                -- because fwd-predℤ (pos (suc n)) ≡ sym (predl-suc (fwd (pos n)))
                   ; (i = i1) → suc (fwd (pos n))
                   ; (j = i1) → suc-adj (fwd (pos n)) k i
                   })
          (suc (sym-filler (pred-suc (fwd (pos n))) i j))

fwd-sucPred (negsuc n) i j
  = hcomp (λ k → λ { (j = i0) → fwd (negsuc n)
                   ; (i = i0) → rUnit (sym (suc-pred (fwd (negsuc n)))) k j
                                -- because fwd-sucℤ (predℤ (negsuc n)) ≡ sym (suc-pred (fwd (negsuc n)))
                   ; (i = i1) → fwd (negsuc n)
                   ; (j = i1) → suc-pred (fwd (negsuc n)) i
                   })
          (sym-filler (suc-pred (fwd (negsuc n))) i j)


fwd-predSuc : ∀ (x : ℤ)
              → Square {- (i = i0) -} (fwd-predℤ (sucℤ x) ∙ (λ i → pred (fwd-sucℤ x i)))
                       {- (i = i1) -} (λ _ → fwd x)
                       {- (j = i0) -} (λ i → fwd (predSuc x i))
                       {- (j = i1) -} (pred-suc (fwd x))

fwd-predSuc (pos n) i j
  = hcomp (λ k → λ { (j = i0) → fwd (pos n)
                   ; (i = i0) → rUnit (sym (pred-suc (fwd (pos n)))) k j
                                -- because fwd-predℤ (sucℤ (pos n)) ≡ sym (pred-suc (fwd (pos n)))
                   ; (i = i1) → fwd (pos n)
                   ; (j = i1) → pred-suc (fwd (pos n)) i
                   })
          (sym-filler (pred-suc (fwd (pos n))) i j)

fwd-predSuc (negsuc zero) i j
  = hcomp (λ k → λ { (j = i0) → fwd (negsuc zero)
                   ; (i = i0) → lUnit (λ i → pred (sym (suc-pred (fwd (pos zero))) i)) k j
                                -- because fwd-sucℤ (negsuc zero) ≡ sym (suc-pred (fwd (pos zero)))
                   ; (i = i1) → fwd (negsuc zero)
                   ; (j = i1) → pred-adj (fwd (pos zero)) k i
                   })
          (pred (sym-filler (suc-pred (fwd (pos zero))) i j))

fwd-predSuc (negsuc (suc n)) i j
  = hcomp (λ k → λ { (j = i0) → fwd (negsuc (suc n))
                   ; (i = i0) → lUnit (λ i → pred (sym (suc-pred (fwd (negsuc n))) i)) k j
                                -- because fwd-sucℤ (negsuc (suc n)) ≡ sym (suc-pred (fwd (negsuc n)))
                   ; (i = i1) → fwd (negsuc (suc n))
                   ; (j = i1) → pred-adj (fwd (negsuc n)) k i
                   })
          (pred (sym-filler (suc-pred (fwd (negsuc n))) i j))


fwd-bwd : ∀ (z : BiInvℤ) -> fwd (bwd z) ≡ z
fwd-bwd zero      = refl
fwd-bwd (suc z)   = fwd-sucℤ  (bwd z) ∙ (λ i → suc (fwd-bwd z i))
fwd-bwd (predr z) = fwd-predℤ (bwd z) ∙ (λ i → predl≡predr (fwd-bwd z i) i)
fwd-bwd (predl z) = fwd-predℤ (bwd z) ∙ (λ i → pred (fwd-bwd z i))
fwd-bwd (suc-predr z i) j
  = hcomp (λ k → λ { (j = i0) → fwd (sucPred (bwd z) i)
                   ; (i = i0) → (fwd-sucℤ (predℤ (bwd z))
                                 ∙ (λ i → suc (compPath-filler (fwd-predℤ (bwd z))
                                                               (λ i' → predl≡predr (fwd-bwd z i') i')
                                                               k i))) j
                   ; (i = i1) → fwd-bwd z (j ∧ k)
                   ; (j = i1) → suc-predl≡predr (fwd-bwd z k) k i })
          (fwd-sucPred (bwd z) i j)
fwd-bwd (predl-suc z i) j
  = hcomp (λ k → λ { (j = i0) → fwd (predSuc (bwd z) i)
                   ; (i = i0) → (fwd-predℤ (sucℤ (bwd z))
                                 ∙ (λ i → pred (compPath-filler (fwd-sucℤ (bwd z))
                                                                (λ i' → suc (fwd-bwd z i'))
                                                                k i))) j
                   ; (i = i1) → fwd-bwd z (j ∧ k)
                   ; (j = i1) → pred-suc (fwd-bwd z k) i })
          (fwd-predSuc (bwd z) i j)


ℤ≡BiInvℤ : ℤ ≡ BiInvℤ
ℤ≡BiInvℤ = isoToPath (iso fwd bwd fwd-bwd bwd-fwd)

discreteBiInvℤ : Discrete BiInvℤ
discreteBiInvℤ = subst Discrete ℤ≡BiInvℤ discreteℤ

isSetBiInvℤ : isSet BiInvℤ
isSetBiInvℤ = subst isSet ℤ≡BiInvℤ isSetℤ



-- suc' is equal to suc (suc≡suc') but cancels pred *exactly* (see suc'-pred)

suc'ᵖ : (z : BiInvℤ) -> Σ BiInvℤ (suc z ≡_)
suc' = fst ∘ suc'ᵖ
suc≡suc' = snd ∘ suc'ᵖ

suc'ᵖ zero = suc zero , refl
suc'ᵖ (suc z) = suc (suc z) , refl
suc'ᵖ (predr z) = z , suc-predr z
suc'ᵖ (suc-predr z i) = let filler : I → I → BiInvℤ
                            filler j i = hfill (λ j → λ { (i = i0) → suc (suc (predr z))
                                                        ; (i = i1) → suc≡suc' z j })
                                               (inS (suc (suc-predr z i))) j
                         in filler i1 i , λ j → filler j i
suc'ᵖ (predl z) = z , suc-predl z
suc'ᵖ (predl-suc z i) = let filler : I → I → BiInvℤ
                            filler j i = hfill (λ j → λ { (i = i0) → suc-predl (suc z) j
                                                        ; (i = i1) → suc≡suc' z j })
                                               (inS (suc (predl-suc z i))) j
                         in filler i1 i , λ j → filler j i

private
  suc'-pred : ∀ z → suc' (pred z) ≡ z
  suc'-pred z = refl


-- pred' is equal to pred (pred≡pred') but cancels suc *exactly* (see pred'-suc)

predr'ᵖ : (z : BiInvℤ) -> Σ BiInvℤ (predr z ≡_)
predr' = fst ∘ predr'ᵖ
predr≡predr' = snd ∘ predr'ᵖ

predr'ᵖ zero = predr zero , refl
predr'ᵖ (suc z) = z , predr-suc z
predr'ᵖ (predr z) = predr (predr z) , refl
predr'ᵖ (suc-predr z i) = let filler : I → I → BiInvℤ
                              filler j i = hfill (λ j → λ { (i = i0) → predr-suc (predr z) j
                                                          ; (i = i1) → predr≡predr' z j })
                                                 (inS (predr (suc-predr z i))) j
                           in filler i1 i , λ j → filler j i
predr'ᵖ (predl z) = predr (predl z) , refl
predr'ᵖ (predl-suc z i) = let filler : I → I → BiInvℤ
                              filler j i = hfill (λ j → λ { (i = i0) → predr (predl (suc z))
                                                          ; (i = i1) → predr≡predr' z j })
                                                 (inS (predr (predl-suc z i))) j
                           in filler i1 i , λ j → filler j i

predl'ᵖ : (z : BiInvℤ) -> Σ BiInvℤ (predl z ≡_)
predl' = fst ∘ predl'ᵖ
predl≡predl' = snd ∘ predl'ᵖ

predl'ᵖ zero = predl zero , refl
predl'ᵖ (suc z) = z , predl-suc z
predl'ᵖ (predr z) = predl (predr z) , refl
predl'ᵖ (suc-predr z i) = let filler : I → I → BiInvℤ
                              filler j i = hfill (λ j → λ { (i = i0) → predl-suc (predr z) j
                                                          ; (i = i1) → predl≡predl' z j })
                                                 (inS (predl (suc-predr z i))) j
                           in filler i1 i , λ j → filler j i
predl'ᵖ (predl z) = predl (predl z) , refl
predl'ᵖ (predl-suc z i) = let filler : I → I → BiInvℤ
                              filler j i = hfill (λ j → λ { (i = i0) → predl (predl (suc z))
                                                          ; (i = i1) → predl≡predl' z j })
                                                 (inS (predl (predl-suc z i))) j
                           in filler i1 i , λ j → filler j i

private
  predr'-suc : ∀ z → predr' (suc z) ≡ z
  predr'-suc z = refl

  predl'-suc : ∀ z → predl' (suc z) ≡ z
  predl'-suc z = refl
