module

public import RKCert.ReviewedNative.HankelLegendreIntData
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

/-! # Exact finite field receipts for the quartic Legendre join

All modes/tails below are interpreted from the literal integer data.
This module does not assert a global rational homomorphism or positivity
in K. `PaidLegendre28` isolates the still-to-prove field transport;
none of its fields asserts exclusion of a mask or profile. -/
namespace RKResearch.Certified.Graded.HankelQuarticLegendre

open Polynomial HankelLegendreIntData
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]

def intPoly (K : Type*) [Field K] : List ℤ → K[X]
  | [] => 0
  | a :: as => C (a : K) + X * intPoly K as

def rowPoly (K : Type*) [Field K] (s : ScaledRow) : K[X] :=
  C ((s.denominator : K)⁻¹) * intPoly K s.numerator

abbrev L (K : Type*) [Field K] (n : ℕ) : K[X] := rowPoly K (modeRow n)

abbrev T (K : Type*) [Field K] (a n : ℕ) : K[X] := rowPoly K (tailRow a n)

def beta (K : Type*) [Field K] (n : ℕ) : K :=
  ((n : K)^2) / ((((2*n-1 : ℕ) : K)) * (((2*n+1 : ℕ) : K)))

def reflect (K : Type*) [Field K] : K[X] →+* K[X] :=
  Polynomial.compRingHom (-(X : K[X]))

def deltaI (K : Type*) [Field K] : K := (601 : K)/1683

def deltaIII (K : Type*) [Field K] : K := (160 : K)/1071

/-- Fixed, small literal Legendre facts over the paid coefficient field.
The nonzero mode norms are only for n≤9. The signed rational
coefficients are explicit small identities after paid division, not
presumed obstructions. Modes/tails are exactly the definitions above. -/
structure PaidLegendre28 (I : K[X] →ₗ[K] K) : Prop where
  units : ∀ n : ℕ, 0 < n → n ≤ 20 → (n : K) ≠ 0
  modeMonic : ∀ n ≤ 10, (L K n).Monic
  modeDegree : ∀ n ≤ 10, (L K n).natDegree = n
  modeSilent : ∀ n ≤ 10, ∀ j < n, I (X^j * L K n) = 0
  modeNorm : ∀ n ≤ 9, I (X^n * L K n) ≠ 0
  modeEven : ∀ n ≤ 10, n % 2 = 0 → reflect K (L K n) = L K n
  modeOdd : ∀ n ≤ 10, n % 2 = 1 → reflect K (L K n) = -L K n
  tailMonic : ∀ a n, 5 ≤ a → a ≤ 7 → a+n ≤ 11 → (T K a n).Monic
  tailDegree : ∀ a n, 5 ≤ a → a ≤ 7 → a+n ≤ 11 → (T K a n).natDegree = n
  tailEven : ∀ a n, 5 ≤ a → a ≤ 7 → a+n ≤ 11 → n % 2 = 0 →
    reflect K (T K a n) = T K a n
  tailOdd : ∀ a n, 5 ≤ a → a ≤ 7 → a+n ≤ 11 → n % 2 = 1 →
    reflect K (T K a n) = -T K a n
  cop43 : IsCoprime (L K 4) (L K 3)
  cop54 : IsCoprime (L K 5) (L K 4)
  step84 : L K 8 = T K 5 4 * L K 4 - C (beta K 4)*T K 6 3*L K 3
  step94 : L K 9 = T K 5 5 * L K 4 - C (beta K 4)*T K 6 4*L K 3
  step104 : L K 10 = T K 5 6 * L K 4 - C (beta K 4)*T K 6 5*L K 3
  step95 : L K 9 = T K 6 4 * L K 5 - C (beta K 5)*T K 7 3*L K 4
  step105 : L K 10 = T K 6 5 * L K 5 - C (beta K 5)*T K 7 4*L K 4
  tail74 : T K 7 4 = X*T K 7 3 - C (beta K 9)*T K 7 2
  coeff55 : (T K 6 4 - L K 4).coeff 2 = (135 : K)/1309
  coeff45 : (T K 5 4 - L K 4).coeff 2 = (32 : K)/315
  cubicI : (X*T K 6 4 - L K 5).coeff 3 = deltaI K
  oddI : (X*T K 6 4 - C (deltaI K)*T K 7 3 - L K 5).coeff 1 = (6432 : K)/1446445
  evenI : (C (deltaI K + beta K 5)*(X*T K 7 3) - C (deltaI K)*T K 6 4 -
    C (beta K 5)*L K 4).coeff 2 = (33603 : K)/187187
  cubicII : (L K 5 - X*T K 7 4).coeff 3 = (-796 : K)/2223
  linearII : (L K 5 - X*T K 7 4).coeff 1 = (77192 : K)/440895
  cubicIII : (X*L K 4 - T K 5 5).coeff 3 = deltaIII K
  linearIII : (X*L K 4 - C (deltaIII K)*L K 3 - T K 5 5).coeff 1 = (-96 : K)/6545
  cubicIV : (T K 6 5 - X*L K 4).coeff 3 = (-216 : K)/1463

end
end RKResearch.Certified.Graded.HankelQuarticLegendre
