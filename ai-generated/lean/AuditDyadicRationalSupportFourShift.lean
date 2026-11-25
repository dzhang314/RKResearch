module

import RKCert.ReviewedNative.DyadicRationalSupportFourShift

open Polynomial RKResearch RKResearch.Certified.RationalPrimeCut
open RKResearch.Certified.DyadicFourShift
open scoped Polynomial Matrix

#check (integralNodal_dyadicCredit_dvd :
  ∀ (T : Finset ℚ) (k : ℕ),
    (2 : ℤ)^(dyadicCredit (dyadicDenCount T) (dyadicEvenCount T) k) ∣
      (integralRationalNodalHull T).coeff k)

#check (integralNodal_coeff_two :
  ∀ (T : Finset ℚ) (k : ℕ),
    ((integralRationalNodalHull T).coeff k : ZMod 2) =
      (dyadicParity (dyadicDenCount T) (dyadicEvenCount T) k : ZMod 2))

#check (dyadicFourRows8_of_uniformInt :
  ∀ (a : ℕ → ℤ) {m : ℕ}, m ≤ 16 → (∀ k, m < k → a k = 0) →
    (∀ j : Fin 4, UniformIntRowZero a m j.val) → DyadicFourRows8 a)

#check (dyadicParityGate_exact :
  ∀ t u : Fin 17, DyadicParityGate t.val u.val ↔ (t.val,u.val) ∈ dyadicSurvivingPairs)

#check (dyadicBalanced_coeffs_ne_zero :
  ∀ (T : Finset ℚ), T.card ≤ 16 → dyadicDenCount T = 16 → dyadicEvenCount T = 8 →
    ¬ (((integralRationalNodalHull T).coeff 12 : ZMod 4) = 0 ∧
       ((integralRationalNodalHull T).coeff 14 : ZMod 4) = 0))

#check (HasQuadratureOrder.no_dyadic_four_shift_support_of_rat :
  ∀ {ι K : Type} [Fintype ι] [Field K] [CharZero K] {p : ℕ} {b c : ι → K},
    HasQuadratureOrder p b c →
    (activeQuadratureSites b c).card ≤ 16 →
    (activeQuadratureSites b c).card + 4 ≤ p →
    (∀ x ∈ activeQuadratureSites b c, ∃ r : ℚ, x = (r : K)) → False)

#check (HasOrder.min17_sub3_le_activeQuadratureSites_of_rat :
  ∀ {ι K : Type} [Fintype ι] [Field K] [CharZero K] {p : ℕ}
    {b : ι → K} {A : Matrix ι ι K},
    HasOrder p A b → (∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) →
    min 17 (p-3) ≤ (activeQuadratureSites b (A *ᵥ 1)).card)

#check (HasOrder.sub3_le_activeQuadratureSites_of_rat_of_le20 :
  ∀ {ι K : Type} [Fintype ι] [Field K] [CharZero K] {p : ℕ}
    {b : ι → K} {A : Matrix ι ι K},
    HasOrder p A b → p ≤ 20 →
    (∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) →
    p-3 ≤ (activeQuadratureSites b (A *ᵥ 1)).card)

#check (HasOrder.seventeen_le_activeQuadratureSites_of_rat_order20 :
  ∀ {ι K : Type} [Fintype ι] [Field K] [CharZero K]
    {b : ι → K} {A : Matrix ι ι K},
    HasOrder 20 A b → (∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) →
    17 ≤ (activeQuadratureSites b (A *ᵥ 1)).card)

#print axioms integralNodal_dyadicCredit_dvd
#print axioms integralNodal_coeff_two
#print axioms dyadicCounts_reflect
#print axioms dyadicFourRows8_of_uniformInt
#print axioms dyadicParityGate_exact
#print axioms dyadicOneTerm_excludes_paid
#print axioms dyadicBalanced_coeffs_ne_zero
#print axioms HasQuadratureOrder.no_dyadic_four_shift_support_of_rat
#print axioms HasOrder.min17_sub3_le_activeQuadratureSites_of_rat
#print axioms HasOrder.seventeen_le_activeQuadratureSites_of_rat_order20
