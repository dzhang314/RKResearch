module

public import RKCert.ReviewedNative.TallPoleMultiplierProducer

import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The derivative-gcd quotient counts distinct roots in a splitting field

This file uses only polynomial APIs. Splitting is an explicit premise on
the mapped polynomial, never a premise on the coefficient field. -/

namespace RKResearch.Certified.TallFiniteResponse

open Polynomial
open scoped Polynomial

noncomputable section

variable {K L : Type*} [Field K] [Field L]

/-- The ordinary Euclidean gcd and degree commute with passing to a
field extension, including in positive characteristic. -/
theorem derivativeGcdQuotientDegree_map (Q : K[X]) (φ : K →+* L) :
    derivativeGcdQuotientDegree (Q.map φ) = derivativeGcdQuotientDegree Q := by
  classical
  simp only [derivativeGcdQuotientDegree, Polynomial.derivative_map,
    Polynomial.gcd_map, Polynomial.natDegree_map]

open scoped Classical in
/-- Over a field in which the nonzero polynomial splits, the degree
difference is the cardinality of its distinct roots. -/
theorem derivativeGcdQuotientDegree_eq_card_toFinset_of_splits [CharZero K]
    (Q : K[X]) (hQ : Q ≠ 0) (hs : Q.Splits) :
    derivativeGcdQuotientDegree Q = Q.roots.toFinset.card := by
  classical
  let G := EuclideanDomain.gcd Q Q.derivative
  have hGdvd : G ∣ Q := EuclideanDomain.gcd_dvd_left Q Q.derivative
  obtain ⟨V, hq⟩ := hGdvd
  have hp : G * V ≠ 0 := fun hz => hQ (hq.trans hz)
  obtain ⟨hG, hV⟩ := mul_ne_zero_iff.mp hp
  have hVdvd : V ∣ Q := ⟨G, hq.trans (mul_comm G V)⟩
  have hVs : V.Splits := hs.of_dvd hQ hVdvd
  have hgd : G ∣ Q.derivative := EuclideanDomain.gcd_dvd_right Q Q.derivative
  have hroots : V.roots = Q.roots.dedup := by
    apply Multiset.ext'
    intro a
    rw [Polynomial.count_roots, Multiset.count_dedup]
    have hmul : Q.rootMultiplicity a = G.rootMultiplicity a + V.rootMultiplicity a := by
      exact (congrArg (fun f : K[X] => f.rootMultiplicity a) hq).trans
        (Polynomial.rootMultiplicity_mul hp)
    by_cases ha : a ∈ Q.roots
    · have haRoot : Q.IsRoot a := (Polynomial.mem_roots hQ).mp ha
      have haPos : 0 < Q.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hQ).mpr haRoot
      have hD : Q.derivative ≠ 0 := by
        intro hz
        have hC : Q = C (Q.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hz
        have hc : Q.coeff 0 ≠ 0 := by
          intro he
          exact hQ (hC.trans (by rw [he, map_zero]))
        have haC : (C (Q.coeff 0) : K[X]).IsRoot a := by rwa [← hC]
        exact Polynomial.not_isRoot_C _ _ hc haC
      have hUpper := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hD hgd a
      rw [Polynomial.derivative_rootMultiplicity_of_root haRoot] at hUpper
      have hPowQ : (X - C a : K[X]) ^ (Q.rootMultiplicity a - 1) ∣ Q :=
        (Polynomial.le_rootMultiplicity_iff hQ (a := a) (n := Q.rootMultiplicity a - 1)).mp
          (Nat.sub_le _ _)
      have hPowD : (X - C a : K[X]) ^ (Q.rootMultiplicity a - 1) ∣ Q.derivative :=
        Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (Polynomial.pow_rootMultiplicity_dvd Q a)
      have hLower : Q.rootMultiplicity a - 1 ≤ G.rootMultiplicity a :=
        (Polynomial.le_rootMultiplicity_iff hG (a := a) (n := Q.rootMultiplicity a - 1)).mpr
          (EuclideanDomain.dvd_gcd hPowQ hPowD)
      rw [if_pos ha]
      omega
    · have hNotRoot : ¬ Q.IsRoot a := fun hr => ha ((Polynomial.mem_roots hQ).mpr hr)
      have hzero : Q.rootMultiplicity a = 0 := Polynomial.rootMultiplicity_eq_zero hNotRoot
      rw [if_neg ha]
      omega
  calc
    derivativeGcdQuotientDegree Q = V.natDegree := by
      change Q.natDegree - G.natDegree = V.natDegree
      rw [hq, Polynomial.natDegree_mul hG hV]
      omega
    _ = V.roots.card := hVs.natDegree_eq_card_roots
    _ = Q.roots.dedup.card := congrArg Multiset.card hroots
    _ = Q.roots.toFinset.card := (Multiset.card_toFinset _).symm

/-- Count distinct roots in any extension in which the polynomial
splits. Characteristic zero is needed in that extension. -/
theorem derivativeGcdQuotientDegree_eq_ncard_rootSet_of_splits [Algebra K L] [CharZero L]
    (Q : K[X]) (hQ : Q ≠ 0) (hs : (Q.map (algebraMap K L)).Splits) :
    derivativeGcdQuotientDegree Q = (Q.rootSet L).ncard := by
  classical
  let φ : K →+* L := algebraMap K L
  calc
    derivativeGcdQuotientDegree Q = derivativeGcdQuotientDegree (Q.map φ) :=
      (derivativeGcdQuotientDegree_map Q φ).symm
    _ = (Q.map φ).roots.toFinset.card :=
      derivativeGcdQuotientDegree_eq_card_toFinset_of_splits (Q.map φ)
        (Polynomial.map_ne_zero hQ) hs
    _ = (Q.rootSet L).ncard := by
      simp only [Polynomial.rootSet_def, Set.ncard_coe_finset, Polynomial.aroots_def, φ]

end
end RKResearch.Certified.TallFiniteResponse
