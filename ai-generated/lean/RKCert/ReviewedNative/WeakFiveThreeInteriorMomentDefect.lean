module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorSevenRule
public import Mathlib.Algebra.Polynomial.Degree.Operations

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact monomial moments and the single unpaid top coefficient

This is the algebraic portion of the published pencil: the Gram form is
fully paid, and the x-multiplication form misses just its (6,6) entry.
The latter is not assumed to vanish.
-/

namespace RKCert.ReviewedNative.FiniteGaussianNodalLift

open Polynomial
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K]

def indexedAtomicMoment {ι : Type*} (t : Finset ι) (v μ : ι → K) : K[X] →ₗ[K] K :=
  ∑ i ∈ t, μ i • Polynomial.leval (v i)

theorem indexedAtomicMoment_apply {ι : Type*} (t : Finset ι) (v μ : ι → K) (P : K[X]) :
    indexedAtomicMoment t v μ P = ∑ i ∈ t, μ i * P.eval (v i) := by
  simp [indexedAtomicMoment, LinearMap.sum_apply, smul_eq_mul]

/-- A linear functional that vanishes through D only sees the top
coefficient of a degree-at-most-(D+1) test. -/
theorem linear_eq_of_top_defect (E : K[X] →ₗ[K] K) {D : ℕ} (P : K[X])
    (pd : P.natDegree ≤ D+1) (paid : ∀ Q : K[X], Q.natDegree ≤ D → E Q = 0) :
    E P = P.coeff (D+1) * E (X^(D+1)) := by
  calc
    E P = ∑ i ∈ Finset.range (D+2), P.coeff i * E (X^i) := by
      have brief : P.natDegree < D+2 := by omega
      conv_lhs => rw [P.as_sum_range_C_mul_X_pow' brief]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
    _ = P.coeff (D+1) * E (X^(D+1)) := by
      rw [show D+2 = (D+1)+1 by omega, Finset.sum_range_succ]
      have low : (∑ i ∈ Finset.range (D+1), P.coeff i * E (X^i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have qd : ((X : K[X])^i).natDegree ≤ D := by
          rw [natDegree_X_pow]
          exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [paid _ qd, mul_zero]
      rw [low, zero_add]

private theorem coeff_mul_at_cutoff (P Q : K[X]) {a b : ℕ}
    (pd : P.natDegree ≤ a) (qd : Q.natDegree ≤ b) :
    (P*Q).coeff (a+b) = P.coeff a * Q.coeff b := by
  have prod : (P*Q).natDegree ≤ P.natDegree+Q.natDegree := natDegree_mul_le
  by_cases p : P.natDegree = a
  · by_cases q : Q.natDegree = b
    · rw [← p, ← q, coeff_mul_degree_add_degree, coeff_natDegree, coeff_natDegree]
    · have dq : Q.natDegree < b := lt_of_le_of_ne qd q
      have d : (P*Q).natDegree < a+b := by omega
      rw [coeff_eq_zero_of_natDegree_lt d, coeff_eq_zero_of_natDegree_lt dq, mul_zero]
  · have dp : P.natDegree < a := lt_of_le_of_ne pd p
    have d : (P*Q).natDegree < a+b := by omega
    rw [coeff_eq_zero_of_natDegree_lt d, coeff_eq_zero_of_natDegree_lt dp, zero_mul]

/-- The bilinear Gram law is exact through degree 12. The only correction
for multiplication by x is the true, signed degree-13 defect. -/
theorem exact12_pair_and_border {ι : Type*} {J : K[X] →ₗ[K] K}
    {t : Finset ι} {v μ : ι → K} (law : ExactRule J t v μ 12) :
    let atom := indexedAtomicMoment t v μ
    let δ := atom (X^13) - J (X^13)
    ∀ P Q : K[X], P.natDegree ≤ 6 → Q.natDegree ≤ 6 →
      atom (P*Q) = J (P*Q) ∧
      atom (X*(P*Q)) = J (X*(P*Q)) + δ*(P.coeff 6*Q.coeff 6) := by
  dsimp only
  intro P Q pd qd
  let atom := indexedAtomicMoment t v μ
  let E : K[X] →ₗ[K] K := atom-J
  have paid (R : K[X]) (rd : R.natDegree ≤ 12) : E R = 0 := by
    change atom R-J R = 0
    rw [indexedAtomicMoment_apply, ← law R rd, sub_self]
  have pq : (P*Q).natDegree ≤ 12 := natDegree_mul_le_of_le pd qd
  refine ⟨by rw [indexedAtomicMoment_apply, law _ pq], ?_⟩
  have xpq : (X*(P*Q)).natDegree ≤ 13 := natDegree_mul_le_of_le natDegree_X.le pq
  have h := linear_eq_of_top_defect E (D := 12) _ xpq paid
  have cv : (X*(P*Q)).coeff 13 = P.coeff 6*Q.coeff 6 := by
    rw [show 13 = 12+1 by decide, coeff_X_mul]
    exact coeff_mul_at_cutoff P Q pd qd
  change atom (X*(P*Q)) - J (X*(P*Q)) =
    (X*(P*Q)).coeff 13 * (atom (X^13)-J (X^13)) at h
  rw [cv] at h
  calc
    atom (X*(P*Q)) = J (X*(P*Q)) + (atom (X*(P*Q))-J (X*(P*Q))) := by ring
    _ = _ := by rw [h]; ring

end
end RKCert.ReviewedNative.FiniteGaussianNodalLift

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open scoped Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem unit_integral_pow (n : ℕ) :
    integral (0:K) 1 (X^n) = ((n:K)+1)⁻¹ := by
  have nz : (n:K)+1 ≠ 0 := (show 0 < (n:K)+1 by positivity).ne'
  have repr : formalPrimitive (X^n : K[X]) = C ((n:K)+1)⁻¹ * X^(n+1) := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive, derivative_C_mul, derivative_X_pow_succ, ← mul_assoc,
        ← C_mul, inv_mul_cancel₀ nz, C_1, one_mul]
    · simp
  rw [integral_zero_left, repr]
  simp

def threeInteriorBaseMoment (j : ℕ) : K := 1 / (((j:K)+2)*((j:K)+3))

private theorem unit_weight_monomial (n : ℕ) :
    integral (0:K) 1 (X*(1-X)*X^n) = threeInteriorBaseMoment n := by
  have repr : (X:K[X])*(1-X)*X^n = X^(n+1)-X^(n+2) := by
    simp only [pow_succ]
    ring
  rw [repr, map_sub, unit_integral_pow, unit_integral_pow]
  have n₂ : (n:K)+2 ≠ 0 := (show 0 < (n:K)+2 by positivity).ne'
  have n₃ : (n:K)+3 ≠ 0 := (show 0 < (n:K)+3 by positivity).ne'
  have t₂ : ((n+1:ℕ):K)+1 = (n:K)+2 := by simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] <;> ring
  have t₃ : ((n+2:ℕ):K)+1 = (n:K)+3 := by simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] <;> ring
  rw [t₂, t₃, threeInteriorBaseMoment]
  field_simp [n₂,n₃] <;> ring

def threeInteriorScaledMoment (s : K) : K[X] →ₗ[K] K :=
  (12252240 : K) • threeInteriorMoment s

/-- Literal integer-clearing convention used by the two published
bivariate determinant templates. -/
theorem threeInteriorScaledMoment_monomial (s : K) (j : ℕ) :
    threeInteriorScaledMoment s (X^j) =
      12252240 * (threeInteriorBaseMoment (j+1) +
        s*(threeInteriorBaseMoment j-threeInteriorBaseMoment (j+1))) := by
  change 12252240 * integral 0 1 (threeInteriorDensity s*X^j) = _
  have repr :
      threeInteriorDensity s*X^j =
        C s*(X*(1-X)*X^j)+C (1-s)*(X*(1-X)*X^(j+1)) := by
    unfold threeInteriorDensity threeInteriorResidual
    rw [pow_succ]
    ring
  rw [repr, map_add, threeInterior_integral_C_mul, threeInterior_integral_C_mul,
    unit_weight_monomial, unit_weight_monomial]
  ring

theorem ThreeInteriorNormalized.scaled_seven_rule {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) :
    ∃ ω : ThreeInteriorSite → K, (∀ i, 0 < ω i) ∧
      ExactRule (threeInteriorScaledMoment s) Finset.univ (threeInteriorSites r m) ω 12 := by
  obtain ⟨μ, μpos, law⟩ := H.seven_rule
  refine ⟨fun i => 12252240*μ i, fun i => mul_pos (by positivity) (μpos i), ?_⟩
  intro P pd
  change 12252240*threeInteriorMoment s P = _
  rw [law P pd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
