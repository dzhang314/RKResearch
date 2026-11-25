module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCompact
public import RKCert.ReviewedNative.PolynomialCertificateAllWordMoments
public import RKCert.ReviewedNative.UnitBubbleMoments

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The genuine weighted source product is the degree-eight Jacobi pencil -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.JacobiSix
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.WeakFive16
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem integral_monomial_unit (i : ℕ) (a : K) :
    integral 0 1 (monomial i a) = a / ((i+1 : ℕ) : K) := by
  by_cases h : a = 0
  · simp [h, formalPrimitive]
  rw [integral_zero_left]
  simp [formalPrimitive, support_monomial i h]

/-- The two rational terms contributed by one coefficient in a paid test. -/
private theorem weighted_monomial (i k : ℕ) (a : K) :
    integral 0 1 (X * (1-X) * monomial i a * X^k) =
      a / ((i+k+2 : ℕ) : K) - a / ((i+k+3 : ℕ) : K) := by
  have expand : (X : K[X]) * (1-X) * monomial i a * X^k =
      monomial (i+k+1) a - monomial (i+k+2) a := by
    simp only [← C_mul_X_pow_eq_monomial, pow_add, pow_one, pow_two]
    ring
  rw [expand, map_sub, integral_monomial_unit, integral_monomial_unit]

private theorem weighted_vector_moment {n : ℕ} (a : Fin n → K) (k : ℕ) :
    integral 0 1 (X * (1-X) * ofFn n a * X^k) =
      ∑ i : Fin n, (a i / ((i.val+k+2 : ℕ) : K) -
        a i / ((i.val+k+3 : ℕ) : K)) := by
  rw [ofFn_eq_sum_monomial, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact weighted_monomial i.val k (a i)

private theorem orthogonal_of_powers {Q : K[X]}
    (h : ∀ k : Fin 6, integral 0 1 (X * (1-X) * Q * X^k.val) = 0) :
    OrthogonalSix Q := by
  intro R hr
  let L : K[X] →ₗ[K] K :=
    (integral 0 1).comp (LinearMap.mulLeft K (X * (1-X) * Q))
  change L R = 0
  rw [R.as_sum_range' 6 (by omega), map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have z : L (X^i) = 0 := h ⟨i, Finset.mem_range.mp hi⟩
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, z, smul_zero]


/-- The extra power is a proved reference-Jacobi identity, not a seventh
global law for the source polynomial. -/
theorem XJ7_orthogonal : OrthogonalSix (X * J7 K) := by
  apply orthogonal_of_powers
  intro k
  have alg : (X : K[X])*(1-X)*(X*J7 K)*X^k.val = X*(1-X)*J7 K*X^(k.val+1) := by
    rw [pow_succ]
    ring
  have hJ : J7 K = ofFn 8 (a7 K) := by
    simp only [J7, ofFn_eq_sum_monomial]
  rw [alg, hJ]
  calc
    _ = ∑ i : Fin 8, (a7 K i / ((i.val + (k.val + 1) + 2 : ℕ) : K) -
        a7 K i / ((i.val + (k.val + 1) + 3 : ℕ) : K)) :=
      weighted_vector_moment (a7 K) (k.val + 1)
    _ = 0 := by fin_cases k <;> norm_num [Fin.sum_univ_succ, a7]

/-- Every monic degree-eight polynomial satisfying the actual six
weighted conditions has this pencil form, without assuming its coefficients. -/
theorem monic_eight_pencil {T : K[X]} (mon : T.Monic) (deg : T.natDegree = 8)
    (orth : OrthogonalSix T) : ∃ d κ : K, T = unitPencil d κ := by
  let E := T - X * J7 K
  let a := E.coeff 7
  let b := E.coeff 6 - a * (J7 K).coeff 6
  let D := E - C a * J7 K - C b * J6 K
  have E7 : E.natDegree ≤ 7 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h8 : i = 8
    · subst i
      have t8 : T.coeff 8 = 1 := by rw [← deg, coeff_natDegree, mon.leadingCoeff]
      have x8 : (X * J7 K).coeff 8 = 1 := (coeff_X_mul (J7 K) 7).trans (J7_coeff_top K)
      simp only [E, coeff_sub, x8, t8, sub_self]
    · have zt : T.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have zj : (X * J7 K).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_X_mul (J7_monic K).ne_zero, J7_natDegree]; omega)
      simp only [E, coeff_sub, zt, zj, sub_zero]
  have dD : D.natDegree ≤ 5 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rcases (show i = 6 ∨ i = 7 ∨ 7 < i by omega) with e | e | big
    · subst i
      simp only [D, coeff_sub, coeff_C_mul, J6_coeff_top, mul_one, b, sub_self]
    · subst i
      have z6 : (J6 K).coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (by rw [J6_natDegree]; decide)
      simp only [D, coeff_sub, coeff_C_mul, J7_coeff_top, z6, mul_one, mul_zero, sub_zero, a, sub_self]
    · have zE : E.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (E7.trans_lt big)
      have z6 : (J6 K).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by rw [J6_natDegree]; omega)
      have z7 : (J7 K).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by rw [J7_natDegree]; omega)
      simp only [D, coeff_sub, coeff_C_mul, zE, z6, z7, mul_zero, sub_zero]
  have orthoD : OrthogonalSix D := by
    intro H hd
    have alg : X*(1-X)*D*H =
        (X*(1-X)*T*H) - (X*(1-X)*(X*J7 K)*H) -
          a • (X*(1-X)*J7 K*H) - b • (X*(1-X)*J6 K*H) := by
      simp only [D, E, smul_eq_C_mul]
      ring
    rw [alg]
    simp only [map_sub, map_smul, orth H hd, XJ7_orthogonal H hd, J7_orthogonal H hd,
      J6_orthogonal H hd, smul_zero, sub_zero]
  have zero : D = 0 := RKCert.ReviewedNative.UnitBubbleMoments.zero_of_orthogonalThrough orthoD dD (by decide)
  refine ⟨-a, -b, ?_⟩
  calc T = D + unitPencil (-a) (-b) := by simp only [D, E, unitPencil, map_neg]; ring
       _ = unitPencil (-a) (-b) := by rw [zero, zero_add]

theorem source_product_bound {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    q * nodalTail c Z ≠ 0 ∧ (q * nodalTail c Z).natDegree ≤ 8 := by
  rw [nodalTail, M.middleFactor]
  exact ⟨mul_ne_zero M.qNonzero (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
      (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))),
    natDegree_mul_le_of_le M.qDegree (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le)
      (natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le))⟩

theorem raw_eight_site_pencil {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    {β : Fin 8 → K} (inj : Function.Injective β)
    (roots : ∀ i, (q * nodalTail c Z).IsRoot (β i)) :
    ∃ d κ : K, ∀ i, (unitPencil d κ).IsRoot (β i) := by
  classical
  let N := q * nodalTail c Z
  let T := Lagrange.nodal Finset.univ β
  have hmon : T.Monic := Lagrange.nodal_monic
  have hdeg : T.natDegree = 8 := by simp [T, Lagrange.natDegree_nodal]
  obtain ⟨nz, bound⟩ := source_product_bound M
  have dN : N.natDegree = 8 := by
    apply le_antisymm bound
    by_contra! below
    apply nz
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ inj.injOn
    · rw [degree_eq_natDegree nz, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast below
    · exact fun i _ => roots i
  have lc : N.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr nz
  have deg : N.degree = (Finset.univ : Finset (Fin 8)).card := by
    rw [degree_eq_natDegree nz, dN]; simp
  have fac : N = C N.leadingCoeff * T := by
    apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ inj.injOn deg.le
    · have hR : (C N.leadingCoeff * T).degree = T.degree := by
        rw [degree_mul, degree_C lc, zero_add]
      exact deg.trans (hR.trans Lagrange.degree_nodal).symm
    · simp [leadingCoeff_mul, hmon.leadingCoeff]
    · intro i hi
      have hR : (C N.leadingCoeff * T).eval (β i) = 0 := by
        rw [eval_mul, show T.eval (β i) = 0 from Lagrange.eval_nodal_at_node hi, mul_zero]
      rw [hR]
      exact roots i
  have orth : OrthogonalSix T := by
    intro H hd
    have paid := M.weightedMoments H hd
    have alg : X*(1-X)*N*H = N.leadingCoeff • (X*(1-X)*T*H) := by
      calc X*(1-X)*N*H = X*(1-X)*(C N.leadingCoeff*T)*H := congrArg (fun R => X*(1-X)*R*H) fac
           _ = _ := by rw [smul_eq_C_mul]; ring
    change integral 0 1 (X*(1-X)*N*H) = 0 at paid
    rw [alg, map_smul, smul_eq_mul] at paid
    exact (mul_eq_zero.mp paid).resolve_left lc
  obtain ⟨d, κ, heq⟩ := monic_eight_pencil hmon hdeg orth
  refine ⟨d, κ, fun i => ?_⟩
  rw [← heq]
  exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
