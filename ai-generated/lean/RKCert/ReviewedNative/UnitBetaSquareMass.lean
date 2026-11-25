module

public import RKCert.NodalPrimitive
public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Degree-unbounded formal square mass on the unit interval -/

namespace RKCert.ReviewedNative.UnitBetaSquareMass

open Polynomial RKCert.Endpoint

noncomputable section

variable {K : Type*} [Field K]

/-- The literal endpoint-power weight. -/
def betaWeight (a b : ℕ) : K[X] :=
  X ^ a * (1 - X) ^ b

/-- The positive diagonal multiplier in the shifted energy identity. -/
def slope (a b : ℕ) : K :=
  ((a : K) + 1) + ((b : K) + 1)

/-- Shifted Jacobi raising map, without normalization by the top coefficient. -/
def raise (a b : ℕ) : K[X] →ₗ[K] K[X] :=
  LinearMap.mulLeft K (C ((a : K) + 1) * (1 - X) - C ((b : K) + 1) * X) +
    (LinearMap.mulLeft K (X * (1 - X))).comp Polynomial.derivative

theorem raise_apply (a b : ℕ) (Q : K[X]) :
    raise a b Q =
      (C ((a : K) + 1) * (1 - X) - C ((b : K) + 1) * X) * Q +
        X * (1 - X) * Q.derivative := rfl

private theorem weight_derivative (a b : ℕ) :
    (betaWeight (K := K) (a+1) (b+1)).derivative =
      C ((a : K) + 1) * betaWeight a (b+1) -
        C ((b : K) + 1) * betaWeight (a+1) b := by
  rw [betaWeight, derivative_mul, derivative_X_pow_succ, derivative_pow_succ,
    derivative_sub, derivative_one, derivative_X]
  simp only [betaWeight, zero_sub]
  ring

/-- Raising is exactly weighted differentiation. -/
theorem derivative_weight_mul (a b : ℕ) (Q : K[X]) :
    (betaWeight (a+1) (b+1) * Q).derivative = betaWeight a b * raise a b Q := by
  rw [derivative_mul, weight_derivative, raise_apply]
  simp only [betaWeight, pow_succ]
  ring

/-- Differentiation commutes with the raising map up to its scalar diagonal. -/
theorem derivative_raise (a b : ℕ) (Q : K[X]) :
    (raise a b Q).derivative =
      -(C (slope a b) * Q) + raise (a+1) (b+1) Q.derivative := by
  simp only [raise_apply, derivative_add, derivative_sub, derivative_mul,
    derivative_C, derivative_one, derivative_X, zero_sub, zero_mul, zero_add,
    mul_zero, mul_one, one_mul, slope, Nat.cast_add, Nat.cast_one, C_add, C_1]
  ring

private theorem X_mul_derivative_power (n : ℕ) :
    (X : K[X]) * (X^n).derivative = C (n : K) * X^n := by
  cases n with
  | zero => simp
  | succ n =>
      change (X : K[X]) * (X^(n+1)).derivative = C ((n+1 : ℕ) : K) * X^(n+1)
      rw [derivative_X_pow_succ]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] <;> ring

theorem raise_power (a b n : ℕ) :
    raise a b (X^n : K[X]) =
      C (((a : K) + 1) + (n : K)) * X^n -
        C (slope a b + (n : K)) * X^(n+1) := by
  rw [raise_apply]
  have split : (X : K[X]) * (1-X) * (X^n).derivative =
      (1-X) * (X * (X^n).derivative) := by ring
  rw [split, X_mul_derivative_power]
  simp only [slope, C_add, C_1, pow_succ]
  ring

section Formal
variable [CharZero K]

/-- Algebraic, normalized unit mass; this is not an analytic integral. -/
def mass : K[X] →ₗ[K] K :=
  (Polynomial.leval (1 : K)).comp formalPrimitiveLinear

theorem mass_apply (P : K[X]) :
    mass P = (formalPrimitive P).eval 1 := rfl

theorem mass_derivative (P : K[X]) :
    mass P.derivative = P.eval 1 - P.eval 0 := by
  have prim : formalPrimitive P.derivative = P - C (P.eval 0) := by
    apply eq_of_derivative_and_eval_zero
    · simp only [derivative_formalPrimitive, derivative_sub, derivative_C, sub_zero]
    · simp
  rw [mass_apply, prim, eval_sub, eval_C]

theorem mass_C_mul (c : K) (P : K[X]) :
    mass (C c * P) = c * mass P := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (mass (K := K)).map_smul c P

private theorem mass_X_pow (a : ℕ) :
    mass (X^a : K[X]) = ((a : K) + 1)⁻¹ := by
  rw [mass_apply]
  have m : (X : K[X])^a = monomial a (1 : K) := by
    rw [← C_mul_X_pow_eq_monomial, C_1, one_mul]
  rw [m, formalPrimitive, support_monomial a (one_ne_zero : (1 : K) ≠ 0),
    Finset.sum_singleton, coeff_monomial_same, eval_monomial, one_pow, mul_one, one_div]

theorem mass_raise_zero (a b : ℕ) (Q : K[X]) :
    mass (betaWeight a b * raise a b Q) = 0 := by
  rw [← derivative_weight_mul, mass_derivative]
  simp [betaWeight, pow_succ]

theorem mass_pair_raise (a b : ℕ) (P Q : K[X]) :
    mass (betaWeight a b * raise a b P * Q) =
      -mass (betaWeight (a+1) (b+1) * P * Q.derivative) := by
  have dr : (betaWeight (a+1) (b+1) * P * Q).derivative =
      betaWeight a b * raise a b P * Q +
        betaWeight (a+1) (b+1) * P * Q.derivative := by
    rw [derivative_mul, derivative_weight_mul]
  have zero : mass (betaWeight a b * raise a b P * Q) +
      mass (betaWeight (a+1) (b+1) * P * Q.derivative) = 0 := by
    rw [← map_add, ← dr, mass_derivative]
    simp [betaWeight, pow_succ]
  calc
    _ = (mass (betaWeight a b * raise a b P * Q) +
          mass (betaWeight (a+1) (b+1) * P * Q.derivative)) -
        mass (betaWeight (a+1) (b+1) * P * Q.derivative) := by ring
    _ = _ := by rw [zero, zero_sub]

/-- A weighted exact energy identity, with no order or degree hypothesis. -/
theorem mass_raise_sq (a b : ℕ) (Q : K[X]) :
    mass (betaWeight a b * (raise a b Q)^2) =
      slope a b * mass (betaWeight (a+1) (b+1) * Q^2) +
        mass (betaWeight (a+1+1) (b+1+1) * Q.derivative^2) := by
  have fact : betaWeight (a+1) (b+1) * Q * (raise a b Q).derivative =
      -(C (slope a b) * (betaWeight (a+1) (b+1) * Q^2)) +
        betaWeight (a+1) (b+1) * raise (a+1) (b+1) Q.derivative * Q := by
    rw [derivative_raise]
    ring
  have sq : betaWeight (a+1+1) (b+1+1) * Q.derivative^2 =
      betaWeight (a+1+1) (b+1+1) * Q.derivative * Q.derivative := by ring
  calc
    _ = mass (betaWeight a b * raise a b Q * raise a b Q) := by congr 1 <;> ring
    _ = -mass (betaWeight (a+1) (b+1) * Q * (raise a b Q).derivative) :=
      mass_pair_raise a b Q (raise a b Q)
    _ = _ := by
      rw [fact, map_add, map_neg, mass_C_mul,
        mass_pair_raise (a+1) (b+1) Q.derivative Q, sq]
      ring

/-- Block decomposition of the unit Gram mass into a constant coordinate
and two lower-degree square masses. -/
theorem mass_constant_add_raise_sq (a b : ℕ) (c : K) (Q : K[X]) :
    mass (betaWeight a b * (C c + raise a b Q)^2) =
      c^2 * mass (betaWeight a b) +
        slope a b * mass (betaWeight (a+1) (b+1) * Q^2) +
        mass (betaWeight (a+1+1) (b+1+1) * Q.derivative^2) := by
  have split : betaWeight a b * (C c + raise a b Q)^2 =
      C (c^2) * betaWeight a b +
        C (c+c) * (betaWeight a b * raise a b Q) +
        betaWeight a b * (raise a b Q)^2 := by
    simp only [map_pow, C_add]
    ring
  have cross : mass (C (c+c) * (betaWeight a b * raise a b Q)) = 0 := by
    rw [mass_C_mul, mass_raise_zero, mul_zero]
  rw [split, map_add, map_add, mass_C_mul, cross, add_zero, mass_raise_sq]
  exact (add_assoc _ _ _).symm

private theorem mass_C_sq (a b : ℕ) (c : K) :
    mass (betaWeight a b * (C c)^2) = c^2 * mass (betaWeight a b) := by
  have step : betaWeight a b * (C c)^2 = C (c^2) * betaWeight a b := by
    simp only [map_pow, mul_comm]
  rw [step, mass_C_mul]

end Formal

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

private theorem nat_plus_one_pos (a : ℕ) : 0 < (a : K) + 1 :=
  add_pos_of_nonneg_of_pos (Nat.cast_nonneg a) zero_lt_one

theorem slope_pos (a b : ℕ) : 0 < (slope a b : K) :=
  add_pos (nat_plus_one_pos a) (nat_plus_one_pos b)

/-- Positive base masses, by a rational beta recurrence, not a quadrature rule. -/
theorem mass_beta_pos (a b : ℕ) : 0 < mass (betaWeight (K := K) a b) := by
  induction b generalizing a with
  | zero =>
      have e : betaWeight (K := K) a 0 = X^a := by simp [betaWeight]
      rw [e, mass_X_pow]
      exact inv_pos.mpr (nat_plus_one_pos a)
  | succ b ih =>
      have e : mass ((betaWeight (K := K) (a+1) (b+1)).derivative) = 0 := by
        rw [mass_derivative]
        simp [betaWeight, pow_succ]
      rw [weight_derivative, map_sub, mass_C_mul, mass_C_mul] at e
      have h : 0 < ((a : K) + 1) * mass (betaWeight a (b+1)) := by
        rw [sub_eq_zero.mp e]
        exact mul_pos (nat_plus_one_pos b) (ih (a+1))
      exact lt_of_not_ge fun bad =>
        (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (nat_plus_one_pos a).le bad)) h

private theorem eq_constant_of_natDegree_le_zero {P : K[X]} (h : P.natDegree ≤ 0) :
    P = C (P.coeff 0) :=
  eq_C_of_natDegree_eq_zero (p := P) (by omega)

/-- Triangular degree descent for the weighted raising map. The zero
polynomial is allowed and n=0 has a separate constant construction. -/
theorem exists_constant_add_raise (a b n : ℕ) (P : K[X]) (hp : P.natDegree ≤ n) :
    ∃ (c : K) (Q : K[X]), Q.natDegree ≤ n - 1 ∧ P = C c + raise a b Q := by
  induction n generalizing P with
  | zero =>
      refine ⟨P.coeff 0, 0, by simp, ?_⟩
      simpa only [map_zero, add_zero] using eq_constant_of_natDegree_le_zero hp
  | succ n ih =>
      let d : K := slope a b + (n : K)
      have dn : d ≠ 0 :=
        ne_of_gt (add_pos_of_pos_of_nonneg (slope_pos a b) (Nat.cast_nonneg n))
      let c : K := -(P.coeff (n+1) / d)
      let T : K[X] := raise a b (C c * X^n)
      have scale : raise a b (C c * X^n) = C c * raise a b (X^n) := by
        simpa only [smul_eq_C_mul] using (raise a b).map_smul c ((X : K[X])^n)
      have Teq : T = C c * (C (((a : K)+1) + (n : K)) * X^n -
          C d * X^(n+1)) := by
        dsimp only [T]
        rw [scale, raise_power]
      have hc : -(c*d) = P.coeff (n+1) := by
        dsimp only [c]
        rw [neg_mul, neg_neg, div_mul_cancel₀ _ dn]
      have top : T.coeff (n+1) = P.coeff (n+1) := by
        rw [Teq]
        have z : ((X : K[X])^n).coeff (n+1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X_pow]; omega)
        have o : ((X : K[X])^(n+1)).coeff (n+1) = 1 := by simp [coeff_X_pow]
        simp only [coeff_C_mul, coeff_sub, z, o, mul_zero, mul_one, zero_sub, mul_neg]
        exact hc
      have Td : T.natDegree ≤ n+1 := by
        rw [Teq]
        have lo : (C (((a : K)+1) + (n : K)) * X^n).natDegree ≤ n+1 :=
          (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
        have hi : (C d * X^(n+1)).natDegree ≤ n+1 :=
          (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow])
        apply (natDegree_C_mul_le _ _).trans
        simpa only [max_self] using natDegree_sub_le_of_le lo hi
      let S : K[X] := P - T
      have Sd : S.natDegree ≤ n := by
        apply natDegree_le_iff_coeff_eq_zero.mpr
        intro i hi
        change (P-T).coeff i = 0
        rw [coeff_sub]
        by_cases ei : i = n+1
        · subst i
          rw [top, sub_self]
        · have large : n+1 < i := by omega
          have pz : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt large)
          have tz : T.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (Td.trans_lt large)
          rw [pz, tz, sub_self]
      obtain ⟨e, Q, Qd, form⟩ := ih S Sd
      have dd : (Q + C c * X^n).natDegree ≤ n :=
        natDegree_add_le_of_degree_le (Qd.trans (Nat.sub_le _ _))
          ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]))
      refine ⟨e, Q + C c * X^n, by omega, ?_⟩
      rw [map_add]
      calc
        P = S + raise a b (C c * X^n) := by dsimp [S, T]; ring
        _ = C e + (raise a b Q + raise a b (C c * X^n)) := by rw [form]; ring

private theorem mass_C_sq_pos (a b : ℕ) {c : K} (hc : c ≠ 0) :
    0 < mass (betaWeight a b * (C c)^2) := by
  rw [mass_C_sq]
  exact mul_pos (by simpa only [pow_two] using (mul_self_pos.mpr hc)) (mass_beta_pos a b)

private theorem mass_beta_square_pos_of_degree (n : ℕ) :
    ∀ (a b : ℕ) {P : K[X]}, P.natDegree ≤ n → P ≠ 0 →
      0 < mass (betaWeight a b * P^2) := by
  induction n with
  | zero =>
      intro a b P d hP
      have form : P = C (P.coeff 0) := eq_constant_of_natDegree_le_zero d
      have hc : P.coeff 0 ≠ 0 := fun z => hP (by rw [form, z, C_0])
      rw [form]
      exact mass_C_sq_pos a b hc
  | succ n ih =>
      intro a b P d hP
      obtain ⟨c, Q, Qd, form⟩ := exists_constant_add_raise a b (n+1) P d
      by_cases hQ : Q = 0
      · have pc : P = C c := by simpa only [hQ, map_zero, add_zero] using form
        have hc : c ≠ 0 := fun z => hP (by rw [pc, z, C_0])
        rw [pc]
        exact mass_C_sq_pos a b hc
      · have smaller : Q.natDegree ≤ n := by omega
        have dq : Q.derivative.natDegree ≤ n :=
          (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans smaller)
        have nonnegD : 0 ≤ mass (betaWeight (a+1+1) (b+1+1) * Q.derivative^2) := by
          by_cases hd : Q.derivative = 0
          · simp [hd]
          · exact (ih (a+1+1) (b+1+1) dq hd).le
        have nonnegC : 0 ≤ c^2 * mass (betaWeight a b) :=
          mul_nonneg (sq_nonneg c) (mass_beta_pos a b).le
        have posQ : 0 < slope a b * mass (betaWeight (a+1) (b+1) * Q^2) :=
          mul_pos (slope_pos a b) (ih (a+1) (b+1) smaller hQ)
        rw [form, mass_constant_add_raise_sq]
        exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos nonnegC posQ) nonnegD

/-- Unit mass is strictly positive for a nonzero square with arbitrary
natural endpoint exponents, over any ordered field and at every degree. -/
theorem mass_beta_square_pos (a b : ℕ) {P : K[X]} (hP : P ≠ 0) :
    0 < mass (betaWeight a b * P^2) :=
  mass_beta_square_pos_of_degree P.natDegree a b le_rfl hP

theorem mass_beta_square_eq_zero_iff (a b : ℕ) (P : K[X]) :
    mass (betaWeight a b * P^2) = 0 ↔ P = 0 := by
  constructor
  · intro paid
    by_contra hP
    exact (ne_of_gt (mass_beta_square_pos a b hP)) paid
  · rintro rfl
    simp

theorem beta_square_pos (a b : ℕ) {P : K[X]} (hP : P ≠ 0) :
    0 < (formalPrimitive (X^a * (1-X)^b * P^2)).eval 1 :=
  mass_beta_square_pos a b hP

theorem square_pos {P : K[X]} (hP : P ≠ 0) :
    0 < (formalPrimitive (P^2)).eval 1 := by
  simpa using beta_square_pos 0 0 hP

theorem X_square_pos {P : K[X]} (hP : P ≠ 0) :
    0 < (formalPrimitive (X * P^2)).eval 1 := by
  simpa using beta_square_pos 1 0 hP

theorem X_one_sub_X_square_pos {P : K[X]} (hP : P ≠ 0) :
    0 < (formalPrimitive (X * (1-X) * P^2)).eval 1 := by
  simpa using beta_square_pos 1 1 hP

end Ordered
end
end RKCert.ReviewedNative.UnitBetaSquareMass
