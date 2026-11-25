module

public import RKCert.ReviewedNative.WeakFiveLocalVariation
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveReflectedMoments

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Primitive-square balance, including any reflected-origin seam -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.FiniteOrderedSigns
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def rawFourHull (u a h z : K) : K[X] :=
  (X-C u)*(X-C z)*((X-C a)*(X-C h))

def PaidSix (q : K[X]) (u a h z : K) : Prop :=
  ∀ R : K[X], R.natDegree ≤ 5 → integral 0 1 (X*(1-X)*(q*rawFourHull u a h z)*R) = 0

/-- The exact balance of three strictly positive square integrals. Its
premises contain no off-root condition at the origin or at one. -/
theorem primitive_square_balance {q : K[X]} {u a h z : K}
    (qn : q ≠ 0) (qd : q.natDegree ≤ 4) (un : u ≠ 0) (an : a ≠ 0) (au : a ≠ u)
    (lPaid : integral 0 u (X*(X-C u)*q) = 0)
    (aPaid : integral 0 a (X*(X-C u)*q) = 0)
    (g : PaidSix q u a h z) :
    ∃ A B D : K, 0 < A ∧ 0 < B ∧ 0 < D ∧ u*A = z*h*B + (u-1)*(u-z)*(u-h)*D := by
  let L : K[X] := X * (X - C u)
  let P : K[X] := (X - 1) * (X - C z) * (X - C h)
  let F := formalPrimitive (L * q)
  have f0 : F.eval 0 = 0 := formalPrimitive_eval_zero _
  have fprime : F.derivative = L * q := derivative_formalPrimitive _
  have ln : L ≠ 0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  have fn : F ≠ 0 := by
    intro zero
    rw [zero, derivative_zero] at fprime
    exact (mul_ne_zero ln qn) fprime.symm
  have fu : F.eval u = 0 := by
    have eq := lPaid
    rw [integral_zero_left] at eq
    exact eq
  have fa : F.eval a = 0 := by
    have eq := aPaid
    rw [integral_zero_left] at eq
    exact eq
  obtain ⟨J, Jrep⟩ := dvd_iff_isRoot.mpr (show F.IsRoot 0 from f0)
  have fJ : F = X * J := by simpa only [map_zero, sub_zero] using Jrep
  have Ju : J.eval u = 0 := by
    rw [fJ, eval_mul, eval_X] at fu
    exact (mul_eq_zero.mp fu).resolve_left un
  obtain ⟨V, Vrep⟩ := dvd_iff_isRoot.mpr (show J.IsRoot u from Ju)
  have fV : F = L * V := by rw [fJ, Vrep]; dsimp only [L]; ring
  have vn : V ≠ 0 := fun e => fn (by rw [fV, e, mul_zero])
  have Lna : L.eval a ≠ 0 := by
    simp only [L, eval_mul, eval_X, eval_sub, eval_C]
    exact mul_ne_zero an (sub_ne_zero.mpr au)
  have Va : V.eval a = 0 := by
    rw [fV, eval_mul] at fa
    exact (mul_eq_zero.mp fa).resolve_left Lna
  obtain ⟨B, Brep⟩ := dvd_iff_isRoot.mpr (show V.IsRoot a from Va)
  have bn : B ≠ 0 := fun e => vn (by rw [Brep, e, mul_zero])
  have ld : L.natDegree = 2 := by
    dsimp only [L]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero u), natDegree_X, natDegree_X_sub_C]
  have raw : (L * q).natDegree ≤ 6 := natDegree_mul_le_of_le ld.le qd
  have fd : F.natDegree ≤ 7 :=
    (natDegree_formalPrimitive_le (L * q)).trans (Nat.add_le_add_right raw 1)
  have vd : V.natDegree ≤ 5 := by
    rw [fV, natDegree_mul ln vn, ld] at fd
    omega
  have bd : B.natDegree ≤ 4 := by
    have e := vd
    rw [Brep, natDegree_mul (X_sub_C_ne_zero a) bn, natDegree_X_sub_C] at e
    omega
  have identity : (X * (1 - X)) * (q * rawFourHull u a h z) * B =
      -(P * V * F.derivative) := by
    rw [fprime, Brep]
    dsimp only [P, L, rawFourHull]
    ring
  have paid := g B (bd.trans (by decide : 4 ≤ 5))
  rw [identity, map_neg, neg_eq_zero] at paid
  let T := (P.derivative * L - P * L.derivative) * V^2
  let H := P * L * V^2
  have deriv : H.derivative = T + C (2 : K) * (P * V * F.derivative) := by
    rw [fV]
    dsimp only [H, T]
    simp only [derivative_mul, derivative_sq, map_ofNat]
    ring
  have hz : integral 0 1 H.derivative = 0 := by
    have e : formalPrimitive H.derivative = H - C (H.eval 0) := by
      apply eq_of_derivative_and_eval_zero
      · simp [derivative_sub]
      · simp
    rw [integral_apply, e]
    simp [H, P, L]
  rw [deriv, map_add, integral_C_mul, paid, mul_zero, add_zero] at hz
  let J₀ : K[X] := C u * L^2 - C (z * h) * (X - C u)^2 -
    C ((u - 1) * (u - z) * (u - h)) * X^2
  have shape : C u * T = J₀ * V^2 := by
    dsimp only [T, J₀, P, L]
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, derivative_one,
      sub_zero, one_mul, mul_one, map_mul, map_sub, map_one]
    ring
  have zero : integral 0 1 (J₀ * V^2) = 0 := by
    rw [← shape, integral_C_mul, hz, mul_zero]
  let A := integral 0 1 (L^2*V^2)
  let B₀ := integral 0 1 ((X-C u)^2*V^2)
  let D₀ := integral 0 1 (X^2*V^2)
  have squares (B : K[X]) (bn : B ≠ 0) (bd : B.natDegree ≤ 2) :
      0 < integral 0 1 (B^2*V^2) := by
    have prod : B*V ≠ 0 := mul_ne_zero bn vn
    have pd : (B*V).natDegree ≤ 7 := natDegree_mul_le_of_le bd vd
    obtain ⟨i, ni⟩ := exists_nonzero_grid_sample zero_lt_one prod (pd.trans_lt (by decide))
    rw [← mul_pow]
    apply integral_pos_of_grid_samples zero_lt_one ((natDegree_pow_le_of_le 2 pd).trans (by decide))
    · intro j
      rw [eval_pow]
      exact sq_nonneg _
    · refine ⟨i, ?_⟩
      rw [eval_pow]
      exact sq_pos_of_ne_zero ni
  have sum : u*A = z*h*B₀ + ((u-1)*(u-z)*(u-h))*D₀ := by
    have alg : J₀*V^2 = C u*(L^2*V^2) - C (z*h)*((X-C u)^2*V^2)
        - C ((u-1)*(u-z)*(u-h))*(X^2*V^2) := by
      dsimp only [J₀]
      ring
    rw [alg, map_sub, map_sub, integral_C_mul, integral_C_mul, integral_C_mul] at zero
    change u*A - z*h*B₀ - ((u-1)*(u-z)*(u-h))*D₀ = 0 at zero
    linarith only [zero]
  exact ⟨A, B₀, D₀, squares L ln ld.le, squares (X-C u) (X_sub_C_ne_zero _)
    ((natDegree_X_sub_C _).le.trans (by decide)), squares X X_ne_zero (natDegree_X.le.trans (by decide)),
    sum⟩

theorem paidSix_of_actual_moments {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    PaidSix q (c 1) (c 2) (c 3) (c 4) := by
  intro R rd
  simpa only [rawFourHull, nodalTail, M.middleFactor] using M.weightedMoments R rd

theorem moments_primitive_balance {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    ∃ A B D : K, 0 < A ∧ 0 < B ∧ 0 < D ∧
      (c 1)*A = (c 4)*(c 3)*B + (c 1-1)*(c 1-c 4)*(c 1-c 3)*D :=
  primitive_square_balance M.qNonzero M.qDegree
    (M.clock_ne_zero (by decide)) (M.clock_ne_zero (by decide))
    (fun e => (by decide : (2 : Fin 5) ≠ 1) (M.clockSimple e))
    (forward_outer_hull_zero M) M.forwardInner (paidSix_of_actual_moments M)

private theorem balance_reflect_twice (P : K[X]) : (P.comp (1-X)).comp (1-X) = P := by
  rw [comp_assoc, show (1-X : K[X]).comp (1-X) = X by
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel], comp_X]

private theorem balance_reflect_degree (P : K[X]) : (P.comp (1-X)).natDegree = P.natDegree := by
  rw [natDegree_comp, unit_right_weight_degree, mul_one]

theorem reflected_paidSix {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    PaidSix (q.comp (1-X)) (1-c 4) (1-c 3) (1-c 2) (1-c 1) := by
  intro R rd
  let raw := X*(1-X)*(q*nodalTail c Z)*(R.comp (1-X))
  have pd : (R.comp (1-X)).natDegree ≤ 5 := by rwa [balance_reflect_degree]
  have base : integral 0 1 raw = 0 := M.weightedMoments _ pd
  have rot :
      raw.comp (1-X) =
        X*(1-X)*(q.comp (1-X)*rawFourHull (1-c 4) (1-c 3) (1-c 2) (1-c 1))*R := by
    dsimp only [raw]
    rw [mul_comp, balance_reflect_twice, mul_comp, reflected_source_product M]
    simp only [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel]
    change (1-X)*X*(q.comp (1-X)*rawFourHull (1-c 4) (1-c 3) (1-c 2) (1-c 1))*R = _
    ring
  simpa only [rot, sub_zero] using (integral_reflect raw (0:K)).trans base

/-- Reflected primitive balance does not construct a false origin
activity assumption when q(1)=0. -/
theorem reflected_moments_primitive_balance {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    ∃ A B D : K, 0 < A ∧ 0 < B ∧ 0 < D ∧
      (1-c 4)*A = (1-c 1)*(1-c 2)*B +
        ((1-c 4)-1)*((1-c 4)-(1-c 1))*((1-c 4)-(1-c 2))*D := by
  let p := q.comp (1-X)
  let G := (1-X)*(C (c 4)-X)*q
  have pn : p ≠ 0 := by
    intro e
    apply M.qNonzero
    rw [← balance_reflect_twice q]
    change p.comp (1-X) = 0
    rw [e, zero_comp]
  have nz (i : Fin 5) : 1-c i ≠ 0 :=
    sub_ne_zero.mpr (M.active i).1.symm
  have off : 1-c 3 ≠ 1-c 4 := by
    intro e
    apply (by decide : (3 : Fin 5) ≠ 4)
    apply M.clockSimple
    linarith only [e]
  have rot : G.comp (1-X) = X*(X-C (1-c 4))*p := by
    simp only [G, p, mul_comp, sub_comp, X_comp, C_comp, one_comp, map_sub, map_one]
    ring
  have paid₁ : integral 0 (1-c 4) (X*(X-C (1-c 4))*p) = 0 := by
    simpa only [rot] using (integral_reflect G (c 4)).trans (reverse_outer_hull_zero M)
  have paid₂ : integral 0 (1-c 3) (X*(X-C (1-c 4))*p) = 0 := by
    simpa only [rot] using (integral_reflect G (c 3)).trans M.reverseInner
  exact primitive_square_balance pn ((balance_reflect_degree q).trans_le M.qDegree)
    (nz 4) (nz 3) off paid₁ paid₂ (reflected_paidSix M)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
