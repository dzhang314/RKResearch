module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import RKCert.ReviewedNative.LegendreEnergyRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.LegendreEnergy

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- If the forward first and reverse outer marks are positive, and the
reverse inner mark is negative, the genuine forward first mark cannot
overlap the reverse outer mark. Only a degree-four global test is used. -/
theorem Moments.outer_order_of_negative_reverse_inner {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (u0 : 0 < c 1) (u1 : c 1 < 1)
    (z0 : 0 < c 4) (h0 : c 3 < 0) : c 1 < c 4 := by
  let u := c 1
  let a := c 2
  let h := c 3
  let z := c 4
  change u < z
  by_contra! bad
  have zu : z < u := lt_of_le_of_ne bad (fun e =>
    (by decide : (4 : Fin 5) ≠ 1) (M.clockSimple e))
  let L : K[X] := X * (X - C u)
  let P : K[X] := (X - 1) * (X - C z) * (X - C h)
  let F := formalPrimitive (L * q)
  have f0 : F.eval 0 = 0 := formalPrimitive_eval_zero _
  have fprime : F.derivative = L * q := derivative_formalPrimitive _
  have ln : L ≠ 0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  have fn : F ≠ 0 := by
    intro zero
    rw [zero, derivative_zero] at fprime
    exact (mul_ne_zero ln M.qNonzero) fprime.symm
  have fu : F.eval u = 0 := by
    have j1 : integral 0 u (X * q) = 0 := M.forwardFirst
    have j2 : integral 0 u (X^2 * q) = 0 := M.forwardSecond
    have e : integral 0 u (L * q) = 0 := by
      rw [show L * q = X^2 * q - C u * (X * q) by dsimp only [L]; ring,
        map_sub, integral_C_mul, j1, j2, mul_zero, sub_zero]
    rw [integral_zero_left] at e
    exact e
  have fa : F.eval a = 0 := by
    have e : integral 0 a (L * q) = 0 := M.forwardInner
    rw [integral_zero_left] at e
    exact e
  obtain ⟨J, Jrep⟩ := dvd_iff_isRoot.mpr (show F.IsRoot 0 from f0)
  have fJ : F = X * J := by simpa only [map_zero, sub_zero] using Jrep
  have Ju : J.eval u = 0 := by
    rw [fJ, eval_mul, eval_X] at fu
    exact (mul_eq_zero.mp fu).resolve_left u0.ne'
  obtain ⟨V, Vrep⟩ := dvd_iff_isRoot.mpr (show J.IsRoot u from Ju)
  have fV : F = L * V := by rw [fJ, Vrep]; dsimp only [L]; ring
  have vn : V ≠ 0 := fun e => fn (by rw [fV, e, mul_zero])
  have Lna : L.eval a ≠ 0 := by
    simp only [L, eval_mul, eval_X, eval_sub, eval_C]
    exact mul_ne_zero (M.clock_ne_zero (i := 2) (by decide))
      (sub_ne_zero.mpr (fun e => (by decide : (2 : Fin 5) ≠ 1) (M.clockSimple e)))
  have Va : V.eval a = 0 := by
    rw [fV, eval_mul] at fa
    exact (mul_eq_zero.mp fa).resolve_left Lna
  obtain ⟨B, Brep⟩ := dvd_iff_isRoot.mpr (show V.IsRoot a from Va)
  have bn : B ≠ 0 := fun e => vn (by rw [Brep, e, mul_zero])
  have ld : L.natDegree = 2 := by
    dsimp only [L]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero u), natDegree_X, natDegree_X_sub_C]
  have raw : (L * q).natDegree ≤ 6 := natDegree_mul_le_of_le ld.le M.qDegree
  have fd : F.natDegree ≤ 7 :=
    (natDegree_formalPrimitive_le (L * q)).trans (Nat.add_le_add_right raw 1)
  have vd : V.natDegree ≤ 5 := by
    rw [fV, natDegree_mul ln vn, ld] at fd
    omega
  have bd : B.natDegree ≤ 4 := by
    have e := vd
    rw [Brep, natDegree_mul (X_sub_C_ne_zero a) bn, natDegree_X_sub_C] at e
    omega
  have identity : (X * (1 - X)) * (q * nodalTail c Z) * B =
      -(P * V * F.derivative) := by
    rw [fprime, Brep]
    simp only [nodalTail, M.middleFactor]
    dsimp only [P, L, u, a, h, z]
    ring
  have paid := M.weightedMoments B (bd.trans (by decide : 4 ≤ 5))
  rw [identity, map_neg, neg_eq_zero] at paid
  let T := (P.derivative * L - P * L.derivative) * V^2
  let H := P * L * V^2
  have deriv : H.derivative = T + C (2 : K) * (P * V * F.derivative) := by
    rw [fV]
    dsimp only [H, T]
    simp only [derivative_mul, derivative_sq, map_ofNat]
    ring
  have hz : integral 0 1 H.derivative = 0 := by
    rw [integral_derivative]
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
  have d₁ : (C u * L^2).natDegree ≤ 4 :=
    (natDegree_C_mul_le u (L^2)).trans (natDegree_pow_le_of_le 2 ld.le)
  have d₂ : (C (z * h) * (X - C u)^2).natDegree ≤ 4 :=
    ((natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 2 (natDegree_X_sub_C u).le)).trans
      (by decide : 2 ≤ 4)
  have d₃ : (C ((u - 1) * (u - z) * (u - h)) * X^2).natDegree ≤ 4 :=
    ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)).trans (by decide : 2 ≤ 4)
  have jd : J₀.natDegree ≤ 4 :=
    natDegree_sub_le_of_le (natDegree_sub_le_of_le d₁ d₂) d₃
  have pd : (J₀ * V^2).natDegree ≤ 14 :=
    natDegree_mul_le_of_le jd (natDegree_pow_le_of_le 2 vd)
  have zh : z * h < 0 := mul_neg_of_pos_of_neg z0 h0
  have tiny : (u - 1) * (u - z) * (u - h) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr u1) (sub_pos.mpr zu))
      (sub_pos.mpr (h0.trans u0))
  have positive (x : K) (hx : x ∈ Set.Ioo (0 : K) 1) : 0 < J₀.eval x := by
    simp only [J₀, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    have first := mul_nonneg u0.le (sq_nonneg (L.eval x))
    have second := mul_nonpos_of_nonpos_of_nonneg zh.le (sq_nonneg (x - u))
    have third := mul_neg_of_neg_of_pos tiny (sq_pos_of_ne_zero hx.1.ne')
    linarith only [first, second, third]
  obtain ⟨i, live⟩ := exists_nonzero_grid_sample zero_lt_one vn
    (vd.trans_lt (by decide : 5 < 19))
  have now : 0 < integral 0 1 (J₀ * V^2) := by
    apply integral_pos_of_grid_samples zero_lt_one (pd.trans (by decide : 14 ≤ 19))
    · intro j
      rw [eval_mul, eval_pow]
      exact mul_nonneg (positive _ (intervalPoint_mem zero_lt_one j)).le (sq_nonneg _)
    · refine ⟨i, ?_⟩
      rw [eval_mul, eval_pow]
      exact mul_pos (positive _ (intervalPoint_mem zero_lt_one i)) (sq_pos_of_ne_zero live)
  exact now.ne' zero

end
end RKCert.ReviewedNative.WeakFive16
