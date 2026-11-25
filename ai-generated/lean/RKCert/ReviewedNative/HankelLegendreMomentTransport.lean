module

public import RKCert.ReviewedNative.HankelQuarticLegendreReceipts
public import RKCert.ReviewedNative.OrderTwentyCenteredMoments

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Paid signed transport on integer Horner polynomials

No norm of the degree-10 mode is requested; its last silence is at
raw degree 19. Nonzero norms use the checked integer divisibility by
(20!)², not positivity of the field or of the given weights. -/
namespace RKResearch.Certified.Graded.HankelQuarticLegendre

open Polynomial HankelLegendreIntData HankelCenteredAtom
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K] {I : K[X] →ₗ[K] K}

theorem cast_ne_zero_of_dvd {a b : ℕ} (hdvd : a ∣ b) (hne : (b : K) ≠ 0) :
    (a : K) ≠ 0 := by
  rcases hdvd with ⟨t,ht⟩
  rw [ht, Nat.cast_mul] at hne
  exact fun hz => hne (by rw [hz, zero_mul])

/-- Includes empty rows (whose moment is zero), without wasting a paid
atom on that row. The bound charges the last nonempty degree j+len-1. -/
theorem scaled_intPoly_moment (h : CenteredPower20 I) (cs : List ℤ) (j : ℕ)
    (pay : j+cs.length≤20) :
    (paidNat : K) * I (X^j * intPoly K cs) = (intPaidTest cs j : K) := by
  induction cs generalizing j with
  | nil => simp [intPoly, intPaidTest]
  | cons c cs ih =>
    have tail : j+1+cs.length≤20 := by simp only [List.length_cons] at pay; omega
    have head : j<20 := by omega
    have mul (P : K[X]) :
        X^j * C (c : K) + X^j*(X*P) = C (c : K)*X^j + X^(j+1)*P := by
      rw [pow_succ]
      ac_rfl
    rw [intPoly, mul_add, mul, map_add, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    calc
      _ = (c:K)*((paidNat:K)*I (X^j)) + (paidNat:K)*I (X^(j+1)*intPoly K cs) := by ring
      _ = _ := by rw [h.powers j head, ih (j+1) tail, intPaidTest, Int.cast_add, Int.cast_mul]

theorem scaled_rowPoly_moment (h : CenteredPower20 I) (r : ScaledRow) (j : ℕ)
    (pay : j+r.numerator.length≤20) (den : (r.denominator : K) ≠ 0) :
    (r.denominator : K) * ((paidNat : K) * I (X^j * rowPoly K r)) =
      (intPaidTest r.numerator j : K) := by
  have reorder : X^j * rowPoly K r = C ((r.denominator : K)⁻¹)*(X^j*intPoly K r.numerator) := by
    unfold rowPoly
    ac_rfl
  rw [reorder, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul, ← scaled_intPoly_moment h _ _ pay]
  calc
    _ = ((r.denominator : K) * (r.denominator : K)⁻¹) *
      ((paidNat : K) * I (X^j*intPoly K r.numerator)) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel₀ den, one_mul]

/-- The paid detector tests themselves, with exact mode and power ranges. -/
theorem centered_mode_silent (h : CenteredPower20 I) (n : ℕ) (hn : n≤10)
    (j : ℕ) (hj : j<n) : I (X^j * L K n) = 0 := by
  let i : Fin 11 := ⟨n, Nat.lt_succ_of_le hn⟩
  obtain ⟨dvd,len,_,_⟩ := mode_bands i
  change (modeRow n).denominator ∣ paidNat at dvd
  change (modeRow n).numerator.length=n+1 at len
  have hden := cast_ne_zero_of_dvd dvd h.paidNat_ne_zero
  have e := scaled_rowPoly_moment h (modeRow n) j (by rw [len]; omega) hden
  have z : intPaidTest (modeRow n).numerator j = 0 := mode_tests i ⟨j,hj⟩
  rw [z, Int.cast_zero] at e
  exact (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hden)).resolve_left h.paidNat_ne_zero

theorem centered_mode_norm (h : CenteredPower20 I) (n : ℕ) (hn : n≤9) :
    I (X^n * L K n) ≠ 0 := by
  let i : Fin 10 := ⟨n, Nat.lt_succ_of_le hn⟩
  let i' : Fin 11 := ⟨n, by omega⟩
  obtain ⟨dvd,len,_,_⟩ := mode_bands i'
  obtain ⟨positive,havedvd⟩ := mode_norm_num i
  change (modeRow n).denominator ∣ paidNat at dvd
  change (modeRow n).numerator.length=n+1 at len
  change 0 < intPaidTest (modeRow n).numerator n at positive
  change (intPaidTest (modeRow n).numerator n).natAbs ∣ paidNat^2 at havedvd
  have hd : ((paidNat^2 : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero 2 h.paidNat_ne_zero
  have hnz := cast_ne_zero_of_dvd havedvd hd
  have z : ((intPaidTest (modeRow n).numerator n).natAbs : K) =
      (intPaidTest (modeRow n).numerator n : K) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg positive.le]
  rw [z] at hnz
  have e := scaled_rowPoly_moment h (modeRow n) n (by rw [len]; omega)
    (cast_ne_zero_of_dvd dvd h.paidNat_ne_zero)
  intro zero
  change I (X^n * rowPoly K (modeRow n))=0 at zero
  rw [zero, mul_zero, mul_zero] at e
  exact hnz e.symm

end
end RKResearch.Certified.Graded.HankelQuarticLegendre
