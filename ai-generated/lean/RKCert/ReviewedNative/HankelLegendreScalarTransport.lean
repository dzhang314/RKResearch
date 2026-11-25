module

public import RKCert.ReviewedNative.HankelLegendreScalarData
public import RKCert.ReviewedNative.HankelLegendreMomentTransport
public import Mathlib.Algebra.Polynomial.Eval.Degree

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Transport exact cleared polynomial identities into a paid field

The generic interpreter accepts integer coefficient certificates only.
All field denominators are shown nonzero from divisibility of powers of
(20!) using the actual twentieth-order paid units. -/
namespace RKResearch.Certified.Graded.HankelQuarticLegendre

open Polynomial HankelLegendreIntData HankelCenteredAtom HankelLegendreScalarData
open scoped Polynomial BigOperators

noncomputable section

variable {K : Type*} [Field K]

theorem coeff_intPoly (cs : List ℤ) (j : ℕ) :
    (intPoly K cs).coeff j = ((cs[j]?.getD 0 : ℤ) : K) := by
  induction cs generalizing j with
  | nil => simp [intPoly]
  | cons c cs ih =>
    cases j with
    | zero => simp [intPoly, Polynomial.coeff_C]
    | succ j =>
      rw [intPoly, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.succ_ne_zero j),
        Polynomial.coeff_X_mul, zero_add, ih] <;> rfl

theorem coeff_rowPoly (r : ScaledRow) (j : ℕ) :
    (rowPoly K r).coeff j = (r.denominator : K)⁻¹ * (coeffInt r j : K) := by
  simp only [rowPoly, Polynomial.coeff_C_mul, coeff_intPoly, coeffInt]

private theorem coeffInt_zero_of_length_le (r : ScaledRow) {j : ℕ}
    (hj : r.numerator.length ≤ j) : coeffInt r j = 0 := by
  have h : r.numerator[j]? = none := getElem?_neg _ _ (Nat.not_lt.mpr hj)
  simp only [coeffInt, h, Option.getD_none]

theorem rowPoly_degree_le (r : ScaledRow) : (rowPoly K r).natDegree ≤ r.numerator.length-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_rowPoly, coeffInt_zero_of_length_le r (by omega), Int.cast_zero, mul_zero]

private theorem paidPow_ne_zero (hp : (paidNat : K) ≠ 0) (n : ℕ) :
    ((paidNat^n : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero n hp

private theorem band_monic_degree {r : ScaledRow} {n : ℕ} (rband : RowBand r n)
    (hpaid : (paidNat : K) ≠ 0) : (rowPoly K r).Monic ∧ (rowPoly K r).natDegree=n := by
  have hden := cast_ne_zero_of_dvd rband.1 (paidPow_ne_zero hpaid 2)
  have c : (rowPoly K r).coeff n=1 := by
    rw [coeff_rowPoly, rband.2.2.1, Int.cast_natCast, inv_mul_cancel₀ hden]
  have le := rowPoly_degree_le (K := K) r
  rw [rband.2.1, Nat.add_sub_cancel] at le
  have deg := natDegree_eq_of_le_of_coeff_ne_zero le (by rw [c]; exact one_ne_zero)
  exact ⟨by rw [Monic.def, Polynomial.leadingCoeff, deg, c], deg⟩

private theorem band_parity {r : ScaledRow} {n : ℕ} (rband : RowBand r n) :
    reflect K (rowPoly K r) = C ((-1 : K)^n) * rowPoly K r := by
  apply Polynomial.ext
  intro j
  change ((rowPoly K r).comp (-(X:K[X]))).coeff j = _
  rw [show -(X:K[X])=C (-1)*X by simp, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul]
  by_cases h : j%2=n%2
  · rw [mul_comm ((rowPoly K r).coeff j) ((-1:K)^j),
      neg_one_pow_eq_pow_mod_two j, neg_one_pow_eq_pow_mod_two n, h]
  · have z : coeffInt r j = 0 := by
      by_cases hj : j<n+1
      · exact rband.2.2.2 ⟨j,hj⟩ h
      · apply coeffInt_zero_of_length_le
        rw [rband.2.1]
        exact Nat.le_of_not_gt hj
    rw [coeff_rowPoly, z, Int.cast_zero, mul_zero, zero_mul, mul_zero]

private theorem mode_band {n : ℕ} (hn : n≤10) : RowBand (modeRow n) n := by
  let i : Fin 11 := ⟨n,Nat.lt_succ_of_le hn⟩
  obtain ⟨dvd,len,lc,par⟩ := mode_bands i
  have pn : paidNat ∣ paidNat^2 := ⟨paidNat,pow_two paidNat⟩
  exact ⟨dvd.trans pn,len,lc,par⟩

private theorem tail_band {a n : ℕ} (amin : 5≤a) (amax : a≤7) (nmax : a+n≤11) :
    RowBand (tailRow a n) n := by
  have cases : a=5 ∨ a=6 ∨ a=7 := by omega
  rcases cases with rfl | rfl | rfl
  · exact tail_bands.1 (⟨n,by omega⟩ : Fin 7)
  · exact tail_bands.2.1 (⟨n,by omega⟩ : Fin 6)
  · exact tail_bands.2.2 (⟨n,by omega⟩ : Fin 5)

def evalExpr (K : Type*) [Field K] : Expr → K[X]
  | .row r => rowPoly K r
  | .add a b => evalExpr K a + evalExpr K b
  | .sub a b => evalExpr K a - evalExpr K b
  | .mul a b => evalExpr K a * evalExpr K b

private theorem evalExpr_degree_le (e : Expr) : (evalExpr K e).natDegree ≤ e.height := by
  induction e with
  | row r => exact rowPoly_degree_le r
  | add a b ha hb =>
    exact (natDegree_add_le _ _).trans (max_le_max ha hb)
  | sub a b ha hb =>
    exact (natDegree_sub_le _ _).trans (max_le_max ha hb)
  | mul a b ha hb =>
    exact natDegree_mul_le.trans (Nat.add_le_add ha hb)

private theorem convPrefix_sum (a b : ℕ → ℤ) (j n : ℕ) :
    convPrefix a b j n = ∑ i ∈ Finset.range n, a i * b (j-i) := by
  induction n with
  | zero => simp [convPrefix]
  | succ n ih => simp only [convPrefix, Finset.sum_range_succ, ih]

/-- Matching one rational-expression coefficient after exactly the
compositional integer denominator is cleared. -/
theorem scaled_evalExpr_coeff (e : Expr) (he : (e.denom : K) ≠ 0) (j : ℕ) :
    (e.denom : K) * (evalExpr K e).coeff j = (e.numCoeff j : K) := by
  induction e generalizing j with
  | row r =>
    change (r.denominator : K) * (rowPoly K r).coeff j = (coeffInt r j : K)
    change (r.denominator : K) ≠ 0 at he
    rw [coeff_rowPoly, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
  | add a b ha hb =>
    simp only [Expr.denom, Nat.cast_mul] at he
    simp only [Expr.denom, Nat.cast_mul, evalExpr, coeff_add, Expr.numCoeff,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [← ha (mul_ne_zero_iff.mp he).1 j, ← hb (mul_ne_zero_iff.mp he).2 j]
    ring
  | sub a b ha hb =>
    simp only [Expr.denom, Nat.cast_mul] at he
    simp only [Expr.denom, Nat.cast_mul, evalExpr, coeff_sub, Expr.numCoeff,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [← ha (mul_ne_zero_iff.mp he).1 j, ← hb (mul_ne_zero_iff.mp he).2 j]
    ring
  | mul a b ha hb =>
    simp only [Expr.denom, Nat.cast_mul] at he
    simp only [Expr.denom, Nat.cast_mul, evalExpr, Polynomial.coeff_mul,
      Expr.numCoeff, convPrefix_sum, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro i _
    rw [← ha (mul_ne_zero_iff.mp he).1 i, ← hb (mul_ne_zero_iff.mp he).2 (j-i)]
    ring

theorem evalExpr_eq_zero {e : Expr} (d : ZeroData e) (hp : (paidNat : K) ≠ 0) :
    evalExpr K e = 0 := by
  have hne := cast_ne_zero_of_dvd d.denomPaid (paidPow_ne_zero hp 16)
  apply Polynomial.ext
  intro j
  rw [coeff_zero]
  by_cases hj : j < e.height+1
  · have h := scaled_evalExpr_coeff (K := K) e hne j
    have z := d.zero ⟨j,hj⟩
    change e.numCoeff j=0 at z
    rw [z, Int.cast_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hne
  · exact coeff_eq_zero_of_natDegree_lt ((evalExpr_degree_le e).trans_lt (by omega))

theorem evalExpr_coeff_of_data {e : Expr} {j : ℕ} {num : ℤ} {den : ℕ}
    (d : CoeffData e j num den) (hp : (paidNat : K) ≠ 0) :
    (evalExpr K e).coeff j = (num : K)/(den : K) := by
  have hne := cast_ne_zero_of_dvd d.denomPaid (paidPow_ne_zero hp 16)
  have hden := cast_ne_zero_of_dvd d.denPaid (paidPow_ne_zero hp 2)
  have cle : (e.numCoeff j : K)*(den : K) = (num : K)*(e.denom : K) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun x : ℤ => (x : K)) d.cleared
  apply (eq_div_iff hden).mpr
  apply mul_left_cancel₀ hne
  rw [← mul_assoc, scaled_evalExpr_coeff e hne j, cle]
  exact mul_comm _ _

private theorem val_X : evalExpr K eX = X := by
  simp [eX, evalExpr, rowPoly, intPoly]

private theorem val_mode (n : ℕ) : evalExpr K (eMode n) = L K n := rfl
private theorem val_tail (a n : ℕ) : evalExpr K (eTail a n) = T K a n := rfl

private theorem val_rat (num : ℤ) (den : ℕ) :
    evalExpr K (eRat num den) = C ((num : K)/(den : K)) := by
  change C ((den:K)⁻¹) * (C (num:K)+X*0) = _
  rw [mul_zero, add_zero, ← C_mul, div_eq_mul_inv]
  exact congrArg C (mul_comm _ _)

private theorem val_beta (n : ℕ) : evalExpr K (eBeta n) = C (beta K n) := by
  simp only [eBeta, val_rat, beta, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, pow_two]

private theorem value_modeRec (n : ℕ) :
    evalExpr K (modeRec n) = L K (n+1) - (X*L K n - C (beta K n)*L K (n-1)) := by
  simp only [modeRec, evalExpr, val_X, val_beta, val_mode]

private theorem value_continuation (n a : ℕ) :
    evalExpr K (continuation n a) =
    L K n - (T K (a+1) (n-a)*L K a - C (beta K a)*T K (a+2) (n-a-1)*L K (a-1)) := by
  simp only [continuation, evalExpr, val_mode, val_tail, val_beta]

private theorem recurrence_coprime {F G H : K[X]} {v : K} (hv : v ≠ 0)
    (eqn : F = X*G - C v*H) (old : IsCoprime G H) : IsCoprime F G := by
  obtain ⟨a,b,e⟩ := old
  let u : K[X] := C v⁻¹
  have inv : u*C v=1 := by
    rw [show u=C v⁻¹ from rfl, ← C_mul, inv_mul_cancel₀ hv, C_1]
  refine ⟨-b*u,a+b*u*X,?_⟩
  rw [eqn]
  calc
    _ = a*G + b*(u*C v)*H := by ring
    _ = 1 := by rw [inv, mul_one, e]

private theorem beta_ne_zero {I : K[X] →ₗ[K] K} (h : CenteredPower20 I)
    {n : ℕ} (lo : 1≤n) (hi : n≤9) : beta K n ≠ 0 := by
  have x : (n : K) ≠ 0 := h.units n (by omega) (by omega)
  have y : ((2*n-1 : ℕ) : K) ≠ 0 := h.units _ (by omega) (by omega)
  have z : ((2*n+1 : ℕ) : K) ≠ 0 := h.units _ (by omega) (by omega)
  exact div_ne_zero (pow_ne_zero 2 x) (mul_ne_zero y z)

private theorem initial_mode_zero : L K 0 = 1 := by
  simp [L, rowPoly, modeRow, modeRows, intPoly]

private theorem coprime_modes {I : K[X] →ₗ[K] K} (h : CenteredPower20 I) :
    IsCoprime (L K 4) (L K 3) ∧ IsCoprime (L K 5) (L K 4) := by
  have p := h.paidNat_ne_zero
  have stepFromData {n : ℕ} (d : ZeroData (modeRec n)) :
      L K (n+1) = X*L K n - C (beta K n)*L K (n-1) := by
    have y := evalExpr_eq_zero d p
    rw [value_modeRec] at y
    exact sub_eq_zero.mp y
  have h10 : IsCoprime (L K 1) (L K 0) := by
    rw [initial_mode_zero]
    exact isCoprime_one_right
  have h21 : IsCoprime (L K 2) (L K 1) :=
    recurrence_coprime (beta_ne_zero h (n := 1) (by decide) (by decide)) (stepFromData rec1) h10
  have h32 : IsCoprime (L K 3) (L K 2) :=
    recurrence_coprime (beta_ne_zero h (n := 2) (by decide) (by decide)) (stepFromData rec2) h21
  have h43 : IsCoprime (L K 4) (L K 3) :=
    recurrence_coprime (beta_ne_zero h (n := 3) (by decide) (by decide)) (stepFromData rec3) h32
  exact ⟨h43,recurrence_coprime (beta_ne_zero h (n := 4) (by decide) (by decide)) (stepFromData rec4) h43⟩

/-- Every field-side receipt is obtained from the exact signed paid
powers plus the literal integer coefficients. No tableau-specific
comparison or hypothesis remains at this scalar boundary. -/
theorem paidLegendre28_of_centeredPower20 {I : K[X] →ₗ[K] K} (h : CenteredPower20 I) :
    PaidLegendre28 I := by
  have hp := h.paidNat_ne_zero
  have z {n a : ℕ} (d : ZeroData (continuation n a)) :
      L K n = T K (a+1) (n-a)*L K a - C (beta K a)*T K (a+2) (n-a-1)*L K (a-1) := by
    have y := evalExpr_eq_zero d hp
    rw [value_continuation] at y
    exact sub_eq_zero.mp y
  have p74 : T K 7 4 = X*T K 7 3 - C (beta K 9)*T K 7 2 := by
    have y := evalExpr_eq_zero HankelLegendreScalarData.tail74 hp
    simp only [tailStep74, evalExpr, val_tail, val_X, val_beta] at y
    exact sub_eq_zero.mp y
  refine
    { units := h.units
      modeMonic := fun n hn => (band_monic_degree (mode_band hn) hp).1
      modeDegree := fun n hn => (band_monic_degree (mode_band hn) hp).2
      modeSilent := centered_mode_silent h
      modeNorm := centered_mode_norm h
      modeEven := ?_
      modeOdd := ?_
      tailMonic := fun a n lo hi bn => (band_monic_degree (tail_band lo hi bn) hp).1
      tailDegree := fun a n lo hi bn => (band_monic_degree (tail_band lo hi bn) hp).2
      tailEven := ?_
      tailOdd := ?_
      cop43 := (coprime_modes h).1
      cop54 := (coprime_modes h).2
      step84 := z cont84
      step94 := z cont94
      step104 := z cont104
      step95 := z cont95
      step105 := z cont105
      tail74 := p74
      coeff55 := ?_
      coeff45 := ?_
      cubicI := ?_
      oddI := ?_
      evenI := ?_
      cubicII := ?_
      linearII := ?_
      cubicIII := ?_
      linearIII := ?_
      cubicIV := ?_ }
  · intro n hn par
    simpa only [neg_one_pow_eq_pow_mod_two n, par, pow_zero, C_1, one_mul] using
      band_parity (K := K) (mode_band hn)
  · intro n hn par
    simpa only [neg_one_pow_eq_pow_mod_two n, par, pow_one, map_neg, C_1, neg_mul, one_mul] using
      band_parity (K := K) (mode_band hn)
  · intro a n lo hi bn par
    simpa only [neg_one_pow_eq_pow_mod_two n, par, pow_zero, C_1, one_mul] using
      band_parity (K := K) (tail_band lo hi bn)
  · intro a n lo hi bn par
    simpa only [neg_one_pow_eq_pow_mod_two n, par, pow_one, map_neg, C_1, neg_mul, one_mul] using
      band_parity (K := K) (tail_band lo hi bn)
  · simpa only [eCoeff55, evalExpr, val_tail, val_mode, Int.cast_ofNat, Nat.cast_ofNat] using
      evalExpr_coeff_of_data c55 hp
  · simpa only [eCoeff45, evalExpr, val_tail, val_mode, Int.cast_ofNat, Nat.cast_ofNat] using
      evalExpr_coeff_of_data c45 hp
  · simpa only [eCubicI, evalExpr, val_X, val_tail, val_mode, Int.cast_ofNat, Nat.cast_ofNat, deltaI] using
      evalExpr_coeff_of_data cI hp
  · simpa only [eOddI, evalExpr, val_X, val_tail, val_mode, val_rat, Int.cast_ofNat, Nat.cast_ofNat, deltaI] using
      evalExpr_coeff_of_data lI hp
  · simpa only [eEvenI, evalExpr, val_X, val_tail, val_mode, val_rat, val_beta, ← C_add,
      Int.cast_ofNat, Nat.cast_ofNat, deltaI] using evalExpr_coeff_of_data eI hp
  · simpa only [eTwoII, evalExpr, val_X, val_tail, val_mode, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat] using
      evalExpr_coeff_of_data cII hp
  · simpa only [eTwoII, evalExpr, val_X, val_tail, val_mode, Int.cast_ofNat, Nat.cast_ofNat] using
      evalExpr_coeff_of_data lII hp
  · simpa only [eCubicIII, evalExpr, val_X, val_tail, val_mode, Int.cast_ofNat, Nat.cast_ofNat, deltaIII] using
      evalExpr_coeff_of_data cIII hp
  · simpa only [eLinearIII, evalExpr, val_X, val_tail, val_mode, val_rat, Int.cast_neg,
      Int.cast_ofNat, Nat.cast_ofNat, deltaIII] using evalExpr_coeff_of_data lIII hp
  · simpa only [eCubicIV, evalExpr, val_X, val_tail, val_mode, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat] using
      evalExpr_coeff_of_data cIV hp

end
end RKResearch.Certified.Graded.HankelQuarticLegendre
