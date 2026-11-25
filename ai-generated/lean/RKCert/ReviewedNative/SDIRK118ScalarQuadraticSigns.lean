module

public import RKCert.ReviewedNative.SDIRK118ScalarExistence

import RKCert.ReviewedNative.DyadicBox64
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadraticSigns

open ClaimPin ScalarBindings ScalarExistence
open Polynomial
open RKCert.ReviewedNative.DyadicBox64
open scoped BigOperators Polynomial

private def boxA (S : Box) : Box := mul (add (point 1) S) (point (1/2))
private def boxZ (S : Box) : Box := add (boxA S) S

private theorem boxA_encloses {S : Box} {s : ℝ} (hs : encloses S s) :
    encloses (boxA S) (aAt s) := by
  have hh : encloses (point (1/2)) (1/2:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using point_encloses (K := ℝ) (1/2)
  simpa only [boxA,aAt,mul_one_div] using
    mul_encloses (add_encloses one_encloses hs) hh

private theorem boxZ_encloses {S : Box} {s : ℝ} (hs : encloses S s) :
    encloses (boxZ S) (zAt s) :=
  add_encloses (boxA_encloses hs) hs

/-- Ascending coefficient update for multiplication by X-C(x).
The explicit multiply by 1 keeps the archived operation order. -/
private def next (B : Box) (F : ℕ → Box) : ℕ → Box
  | 0 => mul (F 0) (sub (point 0) B)
  | n+1 => add (mul (F n) (point 1)) (mul (F (n+1)) (sub (point 0) B))

private def oneCoeffs : ℕ → Box
  | 0 => point 1
  | _+1 => point 0

private theorem oneCoeffs_encloses (n : ℕ) :
    encloses (oneCoeffs n) ((1:Polynomial ℝ).coeff n) := by
  cases n with
  | zero => simpa [oneCoeffs] using one_encloses
  | succ n => simpa [oneCoeffs,coeff_one,Nat.succ_ne_zero] using zero_encloses

private theorem next_encloses {P : Polynomial ℝ} {F : ℕ → Box} {B : Box} {x : ℝ}
    (hF : ∀ n, encloses (F n) (P.coeff n)) (hx : encloses B x) (n : ℕ) :
    encloses (next B F n) ((P*linearFactor x).coeff n) := by
  have hneg := sub_encloses zero_encloses hx
  cases n with
  | zero =>
    simpa only [next,linearFactor,mul_sub,coeff_sub,coeff_mul_X_zero,coeff_mul_C,
      zero_sub,mul_neg] using mul_encloses (hF 0) hneg
  | succ n =>
    rw [linearFactor, mul_sub, coeff_sub, coeff_mul_X, coeff_mul_C]
    simpa only [next, zero_sub, zero_add, mul_neg, mul_one, sub_eq_add_neg] using
      add_encloses (mul_encloses (hF n) one_encloses) (mul_encloses (hF (n+1)) hneg)

private def rawCoeffs (S T : Box) : ℕ → Box :=
  next T (next S (next (boxA S) (next (point 1) oneCoeffs)))

private theorem rawCoeffs_encloses {S T : Box} {s t : ℝ}
    (hs : encloses S s) (ht : encloses T t) (i : ℕ) :
    encloses (rawCoeffs S T i) ((Zpoly s t).coeff i) := by
  have h1 := next_encloses oneCoeffs_encloses one_encloses
  have h2 := next_encloses h1 (boxA_encloses hs)
  have h3 := next_encloses h2 hs
  have h4 := next_encloses h3 ht i
  have e : (1:Polynomial ℝ)*linearFactor 1*linearFactor (aAt s)*linearFactor s*
      linearFactor t = Zpoly s t := by
    simp only [one_mul,Zpoly,Jpoly,cubic]
    ac_rfl
  rw [← e]
  exact h4

private theorem z_degree (s t : ℝ) : (Zpoly s t).natDegree ≤ 4 := by
  have f (x : ℝ) : (linearFactor x).natDegree ≤ 1 := natDegree_X_sub_C_le x
  have h2 : (linearFactor s*linearFactor t).natDegree ≤ 2 :=
    natDegree_mul_le.trans (Nat.add_le_add (f s) (f t))
  have h3 : (linearFactor s*linearFactor t*linearFactor (1:ℝ)).natDegree ≤ 3 :=
    natDegree_mul_le.trans (Nat.add_le_add h2 (f 1))
  unfold Zpoly Jpoly cubic
  exact natDegree_mul_le.trans (Nat.add_le_add (f (aAt s)) h3)

theorem moment_eq_receipt_sum (M : MonomialBasis) (hM : standardPowers M)
    (s t : ℝ) (hz : zAt s ≠ 0) (j : ℕ) :
    μ M s t j = ∑ i ∈ Finset.range 5,
      (Zpoly s t).coeff i * ((zAt s)^(j+i) / ((j+i+1:ℕ):ℝ)) := by
  have hd : ((X:Polynomial ℝ)^j*Zpoly s t).natDegree < j+5 :=
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_X_pow_le (R:=ℝ) j) (z_degree s t))).trans_lt
      (Nat.lt_succ_self (j+4))
  rw [μ,avg_eq_coefficient_sum M hM (zAt s) hz _ (j+5) hd,Finset.sum_range_add _ j 5]
  have zeroPart : (∑ k ∈ Finset.range j,
      (((X:Polynomial ℝ)^j*Zpoly s t).coeff k) *
        ((zAt s)^k / ((k+1:ℕ):ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : ¬ j ≤ k := not_le_of_gt (Finset.mem_range.mp hk)
    simp only [coeff_X_pow_mul',if_neg hkj,zero_mul]
  rw [zeroPart,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have shift : (((X:Polynomial ℝ)^j*Zpoly s t).coeff (j+i)) = (Zpoly s t).coeff i := by
    rw [Nat.add_comm j i,coeff_X_pow_mul]
  rw [shift]

private def momentBox (S T : Box) (j : ℕ) : Box :=
  sumBox (fun i => divideNat (mul (rawCoeffs S T i) (powBox (boxZ S) (j+i))) (j+i+1)) 5

private theorem momentBox_encloses (M : MonomialBasis) (hM : standardPowers M)
    {S T : Box} {s t : ℝ} (hs : encloses S s) (ht : encloses T t)
    (hz : zAt s ≠ 0) (j : ℕ) : encloses (momentBox S T j) (μ M s t j) := by
  rw [moment_eq_receipt_sum M hM s t hz j]
  unfold momentBox
  apply sumBox_encloses
  intro i
  simpa only [mul_div_assoc] using divideNat_encloses
    (mul_encloses (rawCoeffs_encloses hs ht i) (powBox_encloses (boxZ_encloses hs) (j+i))) (j+i+1)

private def determinantBox (S T : Box) : Box :=
  sub (mul (momentBox S T 0) (momentBox S T 2))
    (mul (momentBox S T 1) (momentBox S T 1))

private def numeratorOne (S T : Box) : Box :=
  sub (mul (momentBox S T 1) (momentBox S T 2))
    (mul (momentBox S T 0) (momentBox S T 3))

private def numeratorZero (S T : Box) : Box :=
  sub (mul (momentBox S T 1) (momentBox S T 3))
    (mul (momentBox S T 2) (momentBox S T 2))

private def psiBox (S T B : Box) : Box :=
  add (add (mul (determinantBox S T) (mul B B))
    (mul (numeratorOne S T) B)) (numeratorZero S T)

private theorem determinant_encloses (M : MonomialBasis) (hM : standardPowers M)
    {S T : Box} {s t : ℝ} (hs : encloses S s) (ht : encloses T t)
    (hz : zAt s ≠ 0) : encloses (determinantBox S T) (momentDet M s t) := by
  have h := momentBox_encloses M hM hs ht hz
  simpa only [determinantBox,momentDet,pow_two] using
    sub_encloses (mul_encloses (h 0) (h 2)) (mul_encloses (h 1) (h 1))

private theorem psi_encloses (M : MonomialBasis) (hM : standardPowers M)
    {S T B : Box} {s t c : ℝ} (hs : encloses S s) (ht : encloses T t)
    (hz : zAt s ≠ 0) (hc : encloses B c) :
    encloses (psiBox S T B) (clearedQuad M s t c) := by
  have h := momentBox_encloses M hM hs ht hz
  have d := determinant_encloses M hM hs ht hz
  have n1 := sub_encloses (mul_encloses (h 1) (h 2)) (mul_encloses (h 0) (h 3))
  have n0 := sub_encloses (mul_encloses (h 1) (h 3)) (mul_encloses (h 2) (h 2))
  simpa only [psiBox,numeratorOne,numeratorZero,clearedQuad,pow_two] using
    add_encloses (add_encloses (mul_encloses d (mul_encloses hc hc))
      (mul_encloses n1 hc)) n0

private def sInput : Box :=
  ⟨457148959716/(2:ℚ)^40,457148959717/(2:ℚ)^40⟩
private def tInput : Box :=
  ⟨138977439915/(2:ℚ)^40,138977439916/(2:ℚ)^40⟩
private def cLeft : ℚ := 1270550/(2:ℚ)^20
private def cRight : ℚ := 1270551/(2:ℚ)^20

private theorem sInput_encloses {s : ℝ} (hs : s ∈ Set.Icc sLo sHi) : encloses sInput s := by
  simpa only [encloses,sInput,sLo,sHi,Set.mem_Icc,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hs

private theorem tInput_encloses {t : ℝ} (ht : t ∈ Set.Icc tLo tHi) : encloses tInput t := by
  simpa only [encloses,tInput,tLo,tHi,Set.mem_Icc,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using ht

private theorem cLeft_encloses : encloses (point cLeft) cLo := by
  simpa only [cLeft,cLo,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using point_encloses (K := ℝ) cLeft

private theorem cRight_encloses : encloses (point cRight) cHi := by
  simpa only [cRight,cHi,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using point_encloses (K := ℝ) cRight

-- These are the four archived receipt pairs, checked again by the Lean kernel.
private theorem receiptDet : determinantBox sInput tInput =
    ⟨21444555992759/scale,21444556991322/scale⟩ := by decide +kernel

private theorem receiptZero : psiBox sInput tInput (point 0) =
    ⟨-1954075334988/scale,-1954074270433/scale⟩ := by decide +kernel

private theorem receiptLeft : psiBox sInput tInput (point cLeft) =
    ⟨-16404071/scale,-12465253/scale⟩ := by decide +kernel

private theorem receiptRight : psiBox sInput tInput (point cRight) =
    ⟨9914350/scale,13853173/scale⟩ := by decide +kernel

/-- Exactly the quadratic field of BoxSignBindings, with no affine
or old-weight signs and no premise about actual roots. -/
theorem quadratic_box_signs (M : MonomialBasis) (hM : standardPowers M)
    (s : ℝ) (hs : s ∈ Set.Icc sLo sHi) (t : ℝ) (ht : t ∈ Set.Icc tLo tHi) :
    0 < momentDet M s t ∧ clearedQuad M s t 0 < 0 ∧
      clearedQuad M s t cLo < 0 ∧ 0 < clearedQuad M s t cHi := by
  have hs0 : 0 < s := (show (0:ℝ) < sLo by norm_num [sLo]).trans_le hs.1
  have hz : zAt s ≠ 0 := by
    apply ne_of_gt
    unfold zAt aAt
    linarith only [hs0]
  have hS := sInput_encloses hs
  have hT := tInput_encloses ht
  refine ⟨sign_pos (determinant_encloses M hM hS hT hz) ?_,
    sign_neg (psi_encloses M hM hS hT hz zero_encloses) ?_,
    sign_neg (psi_encloses M hM hS hT hz cLeft_encloses) ?_,
    sign_pos (psi_encloses M hM hS hT hz cRight_encloses) ?_⟩
  · rw [receiptDet]
    exact div_pos (by norm_num) scale_pos
  · rw [receiptZero]
    exact div_neg_of_neg_of_pos (by norm_num) scale_pos
  · rw [receiptLeft]
    exact div_neg_of_neg_of_pos (by norm_num) scale_pos
  · rw [receiptRight]
    exact div_pos (by norm_num) scale_pos

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadraticSigns
