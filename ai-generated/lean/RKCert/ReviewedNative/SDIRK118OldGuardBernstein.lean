module

public import RKCert.ReviewedNative.SDIRK118OldGuardSemantics

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.OldGuardBernstein

open ClaimPin ScalarBindings ScalarExistence OldGuardSemantics
open scoped BigOperators

/-- Standard Bernstein weight, ordered as in Mathlib.add_pow. -/
def bern (d i : ℕ) (x : ℝ) : ℝ :=
  x^i*(1-x)^(d-i)*(d.choose i : ℝ)

theorem bern_nonneg (d i : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ bern d i x :=
  mul_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _))
    (Nat.cast_nonneg _)

theorem bern_total (d : ℕ) (x : ℝ) : (∑ i : Fin (d+1), bern d i.val x) = 1 := by
  calc
    _ = ∑ i ∈ Finset.range (d+1), bern d i x := Fin.sum_univ_eq_sum_range _ (d + 1)
    _ = (x+(1-x))^d := (add_pow x (1-x) d).symm
    _ = 1 := by rw [show x+(1-x)=1 by ring,one_pow]

def tensorValue (m n : ℕ) (coeff : Fin (m+1) → Fin (n+1) → ℤ) (S T : ℝ) : ℝ :=
  ∑ i : Fin (m+1), ∑ j : Fin (n+1),
    (coeff i j : ℝ) * (bern m i.val S * bern n j.val T)

theorem tensor_lower (m n : ℕ) (coef : Fin (m+1) → Fin (n+1) → ℤ) (low : ℤ)
    (hcoef : ∀ i j, low ≤ coef i j) {S T : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (low : ℝ) ≤ tensorValue m n coef S T := by
  have one : (∑ i : Fin (m+1), ∑ j : Fin (n+1),
      bern m i.val S * bern n j.val T) = 1 := by
    calc
      _ = ∑ i : Fin (m+1), bern m i.val S * (∑ j : Fin (n+1), bern n j.val T) := by
        simp_rw [Finset.mul_sum]
      _ = 1 := by simp only [bern_total, mul_one]
  calc
    (low : ℝ) = (low : ℝ)*(∑ i : Fin (m+1), ∑ j : Fin (n+1),
        bern m i.val S * bern n j.val T) := by rw [one,mul_one]
    _ = ∑ i : Fin (m+1), ∑ j : Fin (n+1),
        (low : ℝ)*(bern m i.val S * bern n j.val T) := by simp_rw [Finset.mul_sum]
    _ ≤ tensorValue m n coef S T := by
      unfold tensorValue
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr (hcoef i j))
        (mul_nonneg (bern_nonneg m i.val hS0 hS1) (bern_nonneg n j.val hT0 hT1))

/-- Exact integer table semantics: multiply by the published common scale,
substitute the archived affine box map, and reconstruct with the tensor
basis. The reconstruction is a polynomial equality, not an interval test. -/
structure TensorReceipt (f : ℝ → ℝ → ℝ) (m n : ℕ) (scale low : ℤ) where
  coeff : Fin (m+1) → Fin (n+1) → ℤ
  bounds : ∀ i j, low ≤ coeff i j
  reconstruct : ∀ S T : ℝ,
    (scale : ℝ)*f ((13+S)/32) ((25+T)/200) = tensorValue m n coeff S T

theorem TensorReceipt.positive {f : ℝ → ℝ → ℝ} {m n : ℕ} {scale low : ℤ}
    (r : TensorReceipt f m n scale low) (hscale : 0 < scale) (hlow : 0 < low)
    {s t : ℝ} (hs0 : (13/32 : ℝ) ≤ s) (hs1 : s ≤ 14/32)
    (ht0 : (1/8 : ℝ) ≤ t) (ht1 : t ≤ 13/100) :
    0 < f s t := by
  let S := 32*s-13
  let T := 200*t-25
  have hS0 : 0 ≤ S := by dsimp [S]; linarith
  have hS1 : S ≤ 1 := by dsimp [S]; linarith
  have hT0 : 0 ≤ T := by dsimp [T]; linarith
  have hT1 : T ≤ 1 := by dsimp [T]; linarith
  have es : (13+S)/32=s := by dsimp [S]; ring
  have et : (25+T)/200=t := by dsimp [T]; ring
  have lower := tensor_lower m n r.coeff low r.bounds hS0 hS1 hT0 hT1
  have hh : 0 < (scale : ℝ) * f s t := by
    rw [←es,←et,r.reconstruct]
    exact (Int.cast_pos.mpr hlow).trans_le lower
  have hs : (0 : ℝ) ≤ (scale : ℝ) := by exact_mod_cast hscale.le
  exact pos_of_mul_pos_right hh hs

/-- The exact five archived lower bounds, after negating the two negative
receipts. The inputs are the coefficient tables and their reconstruction,
not the desired old-weight or residual guards. -/
structure OldGuardReceipts where
  omega0 : TensorReceipt (fun s t => -omegaExpr s t 0) 9 3
    612849837292577095680000000 669364354399255693516800000000
  omega1 : TensorReceipt (fun s t => omegaExpr s t 1) 9 3
    612849837292577095680000000 410537585922285356236800000000
  omega2 : TensorReceipt (fun s t => -omegaExpr s t 2) 9 3
    612849837292577095680000000 345133187859393097113600000000
  omega3 : TensorReceipt (fun s t => omegaExpr s t 3) 9 0
    12767704943595356160 9500653180184877043200
  residual : TensorReceipt jExpr 12 3
    26508059778292179478039756800000000 96296338477971377220208656384000000000

theorem coarse_oldGuards_of_receipts (M : MonomialBasis) (hm : standardPowers M)
    (receipt : OldGuardReceipts) (s t : ℝ) (hD : 0 < momentDet M s t)
    (hs0 : (13/32 : ℝ) ≤ s) (hs1 : s ≤ 14/32)
    (ht0 : (1/8 : ℝ) ≤ t) (ht1 : t ≤ 13/100) :
    (∀ i : Fin 4, omegaOld M s t i ≠ 0) ∧ 0 < residualJ0 M s t := by
  have hz : 0 < zAt s := by unfold zAt aAt; linarith
  have hz2 : 0 < z2 s := by rw [z2_twice]; exact mul_pos (by norm_num) hz
  have hG (i : Fin 4) : G M s t i ≠ 0 := by
    rw [G_eq_receipt M hm]
    fin_cases i
    · exact neg_ne_zero.mp ((receipt.omega0.positive (by norm_num) (by norm_num) hs0 hs1 ht0 ht1).ne')
    · exact (receipt.omega1.positive (by norm_num) (by norm_num) hs0 hs1 ht0 ht1).ne'
    · exact neg_ne_zero.mp ((receipt.omega2.positive (by norm_num) (by norm_num) hs0 hs1 ht0 ht1).ne')
    · exact (receipt.omega3.positive (by norm_num) (by norm_num) hs0 hs1 ht0 ht1).ne'
  have hJ : 0 < GJ M s t := by
    rw [GJ_eq_receipt M hm]
    exact receipt.residual.positive (by norm_num) (by norm_num) hs0 hs1 ht0 ht1
  constructor
  · intro i hi
    have e := omega_scale M hm s t i hz hD
    rw [hi,mul_zero] at e
    exact (mul_ne_zero (pow_ne_zero 2 hz.ne') (mul_ne_zero (pow_ne_zero 2 hz2.ne') (hG i))) e
  · have hh : 0 < (12*840*16 : ℝ)*D' M s t*residualJ0 M s t := by
      rw [← residual_scale M hm s t hz hD]
      exact mul_pos (pow_pos hz 3) hJ
    exact pos_of_mul_pos_right hh
      (mul_nonneg (by norm_num) (D'_pos M hm s t hz hD).le)

/-- Precisely the oldGuards field of BoxSignBindings. Moment positivity
comes from its separate quadratic field; this module does not prove or
duplicate that field. The fixed narrow box lies inside the archived box. -/
theorem oldGuards_of_receipts (M : MonomialBasis) (hm : standardPowers M)
    (receipt : OldGuardReceipts)
    (hD : ∀ s ∈ Set.Icc sLo sHi, ∀ t ∈ Set.Icc tLo tHi, 0 < momentDet M s t) :
    ∀ s ∈ Set.Icc sLo sHi, ∀ t ∈ Set.Icc tLo tHi,
      (∀ i : Fin 4, omegaOld M s t i ≠ 0) ∧ 0 < residualJ0 M s t := by
  intro s hs t ht
  exact coarse_oldGuards_of_receipts M hm receipt s t (hD s hs t ht)
    ((show (13/32:ℝ) ≤ sLo by norm_num [sLo]).trans hs.1)
    (hs.2.trans (show sHi ≤ (14/32:ℝ) by norm_num [sHi]))
    ((show (1/8:ℝ) ≤ tLo by norm_num [tLo]).trans ht.1)
    (ht.2.trans (show tHi ≤ (13/100:ℝ) by norm_num [tHi]))

end RKResearch.Certified.PaidDefectBridge.SDIRK118.OldGuardBernstein
