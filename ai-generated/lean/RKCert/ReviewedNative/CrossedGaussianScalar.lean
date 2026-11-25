module

public import RKCert.ReviewedNative.FiniteGaussianParity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Scalar exit for the crossed six-node Gaussian rule

Draft. All reference inputs are strict two-node conclusions for paid
degree-eleven localizers. This module uses no extension of the base field.
-/
namespace RKCert.ReviewedNative.CrossedGaussianScalar

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def massFactor (A : K) : K := 5*A+1
def centerMean (A k : K) : K := -k / massFactor A
def centerSecond (A : K) : K := (A+3/7) / massFactor A

/-- Normalized signed moment of the second/penultimate-node factor. -/
def pairValue (m v R S : K) : K := (v-m^2) - (m-R)*(S-m)

theorem pair_lt_box {m v R S d e : K}
    (hl : R < -d) (hu : e < S) (hmL : -d < m) (hmU : m < e) :
    pairValue m v R S < v+(d-e)*m-d*e := by
  have hE : 0 < e-m := sub_pos.mpr hmU
  have hR : 0 < m-R := sub_pos.mpr (hl.trans hmL)
  have hD : m+d < m-R := by linarith only [hl]
  have hP : (m+d)*(e-m) < (m-R)*(S-m) :=
    (mul_lt_mul_of_pos_right hD hE).trans
      (mul_lt_mul_of_pos_left (sub_lt_sub_right hu m) hR)
  unfold pairValue
  nlinarith only [hP]

theorem box_numerator (A k d e : K) (hA : 0 ≤ A) :
    massFactor A * (centerSecond A + (d-e)*centerMean A k-d*e) =
      A+3/7-(d-e)*k-massFactor A*d*e := by
  have hW : 0 < massFactor A := by
    unfold massFactor
    linarith only [hA]
  unfold centerSecond centerMean
  field_simp [hW.ne'] <;> ring

/-- The finite reference cuts imply strict negativity of the actual signed
moment. The rational Newton overestimate t eliminates any square-root
hypothesis from the low-shear reference interface. -/
theorem pairValue_negative (A k R S : K)
    (hA : 0 ≤ A) (hk : 0 ≤ k)
    (atHalf : 0 ≤ A+1/4-k/2) (atQuarter : 0 ≤ A+1/16-k/4)
    (leftCoarse : R < -(13:K)/22) (rightCoarse : (7:K)/20 < S)
    (rightStrong : k ≤ 1 → (8:K)/15 < S)
    (lowShear : ∀ t : K, 0 < t → t^2 ≤ centerSecond A+1/250 →
      k ≤ 5*t/6 → R < -t ∧ t < S)
    (leftStrong : ((16:K)/25)*A / ((16:K)/25+k) < 1/8 → R < -(16:K)/25) :
    pairValue (centerMean A k) (centerSecond A) R S < 0 := by
  let v := centerSecond A
  let m := centerMean A k
  let W := massFactor A
  change pairValue m v R S < 0
  have hW : 0 < W := by
    dsimp [W, massFactor]
    linarith only [hA]
  have hm0 : m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) hW.le
  have hmL : -(1:K)/2 ≤ m := by
    change -(1:K)/2 ≤ -k/W
    apply (le_div_iff₀ hW).2
    dsimp [W, massFactor]
    linarith only [atHalf, hA]
  have hvH : v ≤ (3:K)/7 := by
    change (A+3/7)/W ≤ (3:K)/7
    apply (div_le_iff₀ hW).2
    dsimp [W, massFactor]
    linarith only [hA]
  by_contra hn
  have hT : 0 ≤ pairValue m v R S := le_of_not_gt hn
  have box0 := pair_lt_box (d := (13:K)/22) (e := (7:K)/20)
    (by simpa only [neg_div] using leftCoarse) rightCoarse
    (by linarith only [hmL]) (by linarith only [hm0]) (m := m) (v := v)
  have num0 : 0 < A+3/7-((13:K)/22-7/20)*k-massFactor A*(13/22)*(7/20) := by
    rw [← box_numerator A k ((13:K)/22) (7/20) hA]
    exact mul_pos hW (hT.trans_lt box0)
  have hk1 : k ≤ 1 := by
    unfold massFactor at num0
    linarith only [num0, hA]
  have hS := rightStrong hk1
  have box1 := pair_lt_box (d := (13:K)/22) (e := (8:K)/15)
    (by simpa only [neg_div] using leftCoarse) hS
    (by linarith only [hmL]) (by linarith only [hm0]) (m := m) (v := v)
  have hx : ((13:K)/22-8/15)*m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hm0
  have hvL : (52:K)/165 < v := by linarith only [hT, box1, hx]
  have hApay : ((52:K)/165)*W < A+3/7 := (lt_div_iff₀ hW).mp hvL
  have hAlargeCut : A < (1:K)/5 := by
    dsimp [W, massFactor] at hApay
    linarith only [hApay]
  let t : K := 5*v/6+3/10
  have htHalf : (1:K)/2 < t := by
    dsimp [t]
    linarith only [hvL]
  have ht0 : 0 < t := by linarith only [htHalf]
  have htDiff : t^2-v = (25:K)/36*(v-9/25)^2 := by
    dsimp [t]
    ring
  have htv : v ≤ t^2 := by
    have hnn : 0 ≤ (25:K)/36*(v-9/25)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith only [htDiff, hnn]
  have hband : (v-9/25)^2 ≤ ((7:K)/100)^2 := by
    have hmul := mul_nonneg (show 0 ≤ (7:K)/100-(v-9/25) by linarith only [hvH])
      (show 0 ≤ (7:K)/100+(v-9/25) by linarith only [hvL])
    nlinarith only [hmul]
  have htUpper : t^2 ≤ v+1/250 := by linarith only [htDiff, hband]
  have hkLow : 5*t/6 < k := by
    by_contra hn'
    have hroots := lowShear t ht0 htUpper (le_of_not_gt hn')
    have hb := pair_lt_box (d := t) (e := t) hroots.1 hroots.2
      (by linarith only [htHalf, hmL]) (by linarith only [ht0, hm0]) (m := m) (v := v)
    linarith only [hT, hb, htv]
  have hkL : (7:K)/16 < k := by
    dsimp [t] at hkLow
    linarith only [hkLow, hvL]
  have hASmallCut : (1:K)/16 < A := by
    by_contra hn'
    have hle : A ≤ (1:K)/16 := le_of_not_gt hn'
    have hkH : k ≤ (1:K)/2 := by linarith only [atQuarter, hle]
    have hvSmall : (55:K)/147 ≤ v := by
      change (55:K)/147 ≤ (A+3/7)/W
      apply (le_div_iff₀ hW).2
      dsimp [W, massFactor]
      linarith only [hle]
    dsimp [t] at hkLow
    linarith only [hkLow, hkH, hvSmall]
  have hshift : ((16:K)/25)*A / ((16:K)/25+k) < 1/8 := by
    apply (div_lt_iff₀ (show 0 < (16:K)/25+k by linarith only [hk])).2
    linarith only [hAlargeCut, hkL]
  have hR := leftStrong hshift
  have bf := pair_lt_box (d := (16:K)/25) (e := (8:K)/15)
    (by simpa only [neg_div] using hR) hS
    (by linarith only [hmL]) (by linarith only [hm0]) (m := m) (v := v)
  have numF : 0 < A+3/7-((16:K)/25-8/15)*k-massFactor A*(16/25)*(8/15) := by
    rw [← box_numerator A k ((16:K)/25) (8/15) hA]
    exact mul_pos hW (hT.trans_lt bf)
  unfold massFactor at numF
  linarith only [numF, hASmallCut, hkL]

end
end RKCert.ReviewedNative.CrossedGaussianScalar
