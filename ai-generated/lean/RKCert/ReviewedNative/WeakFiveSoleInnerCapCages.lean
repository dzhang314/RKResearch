module

public import RKCert.ReviewedNative.WeakFiveSoleInnerCapReceipts
public import RKCert.ReviewedNative.WeakFiveSoleInnerCornerEnclosure

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The literal Gaussian cages give the four signed box axes -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A sign-aware alternative to a centered root: the shifted factor is
(X+operatorname{shift}(z,x)) directly in both phases. -/
def rootShift (z x : K) : K := (z-x)/(1-z)

theorem rootShift_le {z₀ z₁ x₀ x₁ : K} (z : z₀≤z₁) (x : x₁≤x₀)
    (h₀ : z₀ < 1) (h₁ : z₁ < 1) (xUnit : x₀≤1) :
    rootShift z₀ x₀≤rootShift z₁ x₁ := by
  unfold rootShift
  apply (div_le_div_iff₀ (sub_pos.mpr h₀) (sub_pos.mpr h₁)).mpr
  apply sub_nonneg.mp
  have e : (z₁-x₁)*(1-z₀)-(z₀-x₀)*(1-z₁) =
      (x₀-x₁)*(1-z₀)+(z₁-z₀)*(1-x₀) := by ring
  rw [e]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr x) (sub_nonneg.mpr h₀.le))
    (mul_nonneg (sub_nonneg.mpr z) (sub_nonneg.mpr xUnit))

private theorem one_sub_corner_r (d : CornerRow) (hd : d.Verified) :
    1-d.r K = ((d.ratioDen : K)*(d.remaining : K))/(d.rightDen : K) := by
  have e : d.breakpoint+d.remaining=64 := Nat.add_sub_of_le hd.breakpoint_le
  have e' : (d.breakpoint : K)+(d.remaining : K)=64 := by exact_mod_cast e
  have v : (0 : K) < (d.ratioDen : K) := by
    cases h : d.upper <;> norm_num [CornerRow.ratioDen,h]
  have u : 0 < d.ratioNum := by cases h : d.upper <;> simp [CornerRow.ratioNum,h]
  have vNat : 0 < d.ratioDen := Nat.cast_pos.mp v
  have rightPos : 0 < d.rightDen := by
    unfold CornerRow.rightDen
    by_cases h : d.breakpoint=0
    · have t : 0 < d.remaining := by simp [CornerRow.remaining,h]
      have hz := Nat.mul_pos vNat t
      omega
    · exact Nat.add_pos_left (Nat.mul_pos u (Nat.pos_of_ne_zero h)) _
  have rd : (d.rightDen : K) ≠ 0 := (Nat.cast_pos.mpr rightPos).ne'
  have s : 1-d.s K=(d.remaining : K)/64 := by unfold CornerRow.s; linarith only [e']
  have dEq : 1-d.s K+d.ratio K*d.s K=(d.rightDen : K)/((d.ratioDen : K)*64) := by
    rw [s]
    simp only [CornerRow.ratio,CornerRow.s,CornerRow.rightDen,Nat.cast_add,Nat.cast_mul]
    field_simp [v.ne'] <;> ring
  have rr : d.r K = ((d.ratioNum : K)*(d.breakpoint : K))/(d.rightDen : K) := by
    rw [CornerRow.r,normalizedRight,dEq]
    unfold CornerRow.ratio CornerRow.s
    field_simp [v.ne',rd] <;> ring
  rw [rr]
  field_simp [rd] <;> simp only [CornerRow.rightDen,Nat.cast_add,Nat.cast_mul] <;> ring

private theorem gamma_code_value (d : CornerRow) (hd : d.Verified) (z : ℕ) :
    (gammaCode d z).value K = (1-d.r K)*(1-(z : K)/4096) := by
  simp only [FracCode.value,gammaCode,Int.cast_mul,Int.cast_sub,Int.cast_natCast,Int.cast_ofNat]
  rw [one_sub_corner_r d hd]
  have h : (1-(z : K)/4096) = (4096-(z : K))/4096 := by
    field_simp <;> ring
  rw [h,div_mul_div_comm]

private theorem shift_code_value (z x : ℕ) (hz : (z : K)/4096 < 1) :
    (shiftCode z x).value K = rootShift ((z : K)/4096) ((x : K)/4096) := by
  have pos : (0 : K) < 4096 := by norm_num
  have lt : (z : K) < 4096 := by simpa only [one_mul] using (div_lt_iff₀ pos).mp hz
  have den : (4096 : K)-(z : K) ≠ 0 := (sub_pos.mpr lt).ne'
  simp only [FracCode.value,shiftCode,rootShift,Int.cast_sub,Int.cast_natCast,Int.cast_ofNat]
  field_simp [pos.ne',den,(sub_pos.mpr hz).ne'] <;> ring

/-- Signed cap on all six caged nodes at any coordinate in the literal
cell. The outward orientation is essential: high-corner lower endpoints
and low-corner upper endpoints are used throughout. -/
theorem cap_of_caged_nodes (p : Phase) (cell : Fin 15) (v : Fin 6 → K) {r : K}
    (rlo : (lowCellCorner cell).r K≤r) (rhi : r≤(highCellCorner cell).r K)
    (cage : ∀ i : Fin 6, (highCellCorner cell).lowerEndpoint K i < v i ∧
      v i < (lowCellCorner cell).upperEndpoint K i) :
    signedTest p ((1-r)*(1-v p.zIndex)) (rootShift (v p.zIndex) (v (p.rootIndex 0)))
      (rootShift (v p.zIndex) (v (p.rootIndex 1)))
      (rootShift (v p.zIndex) (v (p.rootIndex 2))) ≤ (capMillion p : K)/1000000 := by
  let l (j : Fin 6) : K := (highCellCorner cell).lowerEndpoint K j
  let h (j : Fin 6) : K := (lowCellCorner cell).upperEndpoint K j
  let i := p.zIndex
  obtain ⟨Wlo,Whi⟩ := cell_corner_witnesses (K := K) cell
  have h1 (j : Fin 6) : h j < 1 := (Wlo.cages.interior j).2.2
  have l1 (j : Fin 6) : l j < 1 :=
    (Whi.cages.interior j).2.1.trans (Whi.cages.interior j).2.2
  have v1 (j : Fin 6) : v j < 1 := (cage j).2.trans (h1 j)
  have rr : r≤1 := rhi.trans Whi.rUnit.2
  have gBox : (gammaLoCode p cell).value K≤(1-r)*(1-v i) ∧
      (1-r)*(1-v i)≤(gammaHiCode p cell).value K := by
    constructor
    · rw [gammaLoCode,gamma_code_value (highCellCorner cell) (cornerRow_verified (highRowIndex cell))]
      change (1-(highCellCorner cell).r K)*(1-h i)≤(1-r)*(1-v i)
      exact mul_le_mul (sub_le_sub_left rhi _) (sub_le_sub_left (cage i).2.le _)
        (sub_nonneg.mpr (h1 i).le) (sub_nonneg.mpr rr)
    · rw [gammaHiCode,gamma_code_value (lowCellCorner cell) (cornerRow_verified (lowRowIndex cell))]
      change (1-r)*(1-v i)≤(1-(lowCellCorner cell).r K)*(1-l i)
      exact mul_le_mul (sub_le_sub_left rlo _) (sub_le_sub_left (cage i).1.le _)
        (sub_nonneg.mpr (v1 i).le) (sub_nonneg.mpr Wlo.rUnit.2)
  have shiftBox (j : Fin 3) :
      (shiftLoCode p cell j).value K≤rootShift (v i) (v (p.rootIndex j)) ∧
        rootShift (v i) (v (p.rootIndex j))≤(shiftHiCode p cell j).value K := by
    constructor
    · rw [shiftLoCode,shift_code_value (betaLowerNum cell i)
        (betaUpperNum cell (p.rootIndex j)) (l1 i)]
      change rootShift (l i) (h (p.rootIndex j))≤rootShift (v i) (v (p.rootIndex j))
      exact rootShift_le (cage i).1.le (cage (p.rootIndex j)).2.le
        (l1 i) (v1 i) (h1 (p.rootIndex j)).le
    · rw [shiftHiCode,shift_code_value (betaUpperNum cell i)
        (betaLowerNum cell (p.rootIndex j)) (h1 i)]
      change rootShift (v i) (v (p.rootIndex j))≤rootShift (h i) (l (p.rootIndex j))
      exact rootShift_le (cage i).2.le (cage (p.rootIndex j)).1.le
        (v1 i) (h1 i) (v1 (p.rootIndex j)).le
  exact cap_of_code_box p cell gBox (shiftBox 0) (shiftBox 1) (shiftBox 2)

/-- The original exterior ratio parameter band supplies the second
coordinate's box for the same cell, without independent sampling. -/
theorem compact_cell_cap (p : Phase) (cell : Fin 15) (v : Fin 6 → K) {s r c : K}
    (sUnit : s ∈ Set.Icc (0 : K) 1)
    (slo : (cellBreaks cell.castSucc : K)/64≤s) (shi : s≤(cellBreaks cell.succ : K)/64)
    (clo : (2 : K)/3≤c) (chi : c≤(6 : K)/7) (param : r=normalizedRight s c)
    (cage : ∀ i : Fin 6, (highCellCorner cell).lowerEndpoint K i < v i ∧
      v i < (lowCellCorner cell).upperEndpoint K i) :
    signedTest p ((1-r)*(1-v p.zIndex)) (rootShift (v p.zIndex) (v (p.rootIndex 0)))
      (rootShift (v p.zIndex) (v (p.rootIndex 1)))
      (rootShift (v p.zIndex) (v (p.rootIndex 2))) < 0 := by
  obtain ⟨l,h⟩ := cell_corner_witnesses (K := K) cell
  obtain ⟨ls,lr⟩ := lowCellCorner_coordinates (K := K) cell
  obtain ⟨hs,hr⟩ := highCellCorner_coordinates (K := K) cell
  have slo' : (lowCellCorner cell).s K≤s := ls.symm ▸ slo
  have shi' : s≤(highCellCorner cell).s K := hs.symm ▸ shi
  have rlo : (lowCellCorner cell).r K≤r := by
    rw [lr,param,←ls]
    exact normalizedRight_mono l.sUnit sUnit slo' clo (by norm_num)
  have rhi : r≤(highCellCorner cell).r K := by
    rw [hr,param,←hs]
    exact normalizedRight_mono sUnit h.sUnit shi' chi ((by norm_num : (0 : K) < 2/3).trans_le clo)
  exact (cap_of_caged_nodes p cell v rlo rhi cage).trans_lt
    (div_neg_of_neg_of_pos (capMillion_neg p) (by norm_num))

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
