module

public import RKCert.ReviewedNative.ERK13NativeMarkedPrefixPort
public import RKCert.ReviewedNative.NativeHeadMultiplier
public import RKCert.ReviewedNative.NativeClockChainPeel

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Low-grade marked multipliers on the native head

Each paid adjacent run returns its entire column list, so its final
window already covers the tail head powers. No extra E8 purity or
clock support assumption is used by this profile producer. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Matrix Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w v : Fin 19 → K} {r a : ℕ} {G : K[X]}

/-- Actual F2/F3 profiles, when there are enough initial head columns to
pay the adjacent run. The profile has degree at most the defect grade. -/
theorem NativeMarkedEscapeChart.low_multiplier_profile
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    {d : ℕ} (grade : d=2 ∨ d=3) (room : d≤r)
    (hv : v∈zeroSpace A d) (out : v∉U) :
    U.map (diag v)≤U ∧ ∃ P : K[X], P≠0 ∧ P.natDegree≤d ∧
      v*w-weightedEval (nodes A) w P∈U := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  let c := nodes A
  let D := diag c
  let j := 5+d
  have jg : j=7 ∨ j=8 := by dsimp [j]; omega
  have stable := H.head.head.coreStable
  have masks : MaskInvariant c U := clock_mask_invariant (fun u hu=>stable (Submodule.mem_map_of_mem hu))
  have vStable : U.map (diag v)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    let q (t : K) := blockMask c t u*v
    have each (t : K) : q t∈U := by
      apply H.one_clock_local ha ho jg
        (zeroSpace_mul (m:=5) (n:=d) (H.head.head.coreInside (masks t u hu)) hv) (t:=t)
      intro i hn
      simp [q,blockMask,c,hn]
    have eq : assembleBlocks c q=diag v u := by
      funext i
      rw [assembleBlocks_apply,diag_apply]
      change (blockMask c (c i) u) i*v i=v i*u i
      simp [blockMask,mul_comm]
    exact eq ▸ assembleBlocks_mem c masks q each
  have base : zeroSpace A 5=escapeHeadBand A U w r := by
    simpa only [Nat.add_zero] using H.head.head.flags 0 (by decide)
  have vin : v∈escapeHeadBand A U w r := by
    rw [←base]
    exact zeroSpace_mono A (by omega) hv
  have pay (s : ℕ) (hs : s<r) : v*((D^s) w)∈zeroSpace A j := by
    have hw := ((clock_chain_le_iff (T:=D) (U:=U) (w:=w) r).mp le_rfl).2 s hs
    change ((D^s) w)∈escapeHeadBand A U w r at hw
    rw [←base] at hw
    rw [show j=d+5 by dsimp [j]; omega]
    exact zeroSpace_mul hv hw
  have band (k : ℕ) (hk : k<r) : v*((D^k) w)∈escapeHeadBand A U w (r+d) := by
    let k₀ := min k (r-d)
    have k₁ : k₀≤k := min_le_left _ _
    have k₂ : k₀≤r-d := min_le_right _ _
    have len : k-k₀≤j-6 := by
      dsimp [k₀,j]
      by_cases little : k≤r-d
      · rw [min_eq_left little]
        omega
      · rw [min_eq_right (by omega : r-d≤k)]
        omega
    have move (i : ℕ) : (D^i) (v*((D^k₀) w))=v*((D^(i+k₀)) w) := by
      funext s
      simp only [D,HeadFiber.clock_power_value,Pi.mul_apply]
      rw [pow_add]
      ring
    have sh (i : ℕ) (hi : i≤j-6) : (D^i) (v*((D^k₀) w))∈zeroSpace A j := by
      rw [move]
      apply pay
      dsimp [j] at hi
      omega
    have x := H.adjacent_unmarked_pure ha ho jg sh (k-k₀) len
    change (D^(k-k₀)) (v*((D^k₀) w))∈escapeHeadBand A U w (r+j-5) at x
    rwa [move,show k-k₀+k₀=k by omega,show r+j-5=r+d by dsimp [j]; omega] at x
  have big := H.more_head_clocks ha ho (m:=j-(a+1)) (by omega)
  have many : r+d<(HeadFiber.escapeSites (nodes A) w U).card :=
    (show r+d≤r+2+(j-(a+1)) by dsimp [j]; omega).trans_lt big
  obtain ⟨P,nz,deg,rel⟩ := HeadFiber.multiplier_profile_of_chart stable vStable many
    H.head.head.positive band vin out
  exact ⟨vStable,P,nz,by omega,rel⟩

/-- A degree-three defect is already in the invariant core at radius two;
its two successive shifts stay in F5 and peel both head coefficients. -/
theorem radius_two_grade_three_core (H : NativePaidHead A b 2 U w)
    (hv : v∈zeroSpace A 3) : v∈U := by
  let D := diag (nodes A)
  have f5 : zeroSpace A 5=escapeHeadBand A U w 2 := by
    simpa only [Nat.add_zero] using H.head.flags 0 (by decide)
  have f6 : zeroSpace A 6=escapeHeadBand A U w 3 := H.head.flags 1 (by decide)
  have out3 : (D^3) w∉escapeHeadBand A U w 3 := f6 ▸ H.head.unpaid
  have out2 : (D^2) w∉escapeHeadBand A U w 2 := by
    intro hw
    apply out3
    rw [show D^3=D*D^2 from pow_succ' D 2,Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact escapeHeadBand_map_succ H.head.coreStable (by decide : 0<2) (Submodule.mem_map_of_mem hw)
  have out1 : (D^1) w∉escapeHeadBand A U w 1 := by
    intro hw
    apply out2
    rw [show D^2=D*D^1 from pow_succ' D 1,Module.End.mul_eq_comp,LinearMap.comp_apply]
    exact escapeHeadBand_map_succ H.head.coreStable (by decide : 0<1) (Submodule.mem_map_of_mem hw)
  have h4 : D v∈zeroSpace A 4 := diag_zeroSpace A 3 hv
  have h5 : D (D v)∈zeroSpace A 5 := diag_zeroSpace A 4 h4
  have v2 : v∈escapeHeadBand A U w 2 := f5 ▸ zeroSpace_mono A (by decide : 3≤5) hv
  have c2 : D v∈escapeHeadBand A U w 2 := f5 ▸ zeroSpace_mono A (by decide : 4≤5) h4
  have cc2 : D (D v)∈escapeHeadBand A U w 2 := f5 ▸ h5
  have v1 := clock_chain_drop_of_next_unpaid H.head.coreStable 1 out2 v2 c2
  have c1 := clock_chain_drop_of_next_unpaid H.head.coreStable 1 out2 c2 cc2
  exact clock_chain_drop_of_next_unpaid H.head.coreStable 0 out1 v1 c1

end
end RKResearch.Certified.Graded.ERK13NativeFirst
