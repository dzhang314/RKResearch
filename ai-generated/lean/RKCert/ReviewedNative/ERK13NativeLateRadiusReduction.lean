module

public import RKCert.ReviewedNative.ERK13NativeRadiusTwoRanks
public import RKCert.ReviewedNative.ERK13OrdinaryCubicProfile
import RKCert.ReviewedNative.OddForwardBudget
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Earn the late native radius census on actual order-13 data

The literal grade-seven terminal absence removes the terminal coefficient
before the next-band coefficient detector is used. This proves exact F7
head coverage, which pays both actual physical cubic ports for any F3
multiplier. No ordinary, nonzero-seed staircase is invoked. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {r : ℕ} {G : K[X]}
set_option maxHeartbeats 1100000
set_option maxRecDepth 2100

theorem NativeMarkedEscapeChart.late_seven_head
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) :
    zeroSpace A 7=escapeHeadBand A U w (r+2) := by
  let B := escapeHeadBand A U w (r+2)
  have dPay : B≤zeroSpace A 7 := by
    simpa only [Nat.add_zero] using escapeHeadBand_paid_from_seven H.head 0
  refine le_antisymm ?_ dPay
  intro x hx
  have xt := zeroSpace_le_treeSpace A 7 hx
  have mark : x∈markedTreeSpace A b (6+1+0) := Submodule.mem_sup_left xt
  rw [H.chart 0 (by decide)] at mark
  obtain ⟨p,⟨a,rfl⟩,t,ht,total⟩ := Submodule.mem_sup.mp mark
  obtain ⟨v,hv,l,hl,split⟩ := Submodule.mem_sup.mp ht
  rw [terminalMark,if_pos H.seed] at hl
  obtain ⟨k,rfl⟩ := Submodule.mem_span_singleton.mp hl
  have dp : v∈zeroSpace A 7 := dPay hv
  have poly : coeffEval A 6 a∈treeSpace A 7 :=
    treeSpace_mono A (by decide : 6≤7) (coeffEval_mem_treeSpace A 6 a)
  have residual : k • coordinate (K:=K) (Fin.last 18)=x-coeffEval A 6 a-v := by
    rw [←total,←split]
    abel
  have term : k • coordinate (K:=K) (Fin.last 18)∈treeSpace A 7 := by
    rw [residual]
    exact (treeSpace A 7).sub_mem ((treeSpace A 7).sub_mem xt poly) (zeroSpace_le_treeSpace A 7 dp)
  have kz : k=0 := by
    by_contra nz
    exact late (((treeSpace A 7).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr nz)).mp term)
  rw [kz,zero_smul,add_zero] at split
  rw [←split] at total
  have z := (zeroSpace A 7).sub_mem hx dp
  rw [←total,add_sub_cancel_right] at z
  have az := coeff_separated_next (q:=6) ha ho (by decide) a z
  rw [az,map_zero,zero_add] at total
  exact total ▸ hv

/-- Only actual F7 head coverage is needed to kill a noncore low multiplier.
This version works for both first-escape widths and either terminal time. -/
theorem NativeMarkedEscapeChart.three_core_of_seven_cover {a : ℕ}
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (cover : zeroSpace A 7≤escapeHeadBand A U w (r+2)) :
    zeroSpace A 3≤U := by
  by_cases two : r=2
  · subst r
    exact fun _ hx => radius_two_grade_three_core H.head hx
  have lo := H.head.headBounds.1
  have room : 3≤r := by omega
  intro x hx
  by_contra out
  obtain ⟨stable,P,pn,pd,rel⟩ :=
    H.low_multiplier_profile ha ho (Or.inr rfl) room hx out
  exact ordinary_cubic_profile_impossible ha ho
    (PolySeparated.of_coeff (coeff_separated ho (q:=6) (by decide)))
    (H.head.head.coreInside.trans (zeroSpace_mono A (by decide : 5≤6)))
    H.head.head.coreStable stable cover hx pn pd rel

theorem NativeMarkedEscapeChart.late_three_core
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) :
    zeroSpace A 3≤U :=
  H.three_core_of_seven_cover ha ho (H.late_seven_head ha ho late).le

theorem NativeMarkedEscapeChart.late_rank_radius
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) :
    finrank K (zeroSpace A 4)=4 ∧ (r=2 ∨ r=3) ∧
      (r=3 → zeroSpace A 3=U ∧ finrank K U=2) := by
  exact rank_radius_of_three_in_core ha ho H.head (H.late_three_core ha ho late)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
