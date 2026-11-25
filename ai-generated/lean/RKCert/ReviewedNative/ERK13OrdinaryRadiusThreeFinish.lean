module

public import RKCert.ReviewedNative.ERK13OrdinaryRadiusThree
public import RKCert.ReviewedNative.ERK13OrdinaryCubicProfile
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The literal ordinary radius-three contradiction

The early payment of Cw pays each X-divisible cubic test through F6.
Only the native cubic two-port cut is needed: the true F7 chart has
length five and the three paid square shifts forced a cubic profile.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {G P Q : K[X]} {U : Submodule K (Fin 19→K)} {w : Fin 19→K}

private theorem radius_three_paid_mask (ho : HasOrder 13 A b)
    (H : OrdinaryRadiusThreeHead A U w G P Q) (R : K[X])
    (divX : (X:K[X])∣R) (degree : R.natDegree≤3) :
    evalNodes A R*w∈zeroSpace A 6 := by
  obtain ⟨T,e⟩:=divX
  have td : T.natDegree≤2 := by
    by_cases tz : T=0
    · simp [tz]
    · rw [e,natDegree_X_mul tz] at degree
      omega
  have eq : evalNodes A R*w=diag (nodes A) w*evalNodes A T := by
    rw [e]
    ext i
    simp only [Pi.mul_apply,evalNodes_apply,eval_mul,eval_X,diag_apply]
    ring
  rw [eq]
  exact zeroSpace_mul_treeSpace (m:=4) (n:=2) ho (by decide)
    H.clockHeadFour (evalNodes_mem_treeSpace A T td)

/-- The chart and the two lower head columns suffice without a
separate class-count or any quartic factor case. -/
theorem OrdinaryRadiusThreeHead.impossible (H : OrdinaryRadiusThreeHead A U w G P Q)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) : False := by
  have wstable : U.map (diag w)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    have z : diag w u=0 := by
      ext i
      by_cases uz : u i=0
      · simp only [diag_apply,uz,mul_zero,Pi.zero_apply]
      · simp only [diag_apply,H.off i ⟨u,hu,uz⟩,zero_mul,Pi.zero_apply]
    rw [z]
    exact U.zero_mem
  have fit : w*w-weightedEval (nodes A) w P∈U := by
    have eq : w*w=weightedEval (nodes A) w P := by
      ext i
      by_cases wz : w i=0
      · simp only [Pi.mul_apply,weightedEval_apply,wz,mul_zero]
      · simp only [Pi.mul_apply,weightedEval_apply]
        exact congrArg (fun t=>t*w i) (H.profile i wz)
    rw [eq,sub_self]
    exact U.zero_mem
  obtain ⟨_,pc,_⟩ := H.factor_of_eight_sites
  have sd := PolySeparated.of_coeff (coeff_separated ho (q:=6) (by decide))
  have core : U≤zeroSpace A 6 := H.coreEq.ge.trans (zeroSpace_mono A (by decide : 3≤6))
  exact ordinary_cubic_profile_impossible_of_xpaid ha sd core H.stable wstable H.gradeSeven.le
    (radius_three_paid_mask ho H) H.profileNonzero pc.le fit

/-- Actual ordinary width 19 cannot have head radius three. -/
theorem ordinary_radius_three_impossible (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G 3 U w) : False := by
  obtain ⟨v,R,S,L⟩ := ordinary_radius_three_head ha ho seed H
  exact L.impossible ha ho

end
end RKResearch.Certified.Graded.ERK13NativeFirst
