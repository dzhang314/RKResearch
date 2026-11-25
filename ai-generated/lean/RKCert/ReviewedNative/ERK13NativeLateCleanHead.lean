module

public import RKCert.ReviewedNative.ERK13NativeMarkedShiftLocality
import RKCert.ReviewedNative.NativeClockChainPeel
public import RKCert.ReviewedNative.NativeLiveCore
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Earn the late radius-two clean head on original order-13 rows

The same F4/F5/F6 flat interval as in the ordinary branch can be used
because its hypotheses concern only the true defect spaces. Here the core
product, crucially, is paid by *marked* single-clock locality. No
nonzero-first-seed hypothesis nor ordinary staircase is invoked. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w₀ : Fin 19 → K} {G : K[X]}
set_option maxHeartbeats 1100000
set_option maxRecDepth 2100

/-- Apply the flat actual flag a grade earlier; its invariant core
agrees with the given radius-two core, and the new head starts in F4. -/
theorem late_radius_two_grade_four_head (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 2 U w₀)
    (rankFour : finrank K (zeroSpace A 4)=4) :
    ∃ x, U≤zeroSpace A 4 ∧ finrank K U=3 ∧
      zeroSpace A 4=chain (diag (nodes A)) U x 1 ∧
      ∀ k, chain (diag (nodes A)) U x (k+2)=chain (diag (nodes A)) U w₀ (k+2) := by
  let D := diag (nodes A)
  have stable : U.map D≤U := H.head.head.coreStable
  have five : finrank K (zeroSpace A 5)=5 := H.head.five
  have six : finrank K (zeroSpace A 6)=6 := H.head.midpoint.middleDefects
  have base : finrank K (zeroSpace A 5)=finrank K U+2 := H.head.head.baseRank
  have uRank : finrank K U=3 := by omega
  have contour : finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 4)+2 := by omega
  obtain ⟨q,V,x,J⟩ := flat_clock_head ha (j:=4) (d:=2)
    (coeff_separated ho (q:=6) (by decide)) (by decide) (by decide) contour
  have f₄ : zeroSpace A 4=escapeHeadBand A V x q := by simpa only [Nat.add_zero] using J.flags 0 (by decide)
  have f₅ : zeroSpace A 5=escapeHeadBand A V x (q+1) := J.flags 1 (by decide)
  have f₆ : zeroSpace A 6=escapeHeadBand A V x (q+2) := J.flags 2 (by decide)
  have unpaid : (D^(q+1)) x∉escapeHeadBand A V x (q+1) := by
    intro h
    have eq : escapeHeadBand A V x (q+2)=escapeHeadBand A V x (q+1) := by
      change escapeHeadBand A V x (q+1) ⊔ (K ∙ ((D^(q+1)) x))=escapeHeadBand A V x (q+1)
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have same : zeroSpace A 6=zeroSpace A 5 := f₆.trans (eq.trans f₅.symm)
    have dim := congrArg (fun W : Submodule K (Fin 19→K)=>finrank K W) same
    rw [six,five] at dim
    omega
  have coreFour : U≤zeroSpace A 4 := by
    intro y hy
    have y5 : y∈zeroSpace A 5 := H.head.head.coreInside hy
    have cy5 : D y∈zeroSpace A 5 := H.head.head.coreInside (stable (Submodule.mem_map_of_mem hy))
    have yB : y ∈ chain (diag (nodes A)) V x (q+1) := by
      change y ∈ escapeHeadBand A V x (q+1)
      rwa [←f₅]
    have cyB : D y ∈ chain (diag (nodes A)) V x (q+1) := by
      change D y ∈ escapeHeadBand A V x (q+1)
      rwa [←f₅]
    have drop := clock_chain_drop_of_next_unpaid J.coreStable q unpaid yB cyB
    change y ∈ escapeHeadBand A V x q at drop
    rwa [←f₄] at drop
  have vu : V≤U := H.head.head.coreMaximal V J.coreStable
    (J.coreInside.trans (zeroSpace_mono A (by decide : 4≤5)))
  have uv : U≤V := J.coreMaximal U stable coreFour
  have eq : V=U := le_antisymm vu uv
  subst V
  have rankStart : finrank K (zeroSpace A 4)=finrank K U+q := J.baseRank
  have onlyOne : q=1 := by omega
  subst q
  have oldFive : zeroSpace A 5=escapeHeadBand A U w₀ 2 := by
    simpa only [Nat.add_zero] using H.head.head.flags 0 (by decide)
  have sameAtTwo : escapeHeadBand A U x 2=escapeHeadBand A U w₀ 2 := f₅.symm.trans oldFive
  refine ⟨x,coreFour,uRank,f₄,?_⟩
  intro k
  induction k with
  | zero => exact sameAtTwo
  | succ k ih =>
    rw [show k.succ+2=(k+2)+1 by omega,
      ←clock_chain_next (w:=x) stable (by omega : 0<k+2),
      ←clock_chain_next (w:=w₀) stable (by omega : 0<k+2),ih]

/-- Products of a core vector with genuine F4 are genuinely retained
in the core. The neighboring-shift purity is used on each original
clock block, with actual 4+4 tree multiplication. -/
theorem late_radius_two_core_mul_four (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 2 U w₀)
    (inside : U≤zeroSpace A 4) {u v : Fin 19→K} (hu : u∈U) (hv : v∈zeroSpace A 4) :
    u*v∈U := by
  let c := nodes A
  have stable := H.head.head.coreStable
  have mask := clock_mask_invariant (fun y (hy : y∈U) => stable (Submodule.mem_map_of_mem hy))
  let f (a : K) := blockMask c a u*v
  have inU (a : K) : f a∈U := by
    have h : f a∈zeroSpace A 8 :=
      zeroSpace_mul (m:=4) (n:=4) (inside (mask a u hu)) hv
    apply H.one_clock_local ha ho (Or.inr rfl) h (t:=a)
    intro i hi
    have he : c i≠a := hi
    simp only [f,Pi.mul_apply,blockMask,if_neg he,zero_mul]
  have eq : assembleBlocks c f=u*v := by
    funext i
    rw [assembleBlocks_apply]
    change (blockMask c (c i) u) i * v i = u i * v i
    simp [blockMask]
  exact eq ▸ assembleBlocks_mem c mask f inU

/-- The disjoint replacement is still a genuine grade-four column. All
old bands of lengths ≥2 agree, not merely their coordinate dimensions. -/
theorem late_clean_radius_two_head (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 2 U w₀) (rankFour : finrank K (zeroSpace A 4)=4) :
    ∃ w : Fin 19 → K, U≤zeroSpace A 4 ∧ finrank K U=3 ∧
      w∈zeroSpace A 4 ∧ (∀ x∈U, ∀ y∈U, x*y∈U) ∧
      (∀ i,LiveCore.live U i → w i=0) ∧
      ∀ k, escapeHeadBand A U w (k+2)=escapeHeadBand A U w₀ (k+2) := by
  obtain ⟨x,uFour,uRank,four,edge⟩ := late_radius_two_grade_four_head ha ho H rankFour
  have stable := H.head.head.coreStable
  have xFour : x∈zeroSpace A 4 := by
    rw [four]
    have m := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=x) 1).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using m
  have closed (u : Fin 19→K) (hu : u∈U) (v : Fin 19→K) (hv : v∈U) : u*v∈U :=
    late_radius_two_core_mul_four ha ho H uFour hu (uFour hv)
  have keep (u : Fin 19→K) (hu : u∈U) : u*x∈U :=
    late_radius_two_core_mul_four ha ho H uFour hu xFour
  obtain ⟨w,off,shift⟩ := HeadFiber.disjoint_rep stable closed keep
  have clean : ∀ i,LiveCore.live U i → w i=0 := off
  have common (k : ℕ) : escapeHeadBand A U w (k+2)=escapeHeadBand A U w₀ (k+2) := (shift (k+2)).trans (edge k)
  have wFour : w∈zeroSpace A 4 := by
    rw [four,←shift 1]
    have m := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using m
  exact ⟨w,uFour,uRank,wFour,closed,clean,common⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
