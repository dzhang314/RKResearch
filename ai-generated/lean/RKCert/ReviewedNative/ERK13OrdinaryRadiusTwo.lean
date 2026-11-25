module

public import RKCert.ReviewedNative.ERK13OrdinaryShiftPurity
public import RKCert.ReviewedNative.ERK13OrdinarySquareClasses
public import RKCert.ReviewedNative.ERK13OrdinaryFirstPortCubic
import RKCert.ReviewedNative.NativeClockChainPeel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exclude the ordinary order-13 radius-two rank-four chart

A new grade-four representative is earned inside the actual F4.
The ordinary adjacent-shift purity theorem localizes products with
the invariant core, paying the disjoint representative there. The
finite class terminal pays the leading cancellation, the original-row
transport pays full square purity, and the checked first ports then
exclude both placements of the origin factor.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w₀ : Fin 19→K} {G : K[X]}
set_option maxHeartbeats 1100000
set_option maxRecDepth 2100

private abbrev B (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19→K)) (w : Fin 19→K) (n : ℕ) :=
  chain (diag (nodes A)) U w n

/-- Apply the flat actual flag a grade earlier; its invariant core
agrees with the given radius-two core, and the new head starts in F4. -/
theorem radius_two_grade_four_head (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : OrdinaryStaircase A b G 2 U w₀)
    (rankFour : finrank K (zeroSpace A 4)=4) :
    ∃ x, U≤zeroSpace A 4 ∧ finrank K U=3 ∧
      zeroSpace A 4=chain (diag (nodes A)) U x 1 ∧
      ∀ k, chain (diag (nodes A)) U x (k+2)=chain (diag (nodes A)) U w₀ (k+2) := by
  let D := diag (nodes A)
  have stable : U.map D≤U := H.paidHead.head.coreStable
  have five : finrank K (zeroSpace A 5)=5 := H.paidHead.five
  have six : finrank K (zeroSpace A 6)=6 := H.paidHead.midpoint.middleDefects
  have base : finrank K (zeroSpace A 5)=finrank K U+2 := H.paidHead.head.baseRank
  have uRank : finrank K U=3 := by omega
  have contour : finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 4)+2 := by omega
  obtain ⟨q,V,x,J⟩ := flat_clock_head ha (j:=4) (d:=2)
    (coeff_separated ho (q:=6) (by decide)) (by decide) (by decide) contour
  have f₄ : zeroSpace A 4=B A V x q := by simpa only [Nat.add_zero] using J.flags 0 (by decide)
  have f₅ : zeroSpace A 5=B A V x (q+1) := J.flags 1 (by decide)
  have f₆ : zeroSpace A 6=B A V x (q+2) := J.flags 2 (by decide)
  have unpaid : (D^(q+1)) x∉B A V x (q+1) := by
    intro h
    have eq : B A V x (q+2)=B A V x (q+1) := by
      change B A V x (q+1) ⊔ (K ∙ ((D^(q+1)) x))=B A V x (q+1)
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have same : zeroSpace A 6=zeroSpace A 5 := f₆.trans (eq.trans f₅.symm)
    have dim := congrArg (fun W : Submodule K (Fin 19→K)=>finrank K W) same
    rw [six,five] at dim
    omega
  have coreFour : U≤zeroSpace A 4 := by
    intro y hy
    have y5 : y∈zeroSpace A 5 := H.paidHead.head.coreInside hy
    have cy5 : D y∈zeroSpace A 5 := H.paidHead.head.coreInside (stable (Submodule.mem_map_of_mem hy))
    have yB : y ∈ chain (diag (nodes A)) V x (q+1) := by
      change y ∈ B A V x (q+1)
      rwa [←f₅]
    have cyB : D y ∈ chain (diag (nodes A)) V x (q+1) := by
      change D y ∈ B A V x (q+1)
      rwa [←f₅]
    have drop := clock_chain_drop_of_next_unpaid J.coreStable q unpaid yB cyB
    change y ∈ B A V x q at drop
    rwa [←f₄] at drop
  have vu : V≤U := H.paidHead.head.coreMaximal V J.coreStable
    (J.coreInside.trans (zeroSpace_mono A (by decide : 4≤5)))
  have uv : U≤V := J.coreMaximal U stable coreFour
  have eq : V=U := le_antisymm vu uv
  subst V
  have rankStart : finrank K (zeroSpace A 4)=finrank K U+q := J.baseRank
  have onlyOne : q=1 := by omega
  subst q
  have oldFive : zeroSpace A 5=B A U w₀ 2 := by
    simpa only [Nat.add_zero] using H.paidHead.head.flags 0 (by decide)
  have sameAtTwo : B A U x 2=B A U w₀ 2 := f₅.symm.trans oldFive
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
theorem radius_two_core_mul_four (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b≠0) (H : OrdinaryStaircase A b G 2 U w₀)
    (inside : U≤zeroSpace A 4) {u v : Fin 19→K} (hu : u∈U) (hv : v∈zeroSpace A 4) :
    u*v∈U := by
  let c := nodes A
  have stable := H.paidHead.head.coreStable
  have mask := clock_mask_invariant (fun y (hy : y∈U) => stable (Submodule.mem_map_of_mem hy))
  let f (a : K) := blockMask c a u*v
  have inU (a : K) : f a∈U := by
    have h : f a∈zeroSpace A 8 :=
      zeroSpace_mul (m:=4) (n:=4) (inside (mask a u hu)) hv
    apply ordinary_grade_eight_clock_local ha ho seed H h (a:=a)
    intro i hi
    have he : c i≠a := hi
    simp only [f,Pi.mul_apply,blockMask,if_neg he,zero_mul]
  have eq : assembleBlocks c f=u*v := by
    funext i
    rw [assembleBlocks_apply]
    change (blockMask c (c i) u) i * v i = u i * v i
    simp [blockMask]
  exact eq ▸ assembleBlocks_mem c mask f inU

private theorem seven_physical_sites_of_adjacent_charts {w : Fin 19→K}
    (stable : U.map (diag (nodes A))≤U)
    (nine : treeSpace A 9=(coeffEval A 6).range⊔B A U w 6)
    (ten : treeSpace A 10=(coeffEval A 6).range⊔B A U w 7)
    (r₉ : finrank K (treeSpace A 9)=16) (r₁₀ : finrank K (treeSpace A 10)=17) :
    7≤(HeadFiber.physicalSites (nodes A) w).card := by
  have move : ¬(B A U w 6).map (diag (nodes A))≤B A U w 6 := by
    intro inv
    have same : B A U w 7=B A U w 6 :=
      (clock_chain_next (w:=w) stable (by decide : 0<6)).symm.trans (sup_eq_left.mpr inv)
    have eq : treeSpace A 10=treeSpace A 9 := by rw [ten,nine,same]
    have d := congrArg (fun W : Submodule K (Fin 19→K)=>finrank K W) eq
    rw [r₁₀,r₉] at d
    omega
  have escape := HeadFiber.more_escape_sites (n:=6) stable (by decide) move
  exact (Nat.succ_le_of_lt escape).trans (Finset.card_le_card HeadFiber.escape_le_physical)

/-- Actual clean quartic packet. The original head is allowed to
change by its invariant core. No independent eight-grade square,
core closure, physical-clock count, or projection is assumed. -/
theorem clean_head_of_radius_two_four (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b≠0) (H : OrdinaryStaircase A b G 2 U w₀)
    (rankFour : finrank K (zeroSpace A 4)=4) :
    ∃ w R Q, ERK13OrdinaryFirstPort.CleanHead A U w G R Q := by
  obtain ⟨x,uFour,uRank,four,edge⟩ := radius_two_grade_four_head ha ho H rankFour
  have stable := H.paidHead.head.coreStable
  have xFour : x∈zeroSpace A 4 := by
    rw [four]
    have m := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=x) 1).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using m
  have closed (u : Fin 19→K) (hu : u∈U) (v : Fin 19→K) (hv : v∈U) : u*v∈U :=
    radius_two_core_mul_four ha ho seed H uFour hu (uFour hv)
  have keep (u : Fin 19→K) (hu : u∈U) : u*x∈U :=
    radius_two_core_mul_four ha ho seed H uFour hu xFour
  obtain ⟨w,off,shift⟩ := HeadFiber.disjoint_rep stable closed keep
  have clean : ∀ i,LiveCore.live U i → w i=0 := off
  have common (k : ℕ) : B A U w (k+2)=B A U w₀ (k+2) := (shift (k+2)).trans (edge k)
  have wFour : w∈zeroSpace A 4 := by
    rw [four,←shift 1]
    have m := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using m
  have f₇ : zeroSpace A 7=B A U w 4 := H.headSeven.trans (common 2).symm
  have t₈ : treeSpace A 8=(coeffEval A 6).range⊔B A U w 5 := by rw [common 3]; exact H.treeEight
  have t₉ : treeSpace A 9=(coeffEval A 6).range⊔B A U w 6 := by rw [common 4]; exact H.treeNine
  have t₁₀ : treeSpace A 10=(coeffEval A 6).range⊔B A U w 7 := by rw [common 5]; exact H.treeTen
  have oldMesh : evalNodes A G∈B A U w₀ 4 := by
    simpa only [H.paidHead.escapeShape,terminalMark,if_neg seed,sup_bot_eq] using H.first.paid
  have newMesh : evalNodes A G∈B A U w 4 := (common 2).symm ▸ oldMesh
  have gPaid : evalNodes A G∈zeroSpace A 7 := f₇.symm ▸ newMesh
  have gd : G.natDegree=7 := H.first.degree
  have band : B A U w 5≤zeroSpace A 8 := by
    change chain (diag (nodes A)) U w 5≤zeroSpace A 8
    have h7 : zeroSpace A 7 = chain (diag (nodes A)) U w 4 := f₇
    rw [←clock_chain_next (w:=w) stable (by decide : 0<4), ←h7]
    exact sup_le (zeroSpace_mono A (by decide : 7≤8))
      (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 7))
  have squarePaid : w*w∈zeroSpace A 8 := zeroSpace_mul wFour wFour
  obtain ⟨P,R,Q,u,v,hu,hv,pd,rd,qd,pPay,square,mesh⟩ :=
    ERK13OrdinarySquare.charts_of_paid_square t₈ band squarePaid newMesh
  have top := ERK13OrdinarySquare.ordinary_clock_top_impossible ha ho stable closed clean
    uFour wFour uRank H.ranks.2.2.1 H.ranks.2.2.2 t₉ t₁₀ hu hv square mesh gd pd rd qd gPaid
  have direct : ∀ Z : K[X], Z.natDegree≤6 → evalNodes A Z∈B A U w 7 → Z=0 :=
    ERK13OrdinarySquare.direct_polynomial_band ho uRank t₁₀ H.ranks.2.2.2
  have law := ERK13OrdinarySquare.transport stable clean hu hv square mesh
  have divide := ERK13OrdinarySquare.mesh_dvd_square_times_q stable direct newMesh gd pd qd rd law top
  have gn : G≠0 := by intro e; rw [e,natDegree_zero] at gd; omega
  have gTop : G.coeff 7≠0 := by
    rw [←gd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr gn
  have qn : Q≠0 := fun q0=>gTop (by simpa only [q0,mul_zero,sub_zero] using top)
  have p0 := ERK13OrdinarySquare.zero_projection_of_divides (m:=18) ha ho pPay gPaid gd pd qd qn divide
  have pureSquare : w*w=weightedEval (nodes A) w R+u := by
    simpa only [p0,map_zero,zero_add] using square
  have sites := seven_physical_sites_of_adjacent_charts stable t₉ t₁₀ H.ranks.2.2.1 H.ranks.2.2.2
  obtain ⟨degreeR,degreeQ,factor,amp⟩ :=
    ERK13OrdinarySquare.factor_on_seven clean hu hv pureSquare mesh gd qd rd top sites
  exact ⟨w,R,Q,⟨uFour,stable,closed,wFour,clean,amp,f₇.le,gPaid,gd,degreeR,degreeQ,factor⟩⟩

/-- The nonzero-first-seed native width-19 case cannot have radius two
and a four-dimensional F4. All clean-head hypotheses are produced. -/
theorem ordinary_radius_two_four_impossible (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b≠0) (H : OrdinaryStaircase A b G 2 U w₀)
    (rankFour : finrank K (zeroSpace A 4)=4) : False := by
  obtain ⟨_,_,_,packet⟩ := clean_head_of_radius_two_four ha ho seed H rankFour
  exact packet.impossible ha ho

/-- Convenience for dispatch on the actual radius returned by the paid
ordinary staircase. This is not a classification of the other radii. -/
theorem ordinary_radius_not_two_of_four (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (seed : firstSeed A b≠0) {r : ℕ} (H : OrdinaryStaircase A b G r U w₀)
    (rankFour : finrank K (zeroSpace A 4)=4) : r≠2 := by
  rintro rfl
  exact ordinary_radius_two_four_impossible ha ho seed H rankFour

end
end RKResearch.Certified.Graded.ERK13NativeFirst
