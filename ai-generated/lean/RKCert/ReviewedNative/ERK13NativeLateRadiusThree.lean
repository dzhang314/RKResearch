module

public import RKCert.ReviewedNative.ERK13NativeLateRadiusReduction
import RKCert.ReviewedNative.NativeHeadMultiplier
import RKCert.ReviewedNative.NativeLiveCore
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Finish the late radius-three case with two original primitive knots

Only the marked E8-to-E9 step is used for the clock count. All three
square shifts are genuine F8 columns, and the marked adjacent locality
theorem moves the entire triple into the six-term original head band.
No eighth or ninth physical clock, quartic mesh quotient, or unmarked
grade-nine equality is used. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {a : ℕ}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {G : K[X]}
set_option maxHeartbeats 1300000
set_option maxRecDepth 2100

private theorem late_core_times_four
    (H : NativeMarkedEscapeChart A b a G 3 U w)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (inside : U≤zeroSpace A 4) {u v : Fin 19→K} (hu : u∈U) (hv : v∈zeroSpace A 4) :
    u*v∈U := by
  let c := nodes A
  have stable := H.head.head.coreStable
  have mask := clock_mask_invariant (fun y (hy : y∈U) => stable (Submodule.mem_map_of_mem hy))
  let f (a : K) := blockMask c a u*v
  have inU (a : K) : f a∈U := by
    have h : f a∈zeroSpace A 8 := zeroSpace_mul (m:=4) (n:=4) (inside (mask a u hu)) hv
    apply H.one_clock_local ha ho (Or.inr rfl) h (t:=a)
    intro i hi
    have he : c i≠a := hi
    simp only [f,Pi.mul_apply,blockMask,if_neg he,zero_mul]
  have eq : assembleBlocks c f=u*v := by
    funext i
    rw [assembleBlocks_apply]
    change (blockMask c (c i) u) i*v i=u i*v i
    simp [blockMask]
  exact eq ▸ assembleBlocks_mem c mask f inU

/-- A pure F7 on a radius-three chart is impossible at either first-escape
width, even when the actual endpoint already lies in E7. -/
theorem native_radius_three_impossible_of_seven_head
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b a G 3 U w)
    (shape : zeroSpace A 7=escapeHeadBand A U w 5) : False := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  obtain ⟨rank4,_,atThree⟩ :=
    rank_radius_of_three_in_core ha ho H.head (H.three_core_of_seven_cover ha ho shape.le)
  obtain ⟨coreEq,ur⟩ := atThree rfl
  have stable := H.head.head.coreStable
  have rank6 : finrank K (zeroSpace A 6)=6 := H.head.midpoint.middleDefects
  have sep := coeff_separated ho (q:=6) (by decide)
  obtain ⟨t,W,f,L⟩ := flat_clock_head ha (j:=4) (d:=2) sep (by decide) (by decide)
    (by change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 4)+2; omega)
  have coreFour := coreEq.ge.trans (zeroSpace_mono A (by decide : 3≤4))
  have sameU : W=U := le_antisymm
    (H.head.head.coreMaximal W L.coreStable (L.coreInside.trans (zeroSpace_mono A (by decide : 4≤5))))
    (L.coreMaximal U stable coreFour)
  subst W
  have base := L.baseRank
  rw [rank4,ur] at base
  have t2 : t=2 := by omega
  subst t
  let D := diag (nodes A)
  have f4raw : zeroSpace A 4=chain D U f 2 := L.flags 0 (by decide)
  have f5raw : zeroSpace A 5=chain D U f 3 := L.flags 1 (by decide)
  have f5old : zeroSpace A 5=chain D U w 3 := H.head.head.flags 0 (by decide)
  have raw (k : ℕ) : chain D U f (k+3)=chain D U w (k+3) := by
    induction k with
    | zero => exact f5raw.symm.trans f5old
    | succ k ih =>
      rw [show k.succ+3=(k+3)+1 by omega,
        ←clock_chain_next (w:=f) stable (by omega : 0<k+3),
        ←clock_chain_next (w:=w) stable (by omega : 0<k+3),ih]
  have f4 : f∈zeroSpace A 4 := by
    rw [f4raw]
    have h := ((clock_chain_le_iff (T:=D) (U:=U) (w:=f) 2).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h
  have closed (x : Fin 19→K) (hx : x∈U) (y : Fin 19→K) (hy : y∈U) : x*y∈U :=
    late_core_times_four H ha ho coreFour hx (coreFour hy)
  have preserve (x : Fin 19→K) (hx : x∈U) : x*f∈U :=
    late_core_times_four H ha ho coreFour hx f4
  obtain ⟨v,off,all⟩ := HeadFiber.disjoint_rep stable closed preserve
  have clean (k : ℕ) : chain D U v (k+3)=chain D U w (k+3) :=
    (all (k+3)).trans (raw k)
  have F4 : zeroSpace A 4=chain D U v 2 := f4raw.trans (all 2).symm
  have F7 : zeroSpace A 7=chain D U v 5 := shape.trans (clean 2).symm
  have v4 : v∈zeroSpace A 4 := by
    rw [F4]
    have h := ((clock_chain_le_iff (T:=D) (U:=U) (w:=v) 2).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h
  have cv4 : D v∈zeroSpace A 4 := by
    rw [F4]
    have h := ((clock_chain_le_iff (T:=D) (U:=U) (w:=v) 2).mp le_rfl).2 1 (by decide)
    simpa only [pow_one] using h
  have sq : v*v∈zeroSpace A 8 := zeroSpace_mul (m:=4) (n:=4) v4 v4
  have csq : D (v*v)∈zeroSpace A 8 := by
    have e : D (v*v)=v*(D v) := by ext i; simp only [D,diag_apply,Pi.mul_apply]; ring
    rw [e]
    exact zeroSpace_mul (m:=4) (n:=4) v4 cv4
  have ccsq : D (D (v*v))∈zeroSpace A 8 := by
    have e : D (D (v*v))=(D v)*(D v) := by ext i; simp only [D,diag_apply,Pi.mul_apply]; ring
    rw [e]
    exact zeroSpace_mul (m:=4) (n:=4) cv4 cv4
  have shifts (i : ℕ) (hi : i≤2) : (D^i) (v*v)∈zeroSpace A 8 := by
    have steps : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases steps with rfl|rfl|rfl
    · simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using sq
    · simpa only [pow_one] using csq
    · simpa only [pow_two,Module.End.mul_eq_comp,LinearMap.comp_apply] using ccsq
  have triple (i : ℕ) (hi : i≤2) : (D^i) (v*v)∈chain D U v 6 := by
    have old : (D^i) (v*v)∈chain D U w 6 :=
      H.adjacent_unmarked_pure ha ho (j:=8) (Or.inr rfl) shifts i hi
    have eq : chain D U v 6=chain D U w 6 := clean 3
    rwa [eq]
  have escape : ¬(chain D U v 6).map D≤chain D U v 6 := by
    intro inv
    have eq : chain D U v 7=chain D U v 6 :=
      (clock_chain_next (w:=v) stable (by decide : 0<6)).symm.trans (sup_eq_left.mpr inv)
    have old : chain D U w 7=chain D U w 6 := (clean 4).symm.trans (eq.trans (clean 3))
    have h8 := H.chart 1 (by omega)
    have h9 := H.chart 2 (by omega)
    change markedTreeSpace A b (a+1+1)=(coeffEval A a).range⊔(chain D U w 6⊔terminalMark A b) at h8
    change markedTreeSpace A b (a+1+2)=(coeffEval A a).range⊔(chain D U w 7⊔terminalMark A b) at h9
    have marked : markedTreeSpace A b (a+1+2)=markedTreeSpace A b (a+1+1) := by rw [h9,h8,old]
    have ranks := (marked_staircase_ranks13 ha ho H.head H.seed).1
    have bad := congrArg (fun T : Submodule K (Fin 19→K)=>finrank K T) marked
    rw [ranks (a+1+2) (by omega) (by omega),ranks (a+1+1) (by omega) (by omega)] at bad
    omega
  have many := HeadFiber.more_escape_sites (n:=6) stable (by decide) escape
  have sites : 6<(HeadFiber.physicalSites (nodes A) v).card :=
    lt_of_lt_of_le many (Finset.card_le_card HeadFiber.escape_le_physical)
  obtain ⟨P,deg,repr⟩ := HeadFiber.multiplier_polynomial (n:=6) (d:=2) (a:=v) off sites triple
  have pn : P≠0 := by
    intro pz
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<(HeadFiber.physicalSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp ha
    have nz := (Finset.mem_filter.mp hi).2
    exact nz (by rw [repr i nz,pz,eval_zero])
  have pd : P.natDegree≤3 := by have bound := deg.resolve_left pn; omega
  have vStable : U.map (diag v)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    have z : diag v u=0 := by
      ext i
      by_cases uz : u i=0
      · simp only [diag_apply,uz,mul_zero,Pi.zero_apply]
      · simp only [diag_apply,off i ⟨u,hu,uz⟩,zero_mul,Pi.zero_apply]
    rw [z]
    exact U.zero_mem
  have fit : v*v-weightedEval (nodes A) v P∈U := by
    have eq : v*v=weightedEval (nodes A) v P := by
      ext i
      by_cases vz : v i=0
      · simp only [Pi.mul_apply,weightedEval_apply,vz,mul_zero]
      · simp only [Pi.mul_apply,weightedEval_apply]
        exact congrArg (fun t=>t*v i) (repr i vz)
    rw [eq,sub_self]
    exact U.zero_mem
  have prod (R : K[X]) (divX : (X:K[X])∣R) (rd : R.natDegree≤3) : evalNodes A R*v∈zeroSpace A 6 := by
    obtain ⟨T,e⟩ := divX
    have td : T.natDegree≤2 := by
      by_cases tz : T=0
      · simp [tz]
      · rw [e,natDegree_X_mul tz] at rd
        omega
    have eq : evalNodes A R*v=D v*evalNodes A T := by
      rw [e]
      ext i
      simp only [D,Pi.mul_apply,evalNodes_apply,eval_mul,eval_X,diag_apply]
      ring
    rw [eq]
    exact zeroSpace_mul_treeSpace (m:=4) (n:=2) ho (by decide) cv4 (evalNodes_mem_treeSpace A T td)
  exact ordinary_cubic_profile_impossible_of_xpaid ha (PolySeparated.of_coeff sep)
    (coreFour.trans (zeroSpace_mono A (by decide : 4≤6))) stable vStable F7.le prod pn pd fit

theorem NativeMarkedEscapeChart.radius_two_of_seven_head {r : ℕ}
    (H : NativeMarkedEscapeChart A b a G r U w) (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (shape : zeroSpace A 7=escapeHeadBand A U w (r+2)) :
    r=2 := by
  obtain ⟨_,rad,_⟩ :=
    rank_radius_of_three_in_core ha ho H.head (H.three_core_of_seven_cover ha ho shape.le)
  rcases rad with two | rfl
  · exact two
  · exact (native_radius_three_impossible_of_seven_head ha ho H shape).elim

theorem native_late_radius_three_impossible
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (H : NativeMarkedEscapeChart A b 6 G 3 U w)
    (late : coordinate (K:=K) (Fin.last 18)∉treeSpace A 7) : False :=
  native_radius_three_impossible_of_seven_head ha ho H (H.late_seven_head ha ho late)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
