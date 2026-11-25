module

public import RKCert.ReviewedNative.ERK13OrdinaryGradeThreeCore
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The actual radius-three ordinary head at order thirteen

The grade-three inclusion resolves the rank/radius census. In radius three
it pays a two-term F4 chart. The square and its first two clock shifts
are F8 defects, so the six-term band pays a cubic profile. Eight actual
head clocks already force the exact factor; no additional census enters.
-/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {G : K[X]} {U : Submodule K (Fin 19→K)} {w : Fin 19→K} {r : ℕ}

/-- Lower literal flags force rank four at F4, and only radii two and
three survive. The latter consumes exactly all of F3 as its core. -/
theorem ordinary_rank_radius_reduction (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G r U w) :
    finrank K (zeroSpace A 4)=4 ∧ (r=2 ∨ r=3) ∧
      (r=3 → zeroSpace A 3=U ∧ finrank K U=2) := by
  have inside := ordinary_grade_three_le_core ha ho seed H
  have sep := coeff_separated ho (q:=6) (by decide)
  have lo3 := zeroSpace_rank_interval_of_separation (j:=1) (d:=2)
    ha sep (by decide) (by decide)
  have grow34 := zeroSpace_rank_interval_of_separation (j:=3) (d:=1)
    ha sep (by decide) (by decide)
  have grow45 := zeroSpace_rank_interval_of_separation (j:=4) (d:=1)
    ha sep (by decide) (by decide)
  change finrank K (zeroSpace A 1)+2≤finrank K (zeroSpace A 3) at lo3
  change finrank K (zeroSpace A 3)+1≤finrank K (zeroSpace A 4) at grow34
  change finrank K (zeroSpace A 4)+1≤finrank K (zeroSpace A 5) at grow45
  rw [H.paidHead.five] at grow45
  have lowU := Submodule.finrank_mono inside
  have rU := H.paidHead.head.baseRank
  rw [H.paidHead.five] at rU
  have rlo := H.paidHead.headBounds.1
  have stable := H.paidHead.head.coreStable
  have r4 : finrank K (zeroSpace A 4)=4 := by
    by_contra neq
    have f3 : finrank K (zeroSpace A 3)=2 := by omega
    have f4 : finrank K (zeroSpace A 4)=3 := by omega
    have esc : ¬(zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3 := by
      intro h
      have gain := clock_invariant_outgoing (j:=3) ha
        ((PolySeparated.of_coeff sep).mono (by decide)) le_rfl h
      change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at gain
      omega
    have eq := zeroSpace_clock_step_of_unit (n:=3)
      (show finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1 by omega) esc
    have inc : zeroSpace A 4≤U := by
      rw [eq]
      exact sup_le inside ((Submodule.map_mono inside).trans stable)
    have full : zeroSpace A 4=U :=
      Submodule.eq_of_le_of_finrank_le inc (by omega)
    have invariant : (zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := by
      simpa only [full] using stable
    have gain := clock_invariant_incoming (j:=3) ha
      ((PolySeparated.of_coeff sep).mono (by decide)) invariant
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at gain
    omega
  refine ⟨r4,by omega,fun hr=>⟨Submodule.eq_of_le_of_finrank_le inside (by omega),by omega⟩⟩

private theorem higher_same_head {w' : Fin 19→K}
    (stable : U.map (diag (nodes A))≤U)
    (three : chain (diag (nodes A)) U w' 3=chain (diag (nodes A)) U w 3)
    (n : ℕ) (hn : 3≤n) :
    chain (diag (nodes A)) U w' n=chain (diag (nodes A)) U w n := by
  have expand (k : ℕ) :
      chain (diag (nodes A)) U w' (3+k)=chain (diag (nodes A)) U w (3+k) := by
    induction k with
    | zero => exact three
    | succ k ih =>
      rw [show 3+(k+1)=(3+k)+1 by omega,
        ←clock_chain_next (w:=w') stable (by omega : 0<3+k),
        ←clock_chain_next (w:=w) stable (by omega : 0<3+k),ih]
  have num : 3+(n-3)=n := by omega
  simpa only [num] using expand (n-3)

private theorem radius_three_escape_count
    (stable : U.map (diag (nodes A))≤U)
    (E9 : treeSpace A 9=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 7)
    (E10 : treeSpace A 10=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 8)
    (r9 : finrank K (treeSpace A 9)=16) (r10 : finrank K (treeSpace A 10)=17) :
    7<(HeadFiber.escapeSites (nodes A) w U).card := by
  apply HeadFiber.more_escape_sites stable (by decide)
  intro inv
  have chainEq : chain (diag (nodes A)) U w 8=chain (diag (nodes A)) U w 7 := by
    rw [←clock_chain_next stable (by decide : 0<7),sup_eq_left.mpr inv]
  have eq : treeSpace A 9=treeSpace A 10 := by rw [E9,E10,chainEq]
  rw [eq,r10] at r9
  omega

/-- Literal radius-three forward geometry before the native cubic
primitive port. The first three square shifts are all paid. -/
structure OrdinaryRadiusThreeHead (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19→K)) (w : Fin 19→K) (G P Q : K[X]) : Prop where
  coreEq : zeroSpace A 3=U
  coreRank : finrank K U=2
  stable : U.map (diag (nodes A))≤U
  closed : ∀ u∈U, ∀ v∈U, u*v∈U
  off : ∀ i, (∃ u∈U,u i≠0) → w i=0
  gradeFour : zeroSpace A 4=chain (diag (nodes A)) U w 2
  headFour : w∈zeroSpace A 4
  clockHeadFour : diag (nodes A) w∈zeroSpace A 4
  gradeSeven : zeroSpace A 7=chain (diag (nodes A)) U w 5
  treeEight : treeSpace A 8=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 6
  treeNine : treeSpace A 9=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 7
  treeTen : treeSpace A 10=(coeffEval A 6).range⊔chain (diag (nodes A)) U w 8
  ranks : finrank K (treeSpace A 9)=16 ∧ finrank K (treeSpace A 10)=17
  square : w*w∈chain (diag (nodes A)) U w 6
  clockSquare : diag (nodes A) (w*w)∈chain (diag (nodes A)) U w 6
  clockSquareTwice : diag (nodes A) (diag (nodes A) (w*w))∈chain (diag (nodes A)) U w 6
  sites : 8≤(HeadFiber.physicalSites (nodes A) w).card
  profileNonzero : P≠0
  profileDegree : P.natDegree≤3
  profile : ∀ i,w i≠0 → w i=P.eval (nodes A i)
  meshDegree : G.natDegree=7
  meshPaid : evalNodes A G∈zeroSpace A 7
  quotientDegree : Q.natDegree≤4
  meshChart : ∃ u∈U,evalNodes A G=u+weightedEval (nodes A) w Q

/-- Recover and clean the actual two-term F4 head. The three paid
E8 square shifts give a genuine degree-at-most-three profile. -/
theorem ordinary_radius_three_head (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G 3 U w) :
    ∃ (w' : Fin 19→K) (P Q : K[X]), OrdinaryRadiusThreeHead A U w' G P Q := by
  obtain ⟨rank4,_,atThree⟩ := ordinary_rank_radius_reduction ha ho seed H
  obtain ⟨coreEq,ur⟩ := atThree rfl
  have stable := H.paidHead.head.coreStable
  have rank6 : finrank K (zeroSpace A 6)=6 := H.paidHead.midpoint.middleDefects
  have sep := coeff_separated ho (q:=6) (by decide)
  obtain ⟨t,W,f,L⟩ := flat_clock_head ha (j:=4) (d:=2) sep (by decide) (by decide)
    (by change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 4)+2; omega)
  have sameU : W=U := le_antisymm
    (H.paidHead.head.coreMaximal W L.coreStable
      (L.coreInside.trans (zeroSpace_mono A (by decide : 4≤5))))
    (L.coreMaximal U stable (coreEq.ge.trans (zeroSpace_mono A (by decide : 3≤4))))
  subst W
  have base := L.baseRank
  rw [rank4,ur] at base
  have t2 : t=2 := by omega
  subst t
  let D := diag (nodes A)
  have F4raw : zeroSpace A 4=chain D U f 2 := L.flags 0 (by decide)
  have F5raw : zeroSpace A 5=chain D U f 3 := L.flags 1 (by decide)
  have F5old : zeroSpace A 5=chain D U w 3 := H.paidHead.head.flags 0 (by decide)
  have raw (n : ℕ) (hn : 3≤n) : chain D U f n=chain D U w n :=
    higher_same_head stable (F5raw.symm.trans F5old) n hn
  have r9 := H.ranks.2.2.1
  have r10 := H.ranks.2.2.2
  have F7raw : zeroSpace A 7=chain D U f 5 := by
    rw [raw 5 (by decide)]
    exact H.headSeven
  have E9raw : treeSpace A 9=(coeffEval A 6).range⊔chain D U f 7 := by
    rw [raw 7 (by decide)]
    exact H.treeNine
  have E10raw : treeSpace A 10=(coeffEval A 6).range⊔chain D U f 8 := by
    rw [raw 8 (by decide)]
    exact H.treeTen
  have rSites := radius_three_escape_count stable E9raw E10raw r9 r10
  have enough : 5<(HeadFiber.escapeSites (nodes A) f U).card := by omega
  have f4 : f∈zeroSpace A 4 := by
    rw [F4raw]
    have hf := ((clock_chain_le_iff (T:=D) (U:=U) (w:=f) 2).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using hf
  have closed (x : Fin 19→K) (hx : x∈U) (y : Fin 19→K) (hy : y∈U) :
      x*y∈U :=
    HeadFiber.core_mul (j:=3) (k:=3) stable coreEq.ge enough
      (by rw [←F7raw]; exact zeroSpace_mono A (by decide : 6≤7))
      hx (coreEq.ge hy)
  have preserve (x : Fin 19→K) (hx : x∈U) : x*f∈U :=
    HeadFiber.core_mul (j:=3) (k:=4) stable coreEq.ge enough F7raw.le hx f4
  obtain ⟨v,off,all⟩ := HeadFiber.disjoint_rep stable closed preserve
  have clean (n : ℕ) (hn : 3≤n) : chain D U v n=chain D U w n :=
    (all n).trans (raw n hn)
  have F4 : zeroSpace A 4=chain D U v 2 := F4raw.trans (all 2).symm
  have E8 : treeSpace A 8=(coeffEval A 6).range⊔chain D U v 6 := by
    rw [clean 6 (by decide)]
    exact H.treeEight
  have E9 : treeSpace A 9=(coeffEval A 6).range⊔chain D U v 7 := by
    rw [clean 7 (by decide)]
    exact H.treeNine
  have E10 : treeSpace A 10=(coeffEval A 6).range⊔chain D U v 8 := by
    rw [clean 8 (by decide)]
    exact H.treeTen
  have F7 : zeroSpace A 7=chain D U v 5 := F7raw.trans (all 5).symm
  have v4 : v∈zeroSpace A 4 := by
    rw [F4]
    have h := ((clock_chain_le_iff (T:=D) (U:=U) (w:=v) 2).mp le_rfl).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h
  have cv4 : D v∈zeroSpace A 4 := by
    rw [F4]
    have h := ((clock_chain_le_iff (T:=D) (U:=U) (w:=v) 2).mp le_rfl).2 1 (by decide)
    simpa only [pow_one] using h
  have sqF : v*v∈zeroSpace A 8 := zeroSpace_mul (m:=4) (n:=4) v4 v4
  have csqF : D (v*v)∈zeroSpace A 8 := by
    have eq : D (v*v)=v*(D v) := by
      ext i
      simp only [D,diag_apply,Pi.mul_apply]
      ring
    rw [eq]
    exact zeroSpace_mul (m:=4) (n:=4) v4 cv4
  have csq2F : D (D (v*v))∈zeroSpace A 8 := by
    have eq : D (D (v*v))=(D v)*(D v) := by
      ext i
      simp only [D,diag_apply,Pi.mul_apply]
      ring
    rw [eq]
    exact zeroSpace_mul (m:=4) (n:=4) cv4 cv4
  have sqOld : v*v∈chain D U w 6 := ordinary_adjacent_shift_pure ha ho seed H sqF csqF
  have csqOld : D (v*v)∈chain D U w 6 := ordinary_adjacent_shift_pure ha ho seed H csqF csq2F
  have csq2Old : D (D (v*v))∈chain D U w 7 := by
    change D (D (v*v))∈chain D U w (6+1)
    rw [←clock_chain_next stable (by decide : 0<6)]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem csqOld)
  have sq : v*v∈chain D U v 6 := by
    rw [clean 6 (by decide)]
    exact sqOld
  have csq : D (v*v)∈chain D U v 6 := by
    rw [clean 6 (by decide)]
    exact csqOld
  have csq2 : D (D (v*v))∈chain D U v 6 := by
    rw [clean 6 (by decide)]
    exact ordinary_E8_within_next_band ho H (zeroSpace_le_treeSpace A 8 csq2F) csq2Old
  have many := radius_three_escape_count stable E9 E10 r9 r10
  have sites : 8≤(HeadFiber.physicalSites (nodes A) v).card :=
    (Nat.succ_le_of_lt many).trans (Finset.card_le_card HeadFiber.escape_le_physical)
  have triple (k : ℕ) (hk : k≤2) : (D^k) (v*v)∈chain D U v 6 := by
    have h : k=0∨k=1∨k=2 := by omega
    rcases h with rfl|rfl|rfl
    · simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using sq
    · simpa only [pow_one] using csq
    · simpa only [pow_two,Module.End.mul_eq_comp,LinearMap.comp_apply] using csq2
  obtain ⟨P,pd,repr⟩ := HeadFiber.multiplier_polynomial (n:=6) (d:=2) (a:=v)
    off (by omega : 6<(HeadFiber.physicalSites (nodes A) v).card) triple
  have pn : P≠0 := by
    intro pz
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<(HeadFiber.physicalSites (nodes A) v).card by omega)
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp ha
    have nz := (Finset.mem_filter.mp hi).2
    exact nz (by rw [repr i nz,pz,eval_zero])
  have dP : P.natDegree≤3 := by have h := pd.resolve_left pn; omega
  have gpOld : evalNodes A G∈chain D U w 5 := by
    simpa only [H.paidHead.escapeShape,terminalMark,if_neg seed,sup_bot_eq] using H.first.paid
  have gp : evalNodes A G∈zeroSpace A 7 := H.headSeven.symm ▸ gpOld
  obtain ⟨u,hu,Q,dQ,re⟩ := HeadFiber.exists_poly (F7 ▸ gp)
  have qd : Q.natDegree≤4 := by
    by_cases qz : Q=0
    · simp [qz]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt qz).mpr dQ)
  exact ⟨v,P,Q,{
    coreEq := coreEq
    coreRank := ur
    stable := stable
    closed := closed
    off := off
    gradeFour := F4
    headFour := v4
    clockHeadFour := cv4
    gradeSeven := F7
    treeEight := E8
    treeNine := E9
    treeTen := E10
    ranks := ⟨r9,r10⟩
    square := sq
    clockSquare := csq
    clockSquareTwice := csq2
    sites := sites
    profileNonzero := pn
    profileDegree := dP
    profile := repr
    meshDegree := H.first.degree
    meshPaid := gp
    quotientDegree := qd
    meshChart := ⟨u,hu,re⟩ }⟩

/-- A cubic profile and the paid four-degree quotient identify the
degree-seven mesh on the eight actual nonzero-head clocks. -/
theorem OrdinaryRadiusThreeHead.factor_of_eight_sites {P Q : K[X]}
    (H : OrdinaryRadiusThreeHead A U w G P Q) :
    G=P*Q ∧ P.natDegree=3 ∧ Q.natDegree=4 := by
  let S := HeadFiber.physicalSites (nodes A) w
  have size : 8≤S.card := H.sites
  obtain ⟨u,hu,mesh⟩ := H.meshChart
  have fit : G=P*Q := by
    apply eq_of_degrees_lt_of_eval_finset_eq S
    · apply degree_le_natDegree.trans_lt
      exact_mod_cast (show G.natDegree<S.card by rw [H.meshDegree]; omega)
    · apply degree_le_natDegree.trans_lt
      have d := natDegree_mul_le (p:=P) (q:=Q)
      have p := H.profileDegree
      have q := H.quotientDegree
      exact_mod_cast (show (P*Q).natDegree<S.card by omega)
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have wi := (Finset.mem_filter.mp hi).2
      have ui : u i=0 := by
        by_contra nz
        exact wi (H.off i ⟨u,hu,nz⟩)
      have e := congrFun mesh i
      rw [evalNodes_apply,Pi.add_apply,weightedEval_apply,ui,zero_add,H.profile i wi] at e
      simpa only [eval_mul,mul_comm] using e
  have gn : G≠0 := by
    intro z
    have d := H.meshDegree
    rw [z,natDegree_zero] at d
    omega
  have qn : Q≠0 := fun z=>gn (by rw [fit,z,mul_zero])
  have d := congrArg natDegree fit
  rw [H.meshDegree,natDegree_mul H.profileNonzero qn] at d
  have p := H.profileDegree
  have q := H.quotientDegree
  exact ⟨fit,by omega⟩

end
end RKResearch.Certified.Graded.ERK13NativeFirst
