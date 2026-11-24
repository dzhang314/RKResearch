module

public import RKCert.ReviewedNative.ERKOrderTwelveSingleLeak

public section

/-! # The exact physical profile of the remaining order-twelve chart

The true rank-(2,4) split uses a disjoint head on the original stage
set and one leakage scalar. Its degree-two terminal profile and
degree-four square profile are observed on all off-core rows.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Polynomial Module Reverse RKCert.OneEscape RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- The two physical profile equations of the last width-seventeen
branch. No exact support or distinct-clock premise is assumed. -/
structure RankTwoFourProfile (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (U : Submodule K (Fin (s+1) → K)) (z : Fin (s+1) → K) (α : K) (Q R : K[X]) : Prop where
  coreRank : finrank K U=3
  stable : U.map (diag (nodes A))≤U
  closed : ∀ u∈U, ∀ v∈U, u*v∈U
  disjoint : ∀ i, LiveCore.live U i → z i=0
  fourth : zeroSpace A 4=chain (diag (nodes A)) U z 1
  sixth : zeroSpace A 6=chain (diag (nodes A)) U z 3
  eighth : treeSpace A 8=clockBand6 A⊔chain (diag (nodes A)) U z 5
  top : clockBand6 A⊔chain (diag (nodes A)) U z 7=⊤
  many : 7≤(HeadFiber.physicalSites (nodes A) z).card
  lastZero : z (Fin.last s)=0
  qDegree : Q.natDegree≤2
  rDegree : R.natDegree≤4
  mesh : ∀ i, ¬LiveCore.live U i →
    (terminalMesh6 : K[X]).eval (nodes A i)=coordinate (K:=K) (Fin.last s) i+z i*Q.eval (nodes A i)
  square : ∀ i, ¬LiveCore.live U i →
    (z i)^2=α*(terminalLeak8 : K[X]).eval (nodes A i)+z i*R.eval (nodes A i)

private theorem bounded_natDegree {P : K[X]} {n : ℕ} (pos : 0<n)
    (deg : P.degree<(n:WithBot ℕ)) : P.natDegree≤n-1 := by
  by_cases z : P=0
  · simp [z]
  · have d := (natDegree_lt_iff_degree_lt z).mpr deg
    omega

theorem RankTwoFourProfile.coreInside
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) : U≤zeroSpace A 4 :=
  ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=z) 1).mp H.fourth.ge).1

theorem RankTwoFourProfile.headInFour
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) : z∈zeroSpace A 4 := by
  have h := ((clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=z) 1).mp H.fourth.ge).2 0 (by decide)
  simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h

theorem RankTwoFourProfile.mesh_on_head
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) {i : Fin (s+1)} (nz : z i≠0) :
    (terminalMesh6 : K[X]).eval (nodes A i)=z i*Q.eval (nodes A i) := by
  classical
  have off : ¬LiveCore.live U i := fun e => nz (H.disjoint i e)
  have nlast : i≠Fin.last s := fun e => nz (e.symm ▸ H.lastZero)
  have zero : coordinate (K:=K) (Fin.last s) i=0 := by simp [coordinate,nlast]
  simpa only [zero,zero_add] using H.mesh i off

variable [CharZero K]

set_option maxHeartbeats 650000 in
/-- Construct the actual disjoint profile from the measured native chart. -/
theorem rank_two_four_profile (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) (T : TerminalBand A b)
    {U : Submodule K (Fin (s+1) → K)} {w : Fin (s+1) → K}
    (H : ForwardStaircase A 2 U w) (d4 : finrank K (zeroSpace A 4)=4) :
    ∃ z α Q R, RankTwoFourProfile A U z α Q R := by
  classical
  let D := diag (nodes A)
  have shape : zeroSpace A 4=chain D U w 1 := grade_four_of_rank_four S H d4
  have e := (clock_chain_le_iff (T:=D) (U:=U) (w:=w) 1).mp shape.ge
  have core : U≤zeroSpace A 4 := e.1
  have w4 : w∈zeroSpace A 4 := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using e.2 0 (by decide)
  have mul (u : Fin (s+1) → K) (hu : u∈U) (v : Fin (s+1) → K) (hv : v∈zeroSpace A 4) :
      u*v∈U := by
    have keep := grade_eight_multiplier_stable ha ho S T H core (by decide) hv
    have e : diag v u=u*v := by ext i; simp [mul_comm]
    exact e ▸ keep (Submodule.mem_map_of_mem hu)
  have closed (u : Fin (s+1) → K) (hu : u∈U) (v : Fin (s+1) → K) (hv : v∈U) : u*v∈U :=
    mul u hu v (core hv)
  obtain ⟨z,dis,agree⟩ := HeadFiber.disjoint_rep H.initial.coreStable closed
    (fun u hu => mul u hu w w4)
  have f4 : zeroSpace A 4=chain D U z 1 := shape.trans (agree 1).symm
  have f6 : zeroSpace A 6=chain D U z 3 :=
    (show zeroSpace A 6=chain D U w 3 from H.initial.flags 1 (by decide)).trans (agree 3).symm
  have e8 : treeSpace A 8=clockBand6 A⊔chain D U z 5 := by
    rw [agree 5]
    exact (H.bands 1 (by decide)).1
  have e9 : treeSpace A 9=clockBand6 A⊔chain D U z 6 := by
    rw [agree 6]
    exact (H.bands 2 (by decide)).1
  have e10 : treeSpace A 10=clockBand6 A⊔chain D U z 7 := by
    rw [agree 7]
    exact (H.bands 3 (by decide)).1
  have escape : ¬(chain D U z 6).map D≤chain D U z 6 := by
    intro inv
    have flat : chain D U z 7=chain D U z 6 := by
      rw [show 7=6+1 by decide,←clock_chain_next H.initial.coreStable (w:=z) (n:=6) (by decide)]
      exact sup_eq_left.mpr inv
    have collapse : treeSpace A 10=treeSpace A 9 := by rw [e10,e9,flat]
    have rank := congrArg (fun V : Submodule K (Fin (s+1) → K) => finrank K V) collapse
    change finrank K (treeSpace A 10)=finrank K (treeSpace A 9) at rank
    rw [show finrank K (treeSpace A 10)=17 from (H.bands 3 (by decide)).2,
      show finrank K (treeSpace A 9)=16 from (H.bands 2 (by decide)).2] at rank
    omega
  have many := HeadFiber.more_escape_sites H.initial.coreStable (w:=z) (n:=6) (by decide) escape
  have physical := Finset.card_le_card
    (HeadFiber.escape_le_physical (c:=nodes A) (w:=z) (U:=U))
  have z4 : z∈zeroSpace A 4 := by
    have q := ((clock_chain_le_iff (T:=D) (U:=U) (w:=z) 1).mp f4.ge).2 0 (by decide)
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using q
  have zend := grade_five_zero_at_terminal ho S (zeroSpace_mono A (by decide : 4≤5) z4)
  have zsq : z*z∈zeroAt (zeroSpace A 8) (Fin.last s) :=
    mem_zeroAt.mpr ⟨zeroSpace_mul z4 z4,by rw [Pi.mul_apply,zend,zero_mul]⟩
  have cut : chain D U z 4=zeroAt (zeroSpace A 7) (Fin.last s) :=
    (agree 4).trans (H.cut.symm.trans T.cut)
  have end8 : chain D U z 5≤zeroAt (zeroSpace A 8) (Fin.last s) := by
    rw [show 5=4+1 by decide,←clock_chain_next H.initial.coreStable (w:=z) (n:=4) (by decide),cut]
    exact zeroAt_clock_next A 7 _
  obtain ⟨α,leak⟩ := grade_eight_single_leak ha ho S e8 end8 zsq
  have m : coordinate (K:=K) (Fin.last s)-evalNodes A terminalMesh6∈chain D U z 3 :=
    f6 ▸ physical_terminal_mesh ha ho S
  obtain ⟨u,hu,P,pd,pval⟩ := HeadFiber.exists_poly m
  obtain ⟨v,hv,R,rd,rval⟩ := HeadFiber.exists_poly leak
  have dr := bounded_natDegree (by decide : 0<5) rd
  have dq := bounded_natDegree (by decide : 0<3) pd
  have base := H.initial.baseRank
  change finrank K (zeroSpace A 5)=finrank K U+2 at base
  rw [S.f5] at base
  refine ⟨z,α,-P,R,⟨by omega,H.initial.coreStable,closed,dis,f4,f6,e8,
    e10.symm.trans H.top,by omega,zend,by simpa only [natDegree_neg] using dq,dr,?_,?_⟩⟩
  · intro i off
    have e := congrFun pval i
    simp only [Pi.sub_apply,Pi.add_apply,evalNodes_apply,weightedEval_apply] at e
    rw [LiveCore.val_eq_zero_of_not_live off hu,zero_add] at e
    rw [eval_neg]
    linear_combination -e
  · intro i off
    have e := congrFun rval i
    simp only [Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,Pi.add_apply,
      evalNodes_apply,weightedEval_apply] at e
    rw [LiveCore.val_eq_zero_of_not_live off hv,zero_add] at e
    rw [pow_two]
    linear_combination e

/-- In the pure case the observed terminal and square profiles are a
genuine polynomial factorization, not just fits on sampled clocks. -/
theorem RankTwoFourProfile.pure_factor
    {U : Submodule K (Fin (s+1) → K)} {z : Fin (s+1) → K} {α : K} {Q R : K[X]}
    (H : RankTwoFourProfile A U z α Q R) (pure : α=0) :
    terminalMesh6=R*Q ∧ R.natDegree=4 ∧ Q.natDegree=2 ∧
      ∀ i, z i≠0 → z i=R.eval (nodes A i) := by
  classical
  have head (i : Fin (s+1)) (nz : z i≠0) : z i=R.eval (nodes A i) := by
    have off : ¬LiveCore.live U i := fun h => nz (H.disjoint i h)
    have eq := H.square i off
    rw [pure,zero_mul,zero_add,pow_two] at eq
    exact mul_left_cancel₀ nz eq
  have dm := terminalMesh6_natDegree_eq (K:=K)
  have dp := H.rDegree
  have dq := H.qDegree
  have ct := H.many
  have eq : (terminalMesh6 : K[X])=R*Q := by
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (HeadFiber.physicalSites (nodes A) z)
    · apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast (show (terminalMesh6 : K[X]).natDegree<
        (HeadFiber.physicalSites (nodes A) z).card by omega)
    · have d : (R*Q).natDegree≤6 := natDegree_mul_le.trans (by omega)
      apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast (show (R*Q).natDegree<(HeadFiber.physicalSites (nodes A) z).card by omega)
    · intro y hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
      have nz := (Finset.mem_filter.mp hi).2
      rw [eval_mul,H.mesh_on_head nz,head i nz]
  have m0 : (terminalMesh6 : K[X])≠0 := by intro e; simp [e] at dm
  have nz : R*Q≠0 := eq ▸ m0
  have parts := mul_ne_zero_iff.mp nz
  have sum : R.natDegree+Q.natDegree=6 := by rwa [eq,natDegree_mul parts.1 parts.2] at dm
  exact ⟨eq,by omega,by omega,head⟩

/-- From native strict order and the width cap, the last chart has a
single possible terminal-zero leakage scalar, with an exact factor pair
in its pure alternative. -/
theorem actual_rank_two_four_profile (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 12 A b) (cap : s+1≤17) :
    ∃ U z α Q R, RankTwoFourProfile A U z α Q R ∧
      (α≠0 ∨ (α=0 ∧ terminalMesh6=R*Q ∧ R.natDegree=4 ∧ Q.natDegree=2)) := by
  have S := saturation_of_order ha ho cap
  have T := terminal_band ha ho S
  obtain ⟨U,w,H,d⟩ := only_rank_two_four_at_cap ha ho cap
  obtain ⟨z,α,Q,R,H⟩ := rank_two_four_profile ha ho S T H d
  refine ⟨U,z,α,Q,R,H,?_⟩
  by_cases a : α=0
  · obtain ⟨f,dr,dq,_⟩ := H.pure_factor a
    exact Or.inr ⟨a,f,dr,dq⟩
  · exact Or.inl a

end RKResearch.Certified.Graded.ERK12

