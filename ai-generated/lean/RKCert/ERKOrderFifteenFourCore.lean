module
public import RKCert.ERKOrderFifteenThreeMasks
public import RKCert.ERKOrderedQ7Core

@[expose] public section

/-! # A pure rank-two, degree-four head when no terminal interrupts E8 -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Module Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

omit [CharZero K] in
theorem marked_four_pays_two (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (H : MarkedHead A 7 d 2 U w)
    (rank4 : finrank K (zeroSpace A 4)=4) :
    U≤defectPlus A d 4 ∧ w∈defectPlus A d 4 := by
  let D := diag (nodes A)
  let F := defectPlus A d 5
  have two := marked_five_core_two ho S M H
  have coreEq : core D F 2=U := two
  have ru := H.rank
  have F5 : F=chain D U w 2 := by simpa [D,F] using H.paid 5 (by decide) (by decide)
  have r5 : finrank K F=5+d := by
    unfold F defectPlus
    rw [add_tail_rank M (by decide) (disjoint_tail_of_order ho S.lastLive
      (le_refl (zeroSpace A 5)) (by decide)),S.fRank 5 (by decide) (by decide)]
  have r4 : finrank K (defectPlus A d 4)=4+d := by
    unfold defectPlus
    rw [add_tail_rank M (by decide) (disjoint_tail_of_order ho S.lastLive
      (le_refl (zeroSpace A 4)) (by decide)),rank4]
  have rstrict : core D F 1<F := by
    apply lt_of_le_of_ne (descend D F 0)
    intro e
    have stable := invariant_of_plateau e.symm
    change F.map D≤F at stable
    have h := sup_eq_left.mpr stable
    rw [F5,chain_sup_map H.stable (by decide)] at h
    have eq : defectPlus A d 6=F := by
      have h6 := H.paid 6 (by decide) (by decide)
      exact (h6.trans h).trans F5.symm
    have r6 : finrank K (defectPlus A d 6)=6+d := by
      unfold defectPlus
      rw [add_tail_rank M (by decide) (disjoint_tail_of_order ho S.lastLive
        (le_refl (zeroSpace A 6)) (by decide)),S.fRank 6 (by decide) (by decide)]
    rw [eq,r5] at r6
    omega
  have le1 : defectPlus A d 4≤core D F 1 := by
    intro v hv
    apply mem_core.mpr
    intro j hj
    interval_cases j
    · simpa only [pow_zero,one_apply_eq_self] using Fplus_mono A d (by decide : 4≤5) hv
    · simpa only [pow_one] using Fplus_clock A d 4 (Submodule.mem_map_of_mem hv)
  have e1 : defectPlus A d 4=core D F 1 :=
    Submodule.eq_of_le_of_finrank_le le1 (by have := Submodule.finrank_lt_finrank_of_lt rstrict; omega)
  rw [e1]
  refine ⟨le_of_eq two.symm |>.trans (descend D F 1),?_⟩
  have pw := (chain_le_iff (T:=D) (U:=U) (w:=w) 2).mp (le_of_eq F5.symm)
  apply mem_core.mpr
  exact fun j hj=>pw.2 j (by omega)

theorem marked_eight_eq_edge (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (C : OddSevenChart A d 7 2 U w G)
    (absent : d=0 ∨ terminal (K:=K) s∉treeSpace A 8) :
    defectPlus A d 8=firstEscape A d 7 := by
  unfold defectPlus
  rw [no_early_terminal_unmarked_eight ha ho S C absent]
  simp [firstEscape,tailPlane]

omit [CharZero K] in
theorem core_times_marked_four (C : OddSevenChart A d 7 2 U w G)
    (u4 : U≤defectPlus A d 4) (e8 : defectPlus A d 8=firstEscape A d 7)
    {u v : Vec K (s+1)} (hu:u∈U) (hv:v∈defectPlus A d 4) : u*v∈U := by
  let c := nodes A
  have sum : u*v=∑ z∈sites c,fiber c z u*v := by rw [←Finset.sum_mul,sum_fibers]
  rw [sum]
  apply U.sum_mem
  intro z _
  have h : fiber c z u*v∈defectPlus A d 8 :=
    Fplus_mul (j:=4) (k:=4) (u4 (fiber_mem C.marked.stable _ hu)) hv
  rw [e8,C.marked.edge] at h
  have count := C.sites
  have hcnt : 5<(headSites c w).card := by
    change headLen 7 7 2 12≤_ at count
    unfold headLen at count
    change 5<(headSites (nodes A) w).card
    omega
  apply localized_mem (z:=z) C.marked.stable C.marked.norm hcnt h
  intro i hi
  simp [fiber,c,hi]

theorem pure_four_profile (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (C : OddSevenChart A d 7 2 U w G)
    (absent : d=0 ∨ terminal (K:=K) s∉treeSpace A 8)
    (rank4 : finrank K (zeroSpace A 4)=4) :
    ∃ v P,OddSevenChart A d 7 2 U v G ∧ v∈defectPlus A d 4 ∧ SevenProfile A 2 U v P := by
  obtain ⟨u4,w4⟩:=marked_four_pays_two ho S M C.marked rank4
  have e8 := marked_eight_eq_edge ha ho S C absent
  have mulc : MulClosed U := fun u hu v hv => core_times_marked_four C u4 e8 hu (u4 hv)
  obtain ⟨v,vu,dis,eq⟩:=disjoint_head C.marked.stable mulc (fun u hu=>core_times_marked_four C u4 e8 hu w4)
  have v4 : v∈defectPlus A d 4 := by
    have h := (defectPlus A d 4).sub_mem w4 (u4 vu)
    rwa [sub_sub_cancel] at h
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have e := dis i ⟨_,hz,hn⟩
    simp [fiber,e] at hn
  have H : MarkedHead A 7 d 2 U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=>(C.marked.paid j hj hq).trans (eq _).symm,
      C.marked.edge.trans (eq _).symm,C.marked.edgeRank⟩
  have chart : OddSevenChart A d 7 2 U v G := by
    refine ⟨H,C.chartType,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩
    intro j hj hm
    unfold forwardBand
    rw [eq]
    exact C.chart j hj hm
  have h : v*v∈defectPlus A d 8 := Fplus_mul (j:=4) (k:=4) v4 v4
  rw [e8,H.edge] at h
  obtain ⟨z,hz,P,pdeg,repr⟩:=exists_head_poly h
  have eval (i) (vi:v i≠0) : v i=P.eval (nodes A i) := by
    have zi : z i=0 := by by_contra hn; exact vi (dis i ⟨z,hz,hn⟩)
    have ep := repr i
    rw [Pi.mul_apply,zi,zero_add] at ep
    exact mul_right_cancel₀ vi ep
  have cnt := chart.sites
  have pn : P≠0 := by
    intro p0
    have pos : 0<(headSites (nodes A) v).card := by unfold headLen at cnt;omega
    obtain ⟨x,hx⟩ := Finset.card_pos.mp pos
    obtain ⟨i,hi,_⟩ := Finset.mem_image.mp hx
    have vn := (Finset.mem_filter.mp hi).2
    exact vn (by rw [eval i vn,p0,eval_zero])
  have pg : P.natDegree<2+(7-4) := (natDegree_lt_iff_degree_lt pn).mpr pdeg
  exact ⟨v,P,chart,v4,mulc,dis,pn,by omega,eval⟩

end RKCert.Paired.FiniteMidpoint
