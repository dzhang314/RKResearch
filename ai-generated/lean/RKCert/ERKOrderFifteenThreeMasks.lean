module
public import RKCert.ERKOrderFifteenBand
public import RKCert.ERKOrderFifteenTerminalChart
public import RKCert.OrderTwelveOffMask

@[expose] public section

/-! # The rank-two, three-dimensional F4 chart without an early terminal

Use case-short marked core ranks, plain grade-eight rigidity, and the
already checked physical three-mask bootstrap. No additional pencil or
external numerical calculation is required for this branch.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Module Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s d : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
variable {U : Submodule K (Vec K (s+1))} {w : Vec K (s+1)} {G : K[X]}

omit [CharZero K] in
theorem marked_five_core_two (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (H : MarkedHead A 7 d 2 U w) :
    core (diag (nodes A)) (defectPlus A d 5) 2=U := by
  let C := diag (nodes A)
  let F := defectPlus A d 5
  let F' := defectPlus A d 6
  have f (j : ℕ) (lo:5≤j) (hi:j≤7) : finrank K (defectPlus A d j)=j+d := by
    unfold defectPlus
    rw [add_tail_rank M (by decide) (disjoint_tail_of_order ho S.lastLive
      (le_refl (zeroSpace A j)) (by omega)),S.fRank j lo hi]
  have f5 : finrank K F=5+d := f 5 (by decide) (by decide)
  have f6 : finrank K F'=6+d := f 6 (by decide) (by decide)
  have pf : F=chain C U w 2 := by simpa [F,C] using H.paid 5 (by decide) (by decide)
  have pf' : F'=chain C U w 3 := by simpa [F',C] using H.paid 6 (by decide) (by decide)
  have heads := (chain_le_iff (T:=C) (U:=U) (w:=w) 2).mp (le_of_eq pf.symm)
  have wF : w∈F := by simpa only [pow_zero,one_apply_eq_self] using heads.2 0 (by decide)
  have cwF : C w∈F := by simpa only [pow_one] using heads.2 1 (by decide)
  have out : (C^2) w∉F := by
    intro hh
    have e : F'≤F := by
      rw [pf']
      exact sup_le (le_of_eq pf.symm) ((Submodule.span_singleton_le_iff_mem ..).mpr hh)
    have nr := Submodule.finrank_mono e
    omega
  have lt1 : core C F 1<F := by
    apply lt_of_le_of_ne (descend C F 0)
    intro eq
    have h : C w∈core C F 1 := eq.symm ▸ cwF
    apply out
    simpa only [pow_one,pow_two,mul_apply_eq_comp] using mem_core.mp h 1 le_rfl
  have lt2 : core C F 2<core C F 1 := by
    apply lt_of_le_of_ne (descend C F 1)
    intro eq
    have e : w∈core C F 1 := by
      apply mem_core.mpr
      intro n hn
      interval_cases n
      · simpa only [pow_zero,one_apply_eq_self] using wF
      · simpa only [pow_one] using cwF
    exact out (mem_core.mp (eq.symm ▸ e : w∈core C F 2) 2 le_rfl)
  have r1 := Submodule.finrank_lt_finrank_of_lt lt1
  have r2 := Submodule.finrank_lt_finrank_of_lt lt2
  have ru := H.rank
  exact (Submodule.eq_of_le_of_finrank_le (invariant_le_core H.core H.stable 2)
    (by change finrank K (core C F 2)≤finrank K U; omega)).symm

theorem marked_three_core_eq (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d) (H : MarkedHead A 7 d 2 U w)
    (d4 : finrank K (zeroSpace A 4)=3) :
    zeroSpace A 4⊔tailPlane K s d=U ∧ finrank K (zeroSpace A 3)=2 := by
  let C := diag (nodes A)
  let F := defectPlus A d 5
  have h3lower := zeroSpace_finrank ha ho (n:=2) (by decide)
  change 2≤finrank K (zeroSpace A 3) at h3lower
  have h3upper := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha S.separated
    (j:=3) (by decide) (by decide))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at h3upper
  have d3 : finrank K (zeroSpace A 3)=2 := by omega
  have eq := marked_five_core_two ho S M H
  have grade (v) (hv : v∈zeroSpace A 3) : v∈core C F 2 := by
    apply mem_core.mpr
    intro k hk
    have plus : zeroSpace A 5≤F := le_sup_left
    interval_cases k
    · simpa only [pow_zero,one_apply_eq_self] using plus (zeroSpace_mono A (by decide : 3≤5) hv)
    · rw [pow_one]
      exact plus (zeroSpace_mono A (by decide : 4≤5) (diag_zeroSpace A 3 hv))
    · rw [pow_two,mul_apply_eq_comp]
      exact plus (diag_zeroSpace A 4 (diag_zeroSpace A 3 hv))
  have h3 : zeroSpace A 3≤U := fun x hx => eq ▸ grade x hx
  have hni : ¬(zeroSpace A 3).map C≤zeroSpace A 3 := by
    intro inv
    have ra := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=3) (by decide)
      (zeroSpace A 3) le_rfl (fun _ hx=>inv (Submodule.mem_map_of_mem hx))
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at ra
    omega
  have q4 : zeroSpace A 4≤U := by
    rw [Clock.ordinary_step (by omega : finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1) hni]
    exact sup_le h3 ((Submodule.map_mono h3).trans H.stable)
  have tail : tailPlane K s d≤U := by
    rw [←eq]
    exact invariant_le_core (show tailPlane K s d≤F from le_sup_right) (tail_clock d _) 2
  have fr : finrank K ↥(zeroSpace A 4⊔tailPlane K s d)=3+d := by
    rw [add_tail_rank M (by decide) (disjoint_tail_of_order ho S.lastLive
      (le_refl (zeroSpace A 4)) (by decide)),d4]
  exact ⟨Submodule.eq_of_le_of_finrank_le (sup_le q4 tail) (by have := H.rank;omega),d3⟩

/-- True order-fifteen saturated tableaux have no rank-two, three-dimensional
grade-four branch once the ordinary grade-eight decomposition is available. -/
theorem no_three_masks_without_early_terminal
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 15)
    (S : Saturated A b 7 1) (M : Margin A b 7 1 d)
    (C : OddSevenChart A d 7 2 U w G)
    (absent : d=0 ∨ terminal (K:=K) s∉treeSpace A 8)
    (d4 : finrank K (zeroSpace A 4)=3) : False := by
  obtain ⟨eq,d3⟩ := marked_three_core_eq ha ho S M C.marked d4
  have decomp := no_early_terminal_unmarked_eight ha ho S C absent
  have low : zeroSpace A 4≤U := le_sup_left.trans (le_of_eq eq)
  have peel (j:ℕ) (hj:4≤j) (jp:j+1≤15) {v:Vec K (s+1)}
      (hv:v∈U) (hp:v∈zeroSpace A j) : v∈zeroSpace A 4 := by
    rw [←eq] at hv
    obtain ⟨x,hx,y,hy,e⟩:=Submodule.mem_sup.mp hv
    have ye : y=v-x := by rw [←e];abel
    have ym : y∈zeroSpace A j :=
      ye ▸ (zeroSpace A j).sub_mem hp (zeroSpace_mono A hj hx)
    have f := Submodule.mem_inf.mpr ⟨ym,hy⟩
    rw [disjoint_tail_of_order ho S.lastLive (le_refl (zeroSpace A j)) jp] at f
    have yz := (Submodule.mem_bot K).mp f
    rw [yz,add_zero] at e
    exact e ▸ hx
  have inv : (zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := by
    rintro _ ⟨x,hx,rfl⟩
    exact peel 5 (by decide) (by decide) (C.marked.stable (Submodule.mem_map_of_mem (low hx))) (diag_zeroSpace A 4 hx)
  have cnt := C.sites
  have nine : 9≤(headSites (nodes A) w).card := by
    simpa [headLen] using cnt
  have leEscape : firstEscape A 0 7≤firstEscape A d 7 := by
    unfold firstEscape
    exact sup_le_sup le_rfl (by simp [tailPlane])
  have mul : MulClosed (zeroSpace A 4) := by
    intro v hv u hu
    have x : v*u=∑ z∈sites (nodes A),fiber (nodes A) z v*u := by rw [←Finset.sum_mul,sum_fibers]
    rw [x]
    apply (zeroSpace A 4).sum_mem
    intro z _
    have prime : fiber (nodes A) z v*u∈zeroSpace A 8 :=
      zeroSpace_mul (fiber_mem inv z hv) hu
    have pay := leEscape (decomp ▸ prime)
    rw [C.marked.edge] at pay
    have loc : ∀ i,nodes A i≠z→(fiber (nodes A) z v*u) i=0 := by
      intro i hi
      simp [fiber,hi]
    have mU := localized_mem C.marked.stable C.marked.norm (by omega) pay loc
    exact peel 8 (by decide) (by decide) mU prime
  obtain ⟨h,ht⟩:=RKCert.Paired.OrderTwelve.off_mask_bootstrap ha mul inv rfl d4 d3
  let L := RKCert.Paired.OrderTwelve.liveNodes (zeroSpace A 4) (nodes A)
  have cap : L.card≤3 := (RKCert.Paired.OrderTwelve.live_nodes_card inv mul).trans_eq d4
  have hn : headSites (nodes A) w ⊆ L∪{(0:K),h} := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases live : Live (zeroSpace A 4) i
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,live⟩))
    · exact Finset.mem_union_right _ (by rcases ht i live with e|e <;> simp [e])
  have htwo : ({(0:K),h}:Finset K).card≤2 := Finset.card_insert_le _ _
    |>.trans (by simp)
  have total := (Finset.card_le_card hn).trans (Finset.card_union_le _ _)
  omega

end RKCert.Paired.FiniteMidpoint
