module
public import RKCert.ERKMarkedOffMask
public import RKCert.ERKOrder13MarkedCore
public import RKCert.ERKOrder13ThreeTwo

@[expose] public section
/-! # Actual low marked two-chain: at most six numerical head sites -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s a:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2700000

theorem marked13_three_two_core_actual (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (h4:finrank K (zeroSpace A 4)=3) :
    defectPlus A 1 4=U := by
  let T:=diag (nodes A)
  let F:=defectPlus A 1 3
  let J:=F⊔F.map T
  have f3:=grade_three_eq_two_13 ha ho S h4
  have F3rank:finrank K F=3 := by
    change finrank K (defectPlus A 1 3)=3
    rw [marked13_defect_rank ho M S 3 (by decide),f3]
  have u4rank:finrank K U=4 := by have r:=C.marked.rank;omega
  have F4rank:finrank K (defectPlus A 1 4)=4 := by
    rw [marked13_defect_rank ho M S 4 (by decide),h4]
  have u3:F≤U := by
    have low := marked13_lower_into_core ho S M C.marked (k:=3) (by decide) (by decide)
    exact low
  have raw : ¬(zeroSpace A 3).map T≤zeroSpace A 3 := by
    intro h
    have H := forward_invariant_hermite_rank ha ho (j:=3) (by decide) (zeroSpace A 3)
      le_rfl (fun _ hv=>h (Submodule.mem_map_of_mem hv))
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at H
    omega
  have aug : ¬F.map T≤F := by
    intro h
    apply raw
    rintro _ ⟨v,hv,rfl⟩
    have vF : v∈F := (show zeroSpace A 3≤defectPlus A 1 3 from le_sup_left) hv
    have ip : T v∈F := h (Submodule.mem_map_of_mem vF)
    obtain ⟨x,hx,e,he,eq⟩:=Submodule.mem_sup.mp ip
    have both : (zeroSpace A 4)⊓tailPlane K s 1=⊥ :=
      disjoint_tail_of_order ho S.lastLive (V:=zeroSpace A 4) le_rfl (by decide)
    have pay:e∈zeroSpace A 4 := by
      have form:e=T v-x := by rw [←eq];abel
      rw [form]
      exact (zeroSpace A 4).sub_mem (diag_zeroSpace A 3 hv) (zeroSpace_mono A (by decide) hx)
    have e0:e=0 := by
      apply (Submodule.mem_bot K).mp
      rw [←both]
      exact ⟨pay,he⟩
    rw [e0,add_zero] at eq
    rwa [←eq]
  have Jlo : F<J := lt_of_le_of_ne (show F≤J from le_sup_left)
    (fun e=>aug ((show F.map T≤J from le_sup_right).trans (le_of_eq e.symm)))
  have Jdim:=Submodule.finrank_lt_finrank_of_lt Jlo
  have Jfour:J≤defectPlus A 1 4 := sup_le (Fplus_mono A 1 (by decide)) (Fplus_clock A 1 3)
  have JU:J≤U:=sup_le u3 ((Submodule.map_mono u3).trans C.marked.stable)
  exact (Submodule.eq_of_le_of_finrank_le Jfour (by omega)).symm.trans
    (Submodule.eq_of_le_of_finrank_le JU (by omega))

theorem marked13_rank_three_two_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 2 U w G)
    (h4:finrank K (zeroSpace A 4)=3) : False := by
  classical
  have e4:=marked13_three_two_core_actual ha ho S M C h4
  have pay:U≤defectPlus A 1 4:=e4.ge
  have algebra:MulClosed U:=fun u hu v hv=>marked13_local_core_product ha ho S M C (j:=4) (k:=4)
    pay (by decide) hu (pay hv)
  have f3:=grade_three_eq_two_13 ha ho S h4
  have u4:finrank K U=4 := by have r:=C.marked.rank;omega
  have incl:defectPlus A 1 3≤U:=(Fplus_mono A 1 (by decide : 3≤4)).trans e4.le
  have rwk:finrank K (defectPlus A 1 3)+1=finrank K U := by
    rw [marked13_defect_rank ho M S 3 (by decide),f3,u4]
  obtain ⟨h,off⟩:=off_mask_bootstrap_codim_one ha algebra C.marked.stable incl rwk
    (fun v hv=> e4.le (Fplus_mat ha 1 3 ⟨v,hv,rfl⟩))
    (fun k hk=>e4.le ((show zeroSpace A 4≤defectPlus A 1 4 from le_sup_left)
      (zeroSpace_mono A (by omega) (primitive_defect A (X^k) (by simp : (X^k:K[X]).natDegree≤k)))))
  let L:=RKCert.Paired.OrderTwelve.liveNodes U (nodes A)
  have sub:headSites (nodes A) w ⊆ L ∪ {0,h} := by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    by_cases hh:Live U i
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
    · exact Finset.mem_union_right _ (by rcases off i hh with e|e <;> simp [e])
  have c:=(Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have l:L.card≤finrank K U:=RKCert.Paired.OrderTwelve.live_nodes_card C.marked.stable algebra
  have z:({0,h}:Finset K).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
  have wdt:=C.width
  have count:=band13_sites C
  unfold headLen at count
  omega

end RKCert.Paired.FiniteMidpoint
