module
public import RKCert.ERKOrder13FourCore
public import RKCert.OrderTwelveOffMask

@[expose] public section
/-! # Native three-class contradiction for the low full-odd core -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 1300000

theorem grade_three_eq_two_13 (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (h4:finrank K (zeroSpace A 4)=3) :
    finrank K (zeroSpace A 3)=2 := by
  have h34:=Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha S.separated
    (j:=3) (by decide) (by decide))
  have h3 := zeroSpace_finrank ha ho (n:=2) (by decide)
  change 2≤finrank K (zeroSpace A 3) at h3
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at h34
  omega

theorem three_two_core_actual (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (H:MarkedHead A 6 0 2 U w)
    (h4:finrank K (zeroSpace A 4)=3) :
    zeroSpace A 4=U := by
  have h3:=grade_three_eq_two_13 ha ho S h4
  have hnv : ¬(zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3 := by
    intro h
    have H := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=3) (by decide) (zeroSpace A 3)
      le_rfl (fun _ hv=>h (Submodule.mem_map_of_mem hv))
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at H
    omega
  have leU : zeroSpace A 3≤U := by
    have hh := full13_lower_into_core S H (k:=3) (by decide) (by decide)
    exact hh
  apply Submodule.eq_of_le_of_finrank_le ?_ (by have h := H.rank;omega)
  rw [ordinary_step (by omega : finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1) hnv]
  exact sup_le leU ((Submodule.map_mono leU).trans H.stable)

theorem order13_full_rank_three_two_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 2 U w G)
    (h4:finrank K (zeroSpace A 4)=3) : False := by
  classical
  have e4:=three_two_core_actual ha ho S C.marked h4
  have U4:U≤zeroSpace A 4 := le_of_eq e4.symm
  have hu : MulClosed U := fun u hu v hv=>full13_local_core_product ha ho S M C
    (j:=4) (k:=4) U4 (by decide) hu (U4 hv)
  have d3 := grade_three_eq_two_13 ha ho S h4
  have dimU : finrank K U=3 := by rw [←e4,h4]
  obtain ⟨a,ha'⟩ := RKCert.Paired.OrderTwelve.off_mask_bootstrap ha hu C.marked.stable e4 dimU d3
  let L:=RKCert.Paired.OrderTwelve.liveNodes U (nodes A)
  have hs' : headSites (nodes A) w ⊆ L ∪ {0,a} := by
    intro x hx
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
    by_cases hh:Live U j
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
    · exact Finset.mem_union_right _ (by rcases ha' j hh with e|e <;> simp [e])
  have ct := (Finset.card_le_card hs').trans (Finset.card_union_le _ _)
  have hLive : L.card≤finrank K U := RKCert.Paired.OrderTwelve.live_nodes_card C.marked.stable hu
  have count := band13_sites C
  have cA : ({0,a}:Finset K).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
  unfold headLen at count
  omega

end RKCert.Paired.FiniteMidpoint
