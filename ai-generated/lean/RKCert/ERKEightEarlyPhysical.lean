module
public import RKCert.ERKEvenEarlyCaps
public import RKCert.ERKEightPureContrast
public import RKCert.OrderTwelveOffMask
public import RKCert.DirkFourEightSurplus

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
open RKCert.Paired.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p r:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

private theorem grade_three_outside_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (pay:16≤p) (H:OrdinaryEightHead A r U w) {v:Vec K (s+1)}
    (hv:v∈zeroSpace A 3) (out:v∉U) : False := by
  let T:=diag (nodes A)
  have e5 : zeroSpace A 5=chain T U w r := by simpa only [T,Nat.add_zero] using H.paid 0 (by decide)
  have e8 : zeroSpace A 8=chain T U w (r+3) := H.paid 3 (by decide)
  have rpos : 0<r := by have :=H.two;omega
  have hVu : U.map (diag v)≤U := by
    rintro _ ⟨u,hu,rfl⟩
    have natived:=core_mul (j:=5) (k:=3) H.inv H.low H.normalized H.sites e8.le hu hv
    rw [mul_comm] at natived
    exact natived
  have band (k:ℕ) (hk:k<r) : v*((T^k) w)∈chain T U w (r+3) := by
    rw [←e8]
    have ht: (T^k) w∈zeroSpace A 5 := by rw [e5];exact ((chain_le_iff r).mp le_rfl).2 k hk
    exact zeroSpace_mul hv ht
  obtain ⟨P,hP,dp,fit⟩:=multiplier_profile H.inv hVu H.normalized H.sites rpos band
    (e5 ▸ zeroSpace_mono A (by decide : 3≤5) hv) out
  have Hsep:Separated A 8:=explicit_separated ha ho (by omega) (by omega)
  obtain ⟨i,hi,V⟩:=actual_pure_multiplier_contrast ha ho (by omega) Hsep H.inv hVu
    H.low (by decide) hv e8.le P X hP X_ne_zero (by omega) (by rw [natDegree_X];decide) fit
  have u0:nodes A i≠0:=by simpa only [eval_X] using hi
  have vv:=V P (by rw [natDegree_X];omega)
  have e : P*X*P=X*P^2 := by ring
  rw [e] at vv
  exact (primitive_x_square_pos P hP _ u0).ne' vv

private theorem grade_three_all_core_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (pay:16≤p) (H:OrdinaryEightHead A r U w)
    (h4:finrank K (zeroSpace A 4)=3) (incl:zeroSpace A 3≤U) : False := by
  classical
  let _ : DecidableEq K := Classical.decEq K
  have sep:Separated A 8 := explicit_separated ha ho (by omega) (by omega)
  have lo:=strict_rank_interval ha sep 1 2 (by decide) (by decide)
  have hi:=strict_rank_interval ha sep 3 1 (by decide) (by decide)
  change finrank K (zeroSpace A 1)+2≤finrank K (zeroSpace A 3) at lo
  change finrank K (zeroSpace A 3)+1≤finrank K (zeroSpace A 4) at hi
  have f3:finrank K (zeroSpace A 3)=2:=by omega
  have inv3 : ¬(zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3 := by
    intro hc
    have g:=forward_invariant_hermite_rank ha ho (j:=3) (by omega) (zeroSpace A 3)
      le_rfl (fun _ hv=>hc (Submodule.mem_map_of_mem hv))
    rw [f3,h4] at g
    omega
  have e4 := ordinary_step (j:=3) (by
    change finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1
    omega) inv3
  have sub : zeroSpace A 4≤U := by
    rw [e4]
    exact sup_le incl ((Submodule.map_mono incl).trans H.inv)
  have rkU:=H.rank
  have two:=H.two
  have e4U:=Submodule.eq_of_le_of_finrank_le sub (by omega)
  have U4:U≤zeroSpace A 4:=e4U.ge
  have e8 : zeroSpace A 8=chain (diag (nodes A)) U w (r+3) := H.paid 3 (by decide)
  have alg:MulClosed U:=fun u hu v hv=>core_mul (j:=4) (k:=4) H.inv U4 H.normalized H.sites e8.le hu (U4 hv)
  obtain ⟨h,off⟩:=off_mask_bootstrap ha alg H.inv e4U
    (by rw [←e4U,h4]) f3
  let L:=liveNodes U (nodes A)
  have hs:headSites (nodes A) w⊆L∪{0,h} := by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    by_cases hh:Live U i
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
    · exact Finset.mem_union_right _ (by rcases off i hh with e|e <;> simp [e])
  have cc:=(Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have lc:L.card≤finrank K U:=live_nodes_card H.inv alg
  have zc:({0,h}:Finset K).card≤2:=(Finset.card_insert_le _ _).trans (by simp)
  have count:=H.sites
  omega

/-- Universal ordered-field ERK grade-eight surplus. Repeated clocks and signs
are unrestricted; the only pure scalar gates are the ordered 3+2 quartic and
the oriented one-endpoint square. -/
theorem grade_eight_surplus_ordered_of_succ (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b p) (pay:16≤p) : 9≤finrank K (zeroSpace A 8) := by
  by_contra! z
  have cap:finrank K (zeroSpace A 8)≤8 := by omega
  obtain ⟨r,U,w,H⟩:=ordinary_eight_head ha ho pay cap
  have sep:Separated A 8:=explicit_separated ha ho (by omega) (by omega)
  have low:=strict_rank_interval ha sep 1 3 (by decide) (by decide)
  change finrank K (zeroSpace A 1)+3≤finrank K (zeroSpace A 4) at low
  have jump:=Terminal.grade_four_eight_surplus (fun i j hij=>ha i j hij.le) ho (by omega)
    (RKCert.EndpointPhysical.noExceptionalRatio_ordered (R:=K))
  have three:finrank K (zeroSpace A 4)=3:=by omega
  by_cases inc:zeroSpace A 3≤U
  · exact grade_three_all_core_impossible ha ho pay H three inc
  · obtain ⟨v,hv,hno⟩:=Set.not_subset.mp inc
    exact grade_three_outside_impossible ha ho pay H hv hno

/-- The true ordinary defect bound in arbitrary stage count (including empty
stage types, which cannot satisfy the order hypothesis). -/
theorem grade_eight_surplus_ordered {n:ℕ} {A:Fin n→Fin n→K} {b:Vec K n}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p) (pay:16≤p) :
    9≤finrank K (zeroSpace A 8) := by
  cases n with
  | zero =>
    have h:=explicit_order_le_stages ha ho
    omega
  | succ n => exact grade_eight_surplus_ordered_of_succ ha ho pay

/-- Rank-only even endpoint paid by the genuine grade-eight surplus. -/
theorem explicit_even_rank_floor_from_eight {n q:ℕ} {A:Fin n→Fin n→K} {b:Vec K n}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q)) (hq:8≤q) :
    3*q≤n := by
  have sep:Separated A q:=explicit_separated ha ho le_rfl (by
    have h:=explicit_order_le_stages ha ho
    omega)
  have early:=grade_eight_surplus_ordered ha ho (by omega)
  have growth:=strict_rank_interval ha sep 8 (q-8) (by decide) (by omega)
  rw [show 8+(q-8)=q by omega] at growth
  have e:=tree_rank_eq ho sep (by omega)
  have h:=backward_count ha ho q (q-2) (by omega)
  omega

end RKCert.Paired.FiniteMidpoint
