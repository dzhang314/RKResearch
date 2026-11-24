module
public import RKCert.ERKOrder13ShortJoint
public import RKCert.ERKOrder13MixedFactor

@[expose] public section
/-! # Actual final short-head rank charts
The rank-four inside branch and rank-five branch share the literal mixed
factor cancellation. Only their paid product runs and core ranks differ. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint
  Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 4700000

theorem marked13_low_quadratic_span (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (h4:finrank K (zeroSpace A 4)=3) :
    zeroSpace A 2=(K ∙ qdef A) ∧ finrank K (zeroSpace A 2)=1 := by
  have f3:=grade_three_eq_two_13 ha ho S h4
  have d:=qdef_ne_zero ha (S.separated.mono (by decide : 5≤6))
  have rk:=finrank_span_singleton (K:=K) d
  have q:K∙qdef A≤zeroSpace A 2 := (Submodule.span_singleton_le_iff_mem ..).mpr (qdef_mem A)
  have lo:=Submodule.finrank_mono q
  have hi:=Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_separated ha S.separated (j:=2) (by decide) (by decide))
  change finrank K (zeroSpace A 2)<finrank K (zeroSpace A 3) at hi
  have e:finrank K (zeroSpace A 2)=1 := by omega
  exact ⟨(Submodule.eq_of_le_of_finrank_le q (by omega)).symm,e⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem marked13_unmark_to_lower (ho:HasTreeOrderAtLeast A b 13) (S:Saturated A b 6 1)
    {j k:ℕ} (le:j≤k) (cap:k≤12) {x:Vec K (s+1)} (hx:x∈zeroSpace A k)
    (hm:x∈defectPlus A 1 j) : x∈zeroSpace A j := by
  obtain ⟨y,hy,e,he,eq⟩:=Submodule.mem_sup.mp hm
  have both : (zeroSpace A k)⊓tailPlane K s 1=⊥ :=
    disjoint_tail_of_order ho S.lastLive (V:=zeroSpace A k) le_rfl (by omega)
  have epay:e∈zeroSpace A k := by
    rw [show e=x-y by rw [←eq];abel]
    exact (zeroSpace A k).sub_mem hx (zeroSpace_mono A le hy)
  have e0:e=0 := by
    apply (Submodule.mem_bot K).mp
    rw [←both]
    exact ⟨epay,he⟩
  rw [e0,add_zero] at eq
  rwa [←eq]

private theorem short_core_clean (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (up:U≤defectPlus A 1 2) :
    ∃ z:Vec K (s+1),Chart13 A 1 a r U z G∧MulClosed U∧∀i,Live U i→z i=0 := by
  have alg:MulClosed U:=fun u hu y hy=>marked13_local_core_product ha ho S M C (j:=2) (k:=2)
    up (by decide) hu (up hy)
  have w5:w∈defectPlus A 1 5 := by
    rw [C.marked.paid 5 le_rfl (by decide)]
    change w∈chain (diag (nodes A)) U w r
    simpa only [pow_zero,one_apply_eq_self] using
      ((chain_le_iff _).mp le_rfl).2 0 (show 0<r by have := C.marked.rTwo;omega)
  obtain ⟨z,C,dis⟩:=marked13_clean_head C alg (fun _ hu=>marked13_local_core_product ha ho S M C
    (j:=2) (k:=5) up (by decide) hu w5)
  exact ⟨z,C,alg,dis⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem short_paid_product (C:Chart13 A 1 a r U w G)
    {k:ℕ} (vpay:v∈defectPlus A 1 k) {i:ℕ} (hi:i<r) :
    (diag (nodes A)^i) (v*w)∈defectPlus A 1 (k+5) := by
  have p:(diag (nodes A)^i) w∈defectPlus A 1 5 := by
    rw [C.marked.paid 5 le_rfl (by decide)]
    exact ((chain_le_iff _).mp le_rfl).2 _ hi
  have eq : (diag (nodes A)^i) (v*w)=v*((diag (nodes A)^i) w) := by
    ext j
    simp only [pow_diag_apply,Pi.mul_apply]
    ring
  rw [eq]
  exact Fplus_mul vpay p

private theorem short_band_earlier (S:Saturated A b 6 1) (M:Margin A b 6 1 1)
    (C:Chart13 A 1 a r U w G) {z:Vec K (s+1)} {i j:ℕ} (hi:a+1 ≤ i) (hij:i ≤ j) (hj:j≤10)
    (tr:z∈treePlus A 1 i) (mem:z∈Band13 A a r U w j) :
    z∈Band13 A a r U w i := by
  classical
  have sub:Band13 A a r U w i≤Band13 A a r U w j := by
    apply (chain_le_iff _).mpr
    exact ⟨((chain_le_iff _).mp le_rfl).1,
      fun t ht=>((chain_le_iff _).mp le_rfl).2 _ (by unfold headLen at *;omega)⟩
  rw [C.chart i hi (by omega)] at tr
  obtain ⟨x,⟨c,rfl⟩,y,hy,eq⟩:=Submodule.mem_sup.mp tr
  let P:=ofFn (a+1) c
  have pd:P.natDegree≤a := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have zero:=band13_separation S M C (by omega : a+1≤j) hj P pd (by
    rw [evalNodes_ofFn A a c,show polyEval A a c=z-y by rw [←eq];abel]
    exact (Band13 A a r U w j).sub_mem mem (sub hy))
  have ep:polyEval A a c=0 := by
    rw [←evalNodes_ofFn]
    change evalNodes A P=0
    rw [zero]
    ext t
    simp
  rw [ep,zero_add] at eq
  rwa [←eq]

theorem marked13_rank_four_inside_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 4 U w G)
    (h4:finrank K (zeroSpace A 4)=3) (inside:qdef A∈U) : False := by
  let d:=qdef A
  let v:=mat A d
  obtain ⟨dline,dr⟩:=marked13_low_quadratic_span ha ho S h4
  have up : defectPlus A 1 2≤U := by
    apply sup_le _ (marked13_terminal_in_core C)
    rw [dline]
    exact (Submodule.span_singleton_le_iff_mem ..).mpr inside
  have eq : defectPlus A 1 2=U := by
    apply Submodule.eq_of_le_of_finrank_le up
    rw [marked13_defect_rank ho M S 2 (by decide),dr]
    have :=C.marked.rank
    omega
  obtain ⟨z,C,alg,dis⟩:=short_core_clean ha ho S M C eq.ge
  have v3:v∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 (qdef_mem A)
  have vn:v∉U := by
    intro h
    have z:diag (nodes A) d∈U := C.marked.stable ⟨_,inside,rfl⟩
    rw [←eq] at h z
    have x:=marked13_unmark_to_lower ho S (by decide) (by decide) v3 h
    have y:=marked13_unmark_to_lower ho S (by decide) (by decide)
      (diag_zeroSpace A 2 (qdef_mem A)) z
    rw [dline] at x y
    exact marked13_no_invariant_quadratic_line ha S.separated ⟨x,y⟩
  have vp:v∈defectPlus A 1 3 := (show zeroSpace A 3≤defectPlus A 1 3 from le_sup_left) v3
  have vbase:v∈chain (diag (nodes A)) U z 2 :=
    marked13_lower_into_core ho S M C.marked (k:=3) (by decide) (by decide) vp
  have wa:=C.width
  have N:=marked13_head_sites_eleven ha ho S M C
  have cnt:headLen 6 a 4 8<(headSites (nodes A) z).card := by unfold headLen at *;omega
  have bp:=marked13_purify_run ha ho S M C (v*z) 3 (by decide)
    (fun i hi=>short_paid_product C vp (by omega))
  obtain ⟨P,pd,rep⟩:=multiplier_degree dis cnt bp
  have deg:P.natDegree+4+a≤13 := by
    unfold headLen at pd
    rcases pd with h|h
    · rw [h,natDegree_zero];omega
    · omega
  exact marked13_mixed_factor_impossible ha ho S M C (by decide) alg dis (by decide)
    (by decide) vp vn vbase deg rep

theorem marked13_rank_five_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 5 U w G) : False := by
  let d:=qdef A
  have core := marked13_terminal_in_core C
  have tail : tailPlane K s 1=U := by
    apply Submodule.eq_of_le_of_finrank_le core
    rw [tail_rank 1 (by decide)]
    have :=C.marked.rank
    omega
  have up:U≤defectPlus A 1 2 := by rw [←tail];exact le_sup_right
  obtain ⟨z,C,alg,dis⟩:=short_core_clean ha ho S M C up
  have d2:d∈zeroSpace A 2 := qdef_mem A
  have dn:d≠0:=qdef_ne_zero ha (S.separated.mono (by decide : 5≤6))
  have dU:d∉U := by
    intro h
    apply dn
    have both:(zeroSpace A 2)⊓tailPlane K s 1=⊥ :=
      disjoint_tail_of_order ho S.lastLive (V:=zeroSpace A 2) le_rfl (by decide)
    apply (Submodule.mem_bot K).mp
    rw [←both,tail]
    exact ⟨d2,h⟩
  have dp:d∈defectPlus A 1 2 := (show zeroSpace A 2≤defectPlus A 1 2 from le_sup_left) d2
  have dbase:d∈chain (diag (nodes A)) U z 2 :=
    marked13_lower_into_core ho S M C.marked (k:=2) (by decide) (by decide) dp
  have wa:=C.width
  have N:=marked13_head_sites_eleven ha ho S M C
  have cnt:headLen 6 a 5 7<(headSites (nodes A) z).card := by unfold headLen at *;omega
  have prod (i:ℕ) (hi:i≤4) : (diag (nodes A)^i) (d*z)∈defectPlus A 1 7 :=
    short_paid_product C dp (by omega)
  have pure8:=marked13_purify_run ha ho S M C (d*z) 4 (by decide)
    (fun i hi=>Fplus_mono A 1 (by decide) (prod i hi))
  have pure7 (i:ℕ) (hi:i≤4) : (diag (nodes A)^i) (d*z)∈Band13 A a 5 U z 7 :=
    short_band_earlier S M C (by omega) (by decide) (by decide)
      ((sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl) (prod i hi)) (pure8 i hi)
  obtain ⟨P,pd,rep⟩:=multiplier_degree dis cnt pure7
  have deg:P.natDegree+5+a≤13 := by
    unfold headLen at pd
    rcases pd with h|h
    · rw [h,natDegree_zero];omega
    · omega
  exact marked13_mixed_factor_impossible ha ho S M C (by decide) alg dis (by decide)
    (by decide) dp dU dbase deg rep

end RKCert.Paired.FiniteMidpoint
