module
public import RKCert.ERKOrder13TiedFeatures
public import RKCert.ERKOrder13WidePure
public import RKCert.ERKFeatureRepresentatives
public import RKCert.ERKOwnerAdjoints
public import RKCert.ERKTiedAdjointRank
public import RKCert.ERKPartialUnaryRepair
public import RKCert.ExplicitOrderTwelve

@[expose] public section
/-! # The actual full-odd rank-two tied-feature contradiction -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve Module Polynomial
variable {K:Type*} [Field K] [CharZero K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 3000000

omit [CharZero K] in
private theorem zero_tail13 (j:ℕ) : treePlus A 0 j=treeSpace A j := by
  simp [treePlus,tailPlane]

omit [CharZero K] in
private theorem zero_tail13_rank (j:ℕ) :
    finrank K (treePlus A 0 j)=finrank K (treeSpace A j) :=
  congrArg (fun Z:Submodule K (Vec K (s+1))=>finrank K Z) (zero_tail13 j)

theorem full13_pure_feature_caps (C:Chart13 A 0 6 2 U w G) (dis:∀i,Live U i→w i=0)
    (pure:w*w∈Band13 A 6 2 U w 8) (narrow:(headSites (nodes A) w).card≤7) :
    (headFeatures (nodes A) w).card≤7 ∧ (offFeatures U (nodes A) w).card≤7 := by
  classical
  let c:=nodes A
  have N := band13_sites C
  change 7≤(headSites c w).card at N
  have cn : headLen 6 6 2 8<(headSites c w).card := by
    unfold headLen;omega
  obtain ⟨P,_,hP⟩:=multiplier_degree (a:=w) (d:=0) dis cn (fun k hk=>by
    have e:k=0:=by omega
    rw [e,pow_zero,one_apply_eq_self]
    exact pure)
  have bound : (headFeatures c w).card≤(headSites c w).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro x hx
      obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
      exact headSites_mem j ((Finset.mem_filter.mp hj).2)
    · intro x hx y hy e
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hy
      apply Prod.ext e
      change w i=w j
      rw [hP i ((Finset.mem_filter.mp hi).2),hP j ((Finset.mem_filter.mp hj).2)]
      exact congrArg (fun z:K=>P.eval z) e
  refine ⟨bound.trans narrow,?_⟩
  obtain ⟨Q,_,u,hu,hG⟩:=full13_mesh_heads C
  have nz : G≠0 := by
    intro h
    have e:=C.meshDegree
    rw [h,natDegree_zero] at e
    omega
  have roots : offFeatures U c w ⊆ G.roots.toFinset := by
    intro z hz
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨noU,zero⟩:=(Finset.mem_filter.mp hj).2
    have uz:u j=0 := by
      by_contra nn;exact noU ⟨u,hu,nn⟩
    rw [Multiset.mem_toFinset,Polynomial.mem_roots nz,Polynomial.IsRoot.def]
    simpa only [uz,zero,mul_zero,zero_add] using hG j
  exact (((Finset.card_le_card roots).trans (Multiset.toFinset_card_le _)).trans
    (Polynomial.card_roots' G)).trans (le_of_eq C.meshDegree)

omit [CharZero K] in
theorem full13_forward_clock_step (C:Chart13 A 0 6 r U w G)
    {j:ℕ} (lo:7≤j) (hi:j≤9) :
    treeSpace A (j+1)=treeSpace A j⊔(treeSpace A j).map (diag (mirror A)) := by
  have e := C.chart j lo (by omega)
  have f := C.chart (j+1) (by omega) (by omega)
  simp only [treePlus,tailPlane,ite_true,sup_bot_eq] at e f
  let H:=treeSpace A j
  let Y:=diag (mirror A)
  have pol : polyBand A 6≤H := le_sup_left.trans e.ge
  have ch : Band13 A 6 r U w j≤H := le_sup_right.trans e.ge
  refine le_antisymm ?_ (sup_le (treeSpace_mono A (by omega)) (Submodule.map_le_iff_le_comap.mpr (mirror_treeSpace A j)))
  rw [f,←band13_next C lo]
  apply sup_le (pol.trans le_sup_left)
  apply sup_le (ch.trans le_sup_left)
  rintro x ⟨v,hv,rfl⟩
  have eq : diag (nodes A) v=v-Y v := by ext i;simp [Y,mirror,sub_mul]
  rw [eq]
  exact (H⊔H.map Y).sub_mem ((show H≤H⊔H.map Y from le_sup_left) (ch hv))
    ((show H.map Y≤H⊔H.map Y from le_sup_right) ⟨v,ch hv,rfl⟩)

omit [CharZero K] in
theorem full13_clock_step_restrict {n j:ℕ} (C:Chart13 A 0 6 r U w G)
    (lo:7≤j) (hi:j≤9) (e:Fin n→Fin (s+1)) (owner:Fin (s+1)→Fin n)
    (m:∀v∈treeSpace A 10,∀i,v (e (owner i))=v i) :
    treeSpace (compressMat A e (OwnerCompression.stencil owner)) (j+1)=
      treeSpace (compressMat A e (OwnerCompression.stencil owner)) j⊔
       (treeSpace (compressMat A e (OwnerCompression.stencil owner)) j).map
         (diag (mirror (compressMat A e (OwnerCompression.stencil owner)))) := by
  let R:=restrictCol (K:=K) e
  let B:=compressMat A e (OwnerCompression.stencil owner)
  have fit (v:Vec K (s+1)) : R (diag (mirror A) v)=diag (mirror B) (R v) := by
    ext i
    simp only [R,restrictCol_apply,diag_apply,B,OwnerCompression.restrict_mirror m]
  have eq : ((treeSpace A j).map (diag (mirror A))).map R =
       ((treeSpace A j).map R).map (diag (mirror B)) := by
    apply le_antisymm
    · rintro x ⟨_,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨R v,⟨v,hv,rfl⟩,(fit v).symm⟩
    · rintro x ⟨_,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨_,⟨v,hv,rfl⟩,fit v⟩
  change treeSpace B (j+1)=treeSpace B j⊔(treeSpace B j).map (diag (mirror B))
  have a: (treeSpace A (j+1)).map R=treeSpace B (j+1) :=
    OwnerCompression.restrict_treeSpace m (by omega)
  have d: (treeSpace A j).map R=treeSpace B j := OwnerCompression.restrict_treeSpace m (by omega)
  rw [←a,←d,full13_forward_clock_step C lo hi,Submodule.map_sup,eq]

/-- The kept stage count alone is not asserted to reach order twelve.
A genuine repair or the compressed reverse contradiction handles the one
remaining unary equation separately. -/
theorem full13_tied_owner_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (C:Chart13 A 0 6 r U w G) (e:Fin 17 ↪o Fin (s+1)) (owner:Fin (s+1)→Fin 17)
    (early:∀ i, e (owner i) ≤ i) (m:∀v∈treeSpace A 10,∀i,v (e (owner i))=v i) : False := by
  classical
  let B:=compressMat A e (OwnerCompression.stencil owner)
  let b0:=OwnerCompression.weightMerge b owner
  have paid:HasTreeOrderAtLeast A b 11 := fun t ht=>ho t (by omega)
  obtain ⟨ha',ho'⟩:=OwnerCompression.merged_lower_order e owner ha paid early m
  change StrictLower B at ha'
  change HasTreeOrderAtLeast B b0 11 at ho'
  have br : BranchedTop B b0 12 := by
    intro t u v ht
    change ((Tree.attach t (.attach u v)).density:K)*
      weight (compressMat A e (OwnerCompression.stencil owner)) b0 (.attach t (.attach u v))=1
    rw [OwnerCompression.actual_output_branched b e owner m ht]
    exact ho _ (by omega)
  have hn : ∃ i,b0 i≠0 := by
    by_contra! e
    have h:=ho' .leaf (by decide)
    simp [weight,e,Tree.density,Tree.childDensityProduct,Tree.order] at h
  let S:=Finset.univ.filter (fun i=>b0 i≠0)
  have ne:S.Nonempty := by
    obtain ⟨i,hi⟩:=hn
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let k:=S.max' ne
  have bk : b0 k≠0 := (Finset.mem_filter.mp (S.max'_mem ne)).2
  have later (j:Fin 17) (hej:k<j) : b0 j=0 := by
    by_contra hn
    exact (not_le_of_gt hej) (S.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  by_cases rz:reverseResidual B b0 0 k=0
  · have rr:=repair_partial_top ha' (by decide) ho' br bk later rz
    have h := RKCert.explicit_order12_ge18_field rr.1 rr.2
    omega
  · have r (j:ℕ) (lo:7≤j) (hi:j≤10) : finrank K (treeSpace B j)=j+7 := by
      change finrank K (treeSpace (compressMat A e (OwnerCompression.stencil owner)) j)=_
      rw [OwnerCompression.restrict_treeSpace_rank m hi]
      have h:=C.rich j lo hi
      rw [←zero_tail13_rank]
      simpa only [Nat.add_zero] using h
    have ct8 := full13_clock_step_restrict (j:=8) C (by decide) (by decide) e owner m
    have ct9 := full13_clock_step_restrict (j:=9) C (by decide) (by decide) e owner m
    have e2 := OwnerCompression.residual_merge_annih (j:=9) (k:=1) ho m (by decide) (by decide) (by decide)
    have e3 := OwnerCompression.residual_merge_annih (j:=9) (k:=2) ho m (by decide) (by decide) (by decide)
    have e4 := OwnerCompression.residual_merge_annih (j:=8) (k:=3) ho m (by decide) (by decide) (by decide)
    exact tied_reverse_contradiction_of_ranks ha' ho'
      (r 7 (by decide) (by decide)) (r 8 (by decide) (by decide))
      (r 9 (by decide) (by decide)) (r 10 (by decide) (by decide)) ct8 ct9 e2 e3 e4 ⟨k,later,rz⟩

omit [CharZero K] in
theorem order13_full_rank_two_four_impossible [LinearOrder K] [IsStrictOrderedRing K]
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 2 U w G)
    (h4:finrank K (zeroSpace A 4)=4) : False := by
  obtain ⟨v,C,alg,dis⟩:=full13_clean_four_head ha ho S M C h4
  have z4:v∈zeroSpace A 4 := by
    simpa only [pow_zero,one_apply_eq_self] using full13_four_power S C h4 (k:=0) (by decide)
  have z8:v*v∈zeroSpace A 8 := zeroSpace_mul (m:=4) (n:=4) z4 z4
  obtain ⟨P,pd,⟨a,eP⟩,ghost⟩:= full13_decompose ha ho S C z8
  rw [eP] at ghost
  have rk := C.marked.rank
  have cap : finrank K U+(headFeatures (nodes A) v).card+
      (offFeatures U (nodes A) v).card≤17 := by
    by_cases ga:a=0
    · subst a
      have ez : evalNodes A (0:K[X])=(0:Vec K (s+1)) := by ext i;simp
      rw [zero_smul,ez,sub_zero] at ghost
      by_cases wide:8≤(headSites (nodes A) v).card
      · exact (order13_full_wide_pure_impossible ha ho S M C alg dis ghost wide).elim
      · obtain ⟨x,y⟩:=full13_pure_feature_caps C dis ghost (by omega)
        omega
    · obtain ⟨x,y⟩:=full13_genuine_ghost_features C dis ga ghost
      omega
  have rank : finrank K (treeSpace A 10)=17 := by
    rw [←zero_tail13_rank]
    simpa only [Nat.add_zero] using C.rich 10 (by decide) (by decide)
  have band : treeSpace A 10≤LinearMap.range (polyEval A 6)⊔
      chain (diag (nodes A)) U v (headLen 6 6 2 10) := by
    have e:=C.chart 10 (by decide) (by decide)
    simpa only [treePlus,tailPlane,ite_true,sup_bot_eq,polyBand,Band13,forwardBand] using e.le
  obtain ⟨e,own,ear,mt,_⟩:=OwnerCompression.representatives_of_band 6 _ U v _ rank C.marked.stable alg dis band cap
  exact full13_tied_owner_impossible ha ho C e own ear mt

end RKCert.Paired.FiniteMidpoint
