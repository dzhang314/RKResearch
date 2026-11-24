module
public import RKCert.ERKFiniteTail

@[expose] public section

/-! # Exact terminal-row and output steering for a genuine ERK order
The rank-one change and the reweight are on actual tree weights, not
merely the polynomial clock tests.
-/
namespace RKCert.Paired.TerminalSteering
open RKCert.Paired RKCert.Paired.FiniteMidpoint RKCert.Paired.OrderTwelve Module
variable {K:Type*} [Field K] {s p:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem stageWeight_eq_of_agrees {B:Fin (s+1)→Fin (s+1)→K} (hp:2≤p)
    (agree:∀v∈treeSpace A (p-2),mat B v=mat A v) :
    ∀ t:Tree,t.order≤p→stageWeight B t=stageWeight A t := by
  intro t
  induction t with
  | leaf => intro; rfl
  | attach u v hu hv =>
    intro ht
    have hoU:=u.order_pos
    have hoV:=v.order_pos
    change u.order+v.order≤p at ht
    have eq := agree (stageWeight A u) (stageWeight_mem_space A u (by omega))
    change mat B (stageWeight B u)*stageWeight B v=mat A (stageWeight A u)*stageWeight A v
    rw [hu (by omega),hv (by omega),eq]

theorem treeSpace_eq_of_stageWeights {B:Fin (s+1)→Fin (s+1)→K}
    (agree:∀t:Tree,t.order≤p→stageWeight B t=stageWeight A t) {j:ℕ} (hj:j+1≤p) :
    treeSpace B j=treeSpace A j := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,rfl⟩
    rw [agree t (ht.trans hj)]
    exact stageWeight_mem_space A t ht
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,rfl⟩
    rw [←agree t (ht.trans hj)]
    exact stageWeight_mem_space B t ht

theorem zeroSpace_eq_of_stageWeights {B:Fin (s+1)→Fin (s+1)→K}
    (agree:∀t:Tree,t.order≤p→stageWeight B t=stageWeight A t) {j:ℕ} (hj:j+1≤p) :
    zeroSpace B j=zeroSpace A j := by
  have norm (t:Tree) (ht:t.order≤p) : normTree B t=normTree A t := by rw [normTree,normTree,agree t ht]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,u,he,ht,rfl⟩
    rw [norm t (ht.trans hj),norm u (by omega)]
    exact normDiff_mem A t u he ht
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,u,he,ht,rfl⟩
    rw [←norm t (ht.trans hj),←norm u (by omega)]
    exact normDiff_mem B t u he ht

theorem backSeed_last (ha:StrictLower A) :
    backSeed1 A b (Fin.last s)=-(1-nodes A (Fin.last s))*b (Fin.last s) := by
  have hv := transMat_vanish ha (Fin.last s) b
    (fun i hi=>False.elim ((not_lt_of_ge (Fin.le_last i)) hi)) (Fin.last s) le_rfl
  change transMat A b (Fin.last s)=0 at hv
  rw [backSeed1,Pi.sub_apply,hv,diag_apply,zero_sub]
  change -((1-nodes A (Fin.last s))*b (Fin.last s))=_
  ring

noncomputable def steer (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (i j:Fin (s+1)) :=
  A i j-terminal s i*(backSeed1 A b j/b (Fin.last s))

theorem steer_strict (ha:StrictLower A) (h: nodes A (Fin.last s)=1) :
    StrictLower (steer A b) := by
  intro i j hij
  by_cases hi:i=Fin.last s
  · subst i
    have hj:j=Fin.last s := by
      have hn: j.val≤s := Nat.le_of_lt_succ j.isLt
      exact Fin.ext (by simpa using (Nat.le_antisymm hn hij))
    subst j
    simp [steer,ha _ _ hij,backSeed_last ha,h]
  · simp [steer,ha _ _ hij,terminal_at_ne hi]

theorem steer_agrees (ho:HasTreeOrderAtLeast A b p) (hp:2≤p) :
    ∀v∈treeSpace A (p-2),mat (steer A b) v=mat A v := by
  intro v hv
  have h0 := mem_annih.mp (backSeed1_annih ho (j:=p-2) (by omega)) v hv
  ext i
  simp only [mat_apply,steer,sub_mul,Finset.sum_sub_distrib]
  have e : (∑ j,terminal s i*(backSeed1 A b j/b (Fin.last s))*v j)=
      (terminal s i/b (Fin.last s))*row (backSeed1 A b) v := by
    rw [row_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e,h0,mul_zero,sub_zero]

theorem steer_nodes (ho:HasTreeOrderAtLeast A b p) (hp:2≤p) :
    nodes (steer A b)=nodes A := by
  ext i
  have h := congrFun (steer_agrees ho hp (stageWeight A .leaf)
    (stageWeight_mem_space A .leaf (by simp [Tree.order]))) i
  simpa [mat_apply,stageWeight,nodes] using h

theorem steer_backSeed_zero (ho:HasTreeOrderAtLeast A b p) (hp:2≤p)
    (hb:b (Fin.last s)≠0) : backSeed1 (steer A b) b=0 := by
  have e : transMat (steer A b) b=transMat A b-backSeed1 A b := by
    ext j
    simp only [mat_apply,steer,sub_mul,Finset.sum_sub_distrib,Pi.sub_apply]
    have h : (∑ i,terminal s i*(backSeed1 A b j/b (Fin.last s))*b i)=
        (backSeed1 A b j/b (Fin.last s))*row b (terminal s) := by
      rw [row_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h,row_terminal,div_mul_cancel₀ _ hb]
  rw [backSeed1,e,show mirror (steer A b)=mirror A from by unfold mirror;rw [steer_nodes ho hp]]
  unfold backSeed1
  abel

/-- At terminal clock 1, a strict final-row correction kills the first adjoint
without changing any stage tree of size at most the achieved order. -/
theorem terminal_one_steering (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:2≤p) (hb:b (Fin.last s)≠0) (h1:nodes A (Fin.last s)=1) :
    StrictLower (steer A b) ∧ HasTreeOrderAtLeast (steer A b) b p ∧
    (∀t:Tree,t.order≤p→stageWeight (steer A b) t=stageWeight A t) ∧
    nodes (steer A b)=nodes A ∧ backSeed1 (steer A b) b=0 := by
  have w:=stageWeight_eq_of_agrees hp (steer_agrees ho hp)
  refine ⟨steer_strict ha h1,?_,w,steer_nodes ho hp,steer_backSeed_zero ho hp hb⟩
  intro t ht
  simpa only [weight,w t ht] using ho t ht

noncomputable def newOutput (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) : Vec K (s+1) :=
  b+(1-nodes A (Fin.last s))⁻¹•backSeed1 A b

theorem newOutput_order (ho:HasTreeOrderAtLeast A b p) (hp:2≤p) :
    HasTreeOrderAtLeast A (newOutput A b) (p-1) := by
  intro t ht
  let x := stageWeight A t
  let α := (1-nodes A (Fin.last s))⁻¹
  have z := mem_annih.mp (backSeed1_annih ho (j:=p-2) (by omega)) x
    (stageWeight_mem_space A t (by omega))
  have eq : row (newOutput A b) x=row b x := by
    change rowL (b+α•backSeed1 A b) x=_
    rw [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,rowL_apply,rowL_apply,z,smul_zero,add_zero]
  change (t.density:K)*row (newOutput A b) x=1
  rw [eq]
  exact ho t (by omega)

theorem newOutput_last_zero (ha:StrictLower A) (h1:nodes A (Fin.last s)≠1) :
    newOutput A b (Fin.last s)=0 := by
  let u:=1-nodes A (Fin.last s)
  have un:u≠0 := sub_ne_zero.mpr h1.symm
  change b (Fin.last s)+u⁻¹*backSeed1 A b (Fin.last s)=0
  rw [backSeed_last ha]
  change b (Fin.last s)+u⁻¹*(-u*b (Fin.last s))=0
  field_simp
  ring

/-- A terminal clock different from 1 allows a genuine one-stage deletion
at order p−1, by changing only output weights and then trimming. -/
theorem terminal_off_one_trim (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hp:2≤p) (h1:nodes A (Fin.last s)≠1) :
    ∃ b' : Vec K s, HasTreeOrderAtLeast (trim A) b' (p-1) :=
  ⟨_,order_trim ha (newOutput_order ho hp) (newOutput_last_zero ha h1)⟩

end RKCert.Paired.TerminalSteering
