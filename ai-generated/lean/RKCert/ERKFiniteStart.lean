module
public import RKCert.ERKFiniteStaircase

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε d:ℕ}

noncomputable def firstEscape (A:Fin (s+1)→Fin (s+1)→K) (d q:ℕ) : Submodule K (Vec K (s+1)) :=
  (zeroSpace A q⊔(zeroSpace A q).map (diag (nodes A)))⊔tailPlane K s d

omit [CharZero K] in
theorem firstEscape_defect : firstEscape A d q≤defectPlus A d (q+1) :=
  sup_le_sup (sup_le (zeroSpace_mono A (Nat.le_succ _)) (Submodule.map_le_iff_le_comap.mpr
    (diag_zeroSpace A q))) le_rfl

omit [CharZero K] in
theorem add_tail_rank (M:Margin A b q ε d) (he:ε≤1) {V:Submodule K (Vec K (s+1))}
    (hi:V⊓tailPlane K s d=⊥) : finrank K ↥(V⊔tailPlane K s d)=finrank K V+d := by
  have h:=Submodule.finrank_sup_add_finrank_inf_eq V (tailPlane K s d)
  rw [Submodule.finrank_eq_zero.mpr hi,Nat.add_zero,tail_rank] at h
  · exact h
  · have := M.budget
    omega

omit [CharZero K] in
theorem disjoint_tail_of_order (ho:HasTreeOrderAtLeast A b p) (hLive:b (Fin.last s)≠0)
    {V:Submodule K (Vec K (s+1))} {j:ℕ} (hV:V≤zeroSpace A j) (hp:j+1≤p) :
    V⊓tailPlane K s d=⊥ := by
  classical
  by_cases h:d=0
  · simp [tailPlane,h]
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨hw,ht⟩:=Submodule.mem_inf.mp hv
  rw [tailPlane,ite_eq_right h] at ht
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp ht
  have hzero := probe_zeroSpace ho (k:=0) (by omega) (hV hw)
  change probe A b 0 (a • terminal s)=0 at hzero
  have ee : probe A b 0 (terminal s)=b (Fin.last s) := by
    rw [show probe A b 0 (terminal s)=row b (terminal s) by simp [probe],row_terminal]
  rw [map_smul,ee,smul_eq_mul] at hzero
  rw [(mul_eq_zero.mp hzero).resolve_right hLive,zero_smul]
  exact (⊥:Submodule K (Vec K (s+1))).zero_mem

structure MarkedHead (A : Fin (s+1)→Fin (s+1)→K) (q d r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) : Prop where
  rTwo : 2≤r
  rank : finrank K U+r=5+d
  core : U≤defectPlus A d 5
  stable : U.map (diag (nodes A))≤U
  norm : ∀ a,fiber (nodes A) a w∈U→fiber (nodes A) a w=0
  paid : ∀j,5≤j→j≤q→defectPlus A d j=chain (diag (nodes A)) U w (r+(j-5))
  edge : firstEscape A d q=chain (diag (nodes A)) U w (r+(q-4))
  edgeRank : finrank K (firstEscape A d q)=q+1+d

theorem marked_head (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:8≤q)
    (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d) : ∃ r U w,MarkedHead A q d r U w := by
  obtain ⟨r,U,w,H⟩:=head_chart ha ho S hq
  let C := diag (nodes A)
  let T := tailPlane K s d
  let U' := U⊔T
  let w' := w-correction (nodes A) U' w
  have ht : U'.map C≤U' := by
    dsimp [U']
    rw [Submodule.map_sup]
    exact sup_le_sup H.stable (tail_clock d _)
  have e (n:ℕ) : chain C U' w' n=chain C U w n⊔T := by
    rw [show chain C U' w' n=chain C U' w n from chain_sub_head ht (correction_mem _ _ _) n]
    exact chain_add_core n
  have prev : finrank K U'=finrank K U+d := by
    apply add_tail_rank M he
    exact disjoint_tail_of_order ho S.lastLive H.early (by omega)
  have eh : firstEscape A d q=chain C U' w' (r+(q-4)) := by
    rw [e,←H.edge]
    rfl
  have er : finrank K (firstEscape A d q)=q+1+d := by
    unfold firstEscape
    rw [add_tail_rank M he,H.edgeRank]
    apply disjoint_tail_of_order (j:=q+1) ho S.lastLive ?_ (by omega)
    exact sup_le (zeroSpace_mono A (Nat.le_succ _)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A q))
  refine ⟨r,U',w',H.two,by have := H.rank;omega,sup_le_sup H.early le_rfl,ht,normalized _ _ _,?_,eh,er⟩
  intro j hj hjq
  rw [e,←H.paid j hj hjq]
  rfl

omit [CharZero K] in
theorem separated_plus (S:Saturated A b q ε) (M:Margin A b q ε d)
    (P:K[X]) (hP:P.natDegree≤q) (h:evalNodes A P∈defectPlus A d q) : P=0 := by
  obtain ⟨v,hv,t,ht,eq⟩:=Submodule.mem_sup.mp h
  have e : t=evalNodes A P-v := by rw [←eq];abel
  have hT' : t∈treeSpace A q := by
    rw [e]
    exact (treeSpace A q).sub_mem (evalNodes_mem_treeSpace A P hP) (zeroSpace_le_treeSpace A q hv)
  have tz : t=0 := (Submodule.mem_bot K).mp (M.noTail ▸ (Submodule.mem_inf.mpr ⟨hT',ht⟩))
  have hn : evalNodes A P∈zeroSpace A q := by rwa [←eq,tz,add_zero]
  exact S.separated _ hP hn

omit [CharZero K] in
theorem plus_midpoint_sup (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:8≤q) :
    treePlus A d q=polyBand A q⊔defectPlus A d q := by
  unfold treePlus defectPlus
  rw [treeSpace_sup ho (by omega),sup_assoc]

omit [CharZero K] in
theorem band_start_noalias (_ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:8≤q) (M:Margin A b q ε d)
    {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} (H:MarkedHead A q d r U w)
    (sep : ∀ P:K[X], P.natDegree≤q → evalNodes A P∈firstEscape A d q→P=0) :
    treePlus A d (q+1)=polyBand A q⊔firstEscape A d q ∧
      finrank K (treePlus A d (q+1))=2*q+2+d ∧
      ∃ G:K[X],G.natDegree=q+1 ∧ evalNodes A G∈firstEscape A d q := by
  have rSum := poly_band_rank_add (A:=A) (q:=q) (Z:=firstEscape A d q) (by
    intro c hc
    have eq : (by classical exact ofFn (q+1) c : K[X])=0 := by
      classical
      apply sep _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _))
      rwa [evalNodes_ofFn]
    classical
    ext i
    have he := congrArg (fun P:K[X]=>P.coeff i.val) eq
    rwa [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] at he)
  rw [H.edgeRank] at rSum
  have W : polyBand A q⊔firstEscape A d q ≤treePlus A d (q+1) := by
    apply sup_le ((polyBand_le A (by omega)).trans le_sup_left)
    exact firstEscape_defect.trans (sup_le_sup (zeroSpace_le_treeSpace A _) le_rfl)
  have rank:=M.cap (q+1) (by omega)
  have eq := (Submodule.eq_of_le_of_finrank_le W (by omega)).symm
  refine ⟨eq,by rw [eq,rSum];omega,?_⟩
  classical
  have h : evalNodes A (X^(q+1):K[X])∈treePlus A d (q+1) :=
    (show treeSpace A (q+1)≤treePlus A d (q+1) from le_sup_left)
      (evalNodes_mem_treeSpace A _ (by rw [natDegree_X_pow]))
  rw [eq] at h
  obtain ⟨v,⟨a,rfl⟩,z,hz,ev⟩:=Submodule.mem_sup.mp h
  let P:=ofFn (q+1) a
  let G:=X^(q+1)-P
  have deg : P.natDegree≤q := Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  have dg : G.natDegree=q+1 := by
    have hn : (X^(q+1):K[X]).natDegree=q+1 := natDegree_X_pow _
    change ((X^(q+1):K[X])-P).natDegree=q+1
    rw [natDegree_sub_eq_left_of_natDegree_lt (show P.natDegree < (X^(q+1):K[X]).natDegree by rw [hn];omega),hn]
  refine ⟨G,dg,?_⟩
  rw [show evalNodes A G=evalNodes A (X^(q+1):K[X])-polyEval A q a from by
    have hp:evalNodes A P=polyEval A q a:=evalNodes_ofFn A q a
    ext j
    rw [←hp]
    simp [G,evalNodes]]
  have e : evalNodes A (X^(q+1):K[X])-polyEval A q a=z := by rw [←ev];abel
  rwa [e]

omit [CharZero K] in
theorem band_start_alias (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:8≤q) (M:Margin A b q ε d)
    (he:ε≤1) (S:Saturated A b q ε) {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (H:MarkedHead A q d r U w)
    (low : ∀ P:K[X],P.natDegree≤q-1→evalNodes A P∈firstEscape A d q→P=0)
    (G:K[X]) (gd:G.natDegree=q) (gc:evalNodes A G∈firstEscape A d q) :
    treePlus A d q=polyBand A (q-1)⊔firstEscape A d q := by
  have hsmall : defectPlus A d q≤firstEscape A d q := sup_le_sup le_sup_left le_rfl
  have hn : evalNodes A G∉defectPlus A d q := by
    intro m
    have he := separated_plus S M G (by omega) m
    simp [he] at gd
    omega
  have rr : finrank K (defectPlus A d q)=q+d := by
    unfold defectPlus
    rw [add_tail_rank M (by omega),S.fRank q (by omega) le_rfl]
    exact disjoint_tail_of_order ho S.lastLive le_rfl (by omega)
  have e := sup_singleton_eq_of_rank hsmall gc hn (by rw [H.edgeRank,rr];omega)
  have hE : firstEscape A d q≤treePlus A d q := by
    rw [e]
    apply sup_le (sup_le_sup (zeroSpace_le_treeSpace A _) le_rfl)
    apply (Submodule.span_singleton_le_iff_mem ..).mpr
    exact (show treeSpace A q≤treePlus A d q from le_sup_left) (evalNodes_mem_treeSpace A G (by omega))
  have le' : polyBand A (q-1)⊔firstEscape A d q≤treePlus A d q :=
    sup_le ((polyBand_le A (by omega)).trans le_sup_left) hE
  have rSum := poly_band_rank_add (A:=A) (q:=q-1) (Z:=firstEscape A d q) (by
    intro c hc
    have eq : (by classical exact ofFn ((q-1)+1) c : K[X])=0 := by
      classical
      apply low _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _))
      rwa [evalNodes_ofFn]
    classical
    ext i
    have he := congrArg (fun P:K[X]=>P.coeff i.val) eq
    rwa [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] at he)
  rw [H.edgeRank] at rSum
  symm
  apply Submodule.eq_of_le_of_finrank_le le'
  have r0 := M.eMid
  omega

end RKCert.Paired.FiniteMidpoint

