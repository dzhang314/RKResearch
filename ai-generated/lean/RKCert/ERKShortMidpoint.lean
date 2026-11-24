module
public import RKCert.ERKFiniteMesh
public import RKCert.ERKFiniteStaircase

@[expose] public section

/-! # Low-width specialization of the common midpoint chart
The shared 16–19 chart used q≥8. Its actual rank, reverse and marked-edge
arguments use only q≥6. The same data structures and kernel-certified
linear algebra support the low finite orders without changing any frozen
declaration.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.ReverseHull RKCert.OneEscape Polynomial Module
variable {K : Type*} [Field K] [CharZero K] {s q ε d : ℕ}
variable {A : Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

theorem saturated_short {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:6≤q) (he:ε≤1)
    (hsize:s+1≤3*q+2*ε-1) : Saturated A b q ε := by
  have hsep:Separated A q := explicit_separated ha ho (by omega) (by omega)
  have hmin:=grade_five_surplus ha (hsep.mono (by omega : 5≤q))
  have grow (j:ℕ) (hj:5≤j) (hjq:j≤q) : j≤finrank K (zeroSpace A j) := by
    have h:=strict_rank_interval ha hsep 5 (j-5) (by decide) (by omega)
    rw [show 5+(j-5)=j by omega] at h
    omega
  have hfq:=grow q (by omega) le_rfl
  have eEq:=tree_rank_eq ho hsep (by omega)
  have hc:finrank K (treeSpace A q)+(q+2*ε-2)≤s+1 := by
    interval_cases ε
    · have h := backward_count ha ho q (q-2) (by omega)
      omega
    · have h := backward_endpoint_count ha ho q (q-1) (by omega) (by omega)
      omega
  have sz:s+1=3*q+2*ε-1 := by omega
  have fRank (j:ℕ) (hj:5≤j) (hjq:j≤q) : finrank K (zeroSpace A j)=j := by
    have hx:=strict_rank_interval ha hsep j (q-j) (by omega) (by omega)
    rw [show j+(q-j)=q by omega] at hx
    have hy:=grow j hj hjq
    omega
  have hn : finrank K (back A b 0)≤ε := by
    have hb:=backward_count ha ho q (q+ε-2) (by omega)
    omega
  have hprev:=tree_rank_eq ho (hsep.mono (show q-1≤q by omega)) (by omega)
  rw [fRank (q-1) (by omega) (by omega)] at hprev
  refine ⟨sz,?_,hsep,fRank,by omega,by omega,hn⟩
  intro hz
  have htrim := RKCert.Paired.OrderTwelve.order_trim ha ho hz
  have hlead := erk_stage_surplus_charZero_field (RKCert.Paired.OrderTwelve.trim_strict ha) htrim (by omega)
  interval_cases ε <;> omega

theorem midpoint_noninvariant_short {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (S:Saturated A b q ε)
    (hq:6≤q) {j:ℕ} (hj:5≤j) (uq:j≤q) :
    ¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j := by
  intro hinv
  have hC : ∀v∈zeroSpace A j,diag (nodes A) v∈zeroSpace A j := fun x hx =>
    hinv (Submodule.mem_map_of_mem hx)
  by_cases h:j<q
  · have hcost := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=j) (by omega)
      (zeroSpace A j) le_rfl hC
    rw [S.fRank j hj uq,S.fRank (j+1) (by omega) (by omega)] at hcost
    omega
  · have he:j=q := by omega
    subst j
    have hC' : ∀v∈zeroSpace A (q-1+1),diag (nodes A) v∈zeroSpace A (q-1+1) := by
      rwa [show q-1+1=q by omega]
    have H:=RKCert.Endpoint.forward_invariant_incoming_rank ha ho (j:=q-1) (by omega) hC'
    rw [show q-1+1=q by omega,S.fRank (q-1) (by omega) (by omega),S.fRank q (by omega) le_rfl] at H
    omega

theorem head_chart_short {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (S:Saturated A b q ε)
    (hq:6≤q) : ∃ r U w,HeadChart A q r U w := by
  let C:=diag (nodes A)
  let F:=zeroSpace A
  have flat (j:ℕ) (h:5≤j) (hj:j<q) : finrank K (F (j+1))≤finrank K (F j)+1 := by
    change finrank K (zeroSpace A (j+1))≤finrank K (zeroSpace A j)+1
    rw [S.fRank (j+1) (by omega) (by omega),S.fRank j h hj.le]
  obtain ⟨r,U,w,rp,hU,he,_,h5,_,_,hr,hn,_⟩:=Clock.ordinary_normal_head A 5 (flat 5 le_rfl (by omega))
    (midpoint_noninvariant_short ha ho S hq le_rfl (by omega))
  have G:=RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=5) (by omega) U he
    (fun x hx=>hU (Submodule.mem_map_of_mem hx))
  change finrank K U+3≤finrank K (zeroSpace A 6) at G
  rw [S.fRank 6 (by omega) (by omega)] at G
  rw [S.fRank 5 le_rfl (by omega)] at hr
  have hchart:=Clock.ordinary_staircase hU rp h5
    (h:=q-5) (fun k hk=>flat _ (by omega) (by omega))
    (fun k hk=>midpoint_noninvariant_short ha ho S hq (by omega) (by omega))
  have p (j:ℕ) (hj:5≤j) (hjq:j≤q) : zeroSpace A j=OneEscape.chain C U w (r+(j-5)) := by
    have H:=hchart (j-5) (by omega)
    rwa [show 5+(j-5)=j by omega] at H
  have eq : r+(q-5)+1=r+(q-4) := by omega
  have e : F q⊔(F q).map C = OneEscape.chain C U w (r+(q-4)) := by
    change zeroSpace A q⊔(zeroSpace A q).map C=_
    rw [p q (by omega) le_rfl,OneEscape.chain_sup_map hU (by omega),eq]
  have lt : F q<F q⊔(F q).map C := lt_of_le_of_ne le_sup_left
    (fun hh=>midpoint_noninvariant_short ha ho S hq (by omega) le_rfl (le_sup_right.trans (le_of_eq hh.symm)))
  have cap:=RKCert.Paired.OrderTwelve.chain_rank_cap (A:=A) (U:=U) (w:=w) (r+(q-4))
  have rk:=Submodule.finrank_lt_finrank_of_lt lt
  change finrank K (zeroSpace A q)<finrank K ↥(F q⊔(F q).map C) at rk
  rw [S.fRank q (by omega) le_rfl] at rk
  rw [←e] at cap
  have sum_rank : finrank K ↥(F q⊔(F q).map C)=q+1 := by omega
  exact ⟨r,U,w,by omega,hr.symm,hU,he,hn,p,e,sum_rank⟩

omit [CharZero K] in
theorem margin_short {q ε:ℕ} (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:6≤q) (he:ε≤1) (S:Saturated A b q ε) :
    Margin A b q ε (ε-finrank K (back A b 0)) := by
  classical
  let d:=ε-finrank K (back A b 0)
  have dd : d+finrank K (back A b 0)=ε := by
    dsimp [d];have := S.seedCap;omega
  have d1 : d≤1 := by omega
  have hs0 (h:d≠0) : backSeed1 A b=0 := by
    apply seed_zero_of_rank_zero
    omega
  have no : ∀ j,Fin.last s<j→b j=0 := fun _ hj=>False.elim ((not_lt_of_ge (Fin.le_last _)) hj)
  have hnode (h:d≠0) : nodes A (Fin.last s)=1 := (sub_eq_zero.mp
    (last_mirror_zero ha S.lastLive no (hs0 h))).symm
  have htail (n:ℕ) : back A b n≤annih (tailPlane K s d) := by
    intro w hw
    apply mem_annih.mpr
    by_cases h:d=0
    · intro v hv
      have hz:v=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,h] using hv)
      rw [hz,map_zero]
    · rw [tailPlane,ite_eq_right h]
      change Submodule.span K {terminal s} ≤ (row w).ker
      apply (Submodule.span_singleton_le_iff_mem ..).mpr
      change row w (terminal s)=0
      rw [row_terminal]
      exact back_vanish ha S.lastLive no (hs0 h) n hw _ le_rfl
  have dis : treeSpace A q⊓tailPlane K s d=⊥ := by
    by_cases h:d=0
    · simp [tailPlane,h]
    · apply le_antisymm _ bot_le
      intro u hu
      obtain ⟨hE,hT⟩:=Submodule.mem_inf.mp hu
      rw [tailPlane,ite_eq_right h] at hT
      obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hT
      have ne : terminal (K:=K) s ∉treeSpace A q :=
        terminal_single_not_mem ha ho (by omega : 2*q+1≤2*q+ε) _ S.lastLive (hnode h)
      have az : a=0 := by
        by_contra hn
        exact ne (((treeSpace A q).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr hn)).mp hE)
      rw [az,zero_smul]
      exact (⊥:Submodule K (Vec K (s+1))).zero_mem
  have Eplus (j:ℕ) (h:j≤q) : finrank K (treePlus A d j)=finrank K (treeSpace A j)+d := by
    have small : treeSpace A j⊓tailPlane K s d=⊥ := by
      exact le_antisymm ((inf_le_inf (treeSpace_mono A h) le_rfl).trans (le_of_eq dis)) bot_le
    have ht := Submodule.finrank_sup_add_finrank_inf_eq (treeSpace A j) (tailPlane K s d)
    rw [Submodule.finrank_eq_zero.mpr small,Nat.add_zero,tail_rank d d1] at ht
    exact ht
  refine ⟨dd,hnode,dis,htail,(Eplus _ le_rfl).trans (by rw [S.eMid]),
    (Eplus _ (by omega)).trans (by rw [S.ePrev]),?_⟩
  intro j hj
  let n:=2*q+ε-2-j
  have hb : back A b n≤annih (treePlus A d j) := by
    intro w hw
    apply mem_annih.mpr
    change treePlus A d j≤(row w).ker
    exact sup_le (mem_annih.mp (back_annih ho j n (by dsimp [n];omega) hw))
      (mem_annih.mp (htail n hw))
  have hcap:=finrank_annih_le hb
  have hr:=back_finrank ha ho n (by dsimp [n];omega)
  have sz:=S.size
  change finrank K (back A b 0)+n≤finrank K (back A b n) at hr
  change finrank K (treePlus A d j)≤q+j+1+d
  have hn : n+j+2=2*q+ε := by dsimp [n];omega
  omega

omit [CharZero K] in
theorem even_terminal_column_short {q:ℕ} (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b (2*q)) (hq:6≤q) (S:Saturated A b q 0) :
    nodes A (Fin.last s)=1 ∧ terminal (K:=K) s∈treeSpace A q := by
  have h0 : finrank K (back A b 0)=0 := by have := S.seedCap;omega
  have hz := seed_zero_of_rank_zero h0
  have no : ∀ j,Fin.last s<j→b j=0 := fun _ hj=>False.elim ((not_lt_of_ge (Fin.le_last _)) hj)
  have hy:=last_mirror_zero ha S.lastLive no hz
  refine ⟨(sub_eq_zero.mp hy).symm,?_⟩
  have l := back_finrank ha ho (q-2) (by omega)
  have h := back_annih ho q (q-2) (by omega)
  have hc := RKCert.Paired.OrderTwelve.backward_exact_dim (treeSpace A q)
  have exactBack : back A b (q-2)=annih (treeSpace A q) := by
    apply Submodule.eq_of_le_of_finrank_le h
    have := S.eMid
    have := S.size
    omega
  apply row_annih_test
  intro w hw
  rw [←exactBack] at hw
  rw [row_terminal]
  exact back_vanish ha S.lastLive no hz (q-2) hw _ le_rfl

theorem even_last_zero_short {q:ℕ} (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b (2*q)) (hq:6≤q) (S:Saturated A b q 0) :
    ∀ v∈zeroSpace A q,v (Fin.last s)=0 := by
  have ⟨_,h⟩:=even_terminal_column_short ha ho hq S
  have hprev (v) (hv:v∈zeroSpace A (q-1)) : v (Fin.last s)=0 := by
    have hprod := zeroSpace_mul_treeSpace ho (by omega : q+1≤2*q) hv h
    have hp := probe_zeroSpace ho (k:=0) (by omega) hprod
    change probe A b 0 (v*terminal s)=0 at hp
    rw [mul_comm,terminal_mul,map_smul,smul_eq_mul] at hp
    have ev : probe A b 0 (terminal s)=b (Fin.last s) := by
      rw [show probe A b 0 (terminal s)=row b (terminal s) by simp [probe],row_terminal]
    rw [ev] at hp
    exact (mul_eq_zero.mp hp).resolve_right S.lastLive
  have eq:=Clock.ordinary_step (A:=A) (j:=q-1)
    (by rw [show q-1+1=q by omega,S.fRank q (by omega) le_rfl,S.fRank (q-1) (by omega) (by omega)];omega)
    (midpoint_noninvariant_short (ε:=0) ha (by simpa using ho) S hq (by omega) (by omega))
  rw [show q-1+1=q by omega] at eq
  intro v hv
  rw [eq] at hv
  obtain ⟨u,hu,_,⟨w,hw,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hv
  simp [hprev u hu,hprev w hw]

theorem marked_head_short (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:6≤q)
    (he:ε≤1) (S:Saturated A b q ε) (M:Margin A b q ε d) : ∃ r U w,MarkedHead A q d r U w := by
  obtain ⟨r,U,w,H⟩:=head_chart_short ha ho S hq
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
theorem plus_midpoint_sup_short (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:6≤q) :
    treePlus A d q=polyBand A q⊔defectPlus A d q := by
  unfold treePlus defectPlus
  rw [treeSpace_sup ho (by omega),sup_assoc]

omit [CharZero K] in
theorem band_start_noalias_short (_ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:6≤q) (M:Margin A b q ε d)
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
theorem band_start_alias_short (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:6≤q) (M:Margin A b q ε d)
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

theorem firstEscape_last_zero_short (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q))
    (hq:6≤q) (S:Saturated A b q 0) {v:Vec K (s+1)} (hv:v∈firstEscape A 0 q) :
    v (Fin.last s)=0 := by
  have hm : v∈zeroSpace A q⊔(zeroSpace A q).map (diag (nodes A)) := by
    simpa [firstEscape,tailPlane] using hv
  obtain ⟨u,hu,_,⟨w,hw,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hm
  rw [Pi.add_apply,diag_apply,even_last_zero_short ha ho hq S _ hu,even_last_zero_short ha ho hq S _ hw,mul_zero,add_zero]

theorem edge_noninvariant_short (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:6≤q) (M:Margin A b q ε d)
    {j:ℕ} (hlo:q≤j) (hhi:j+4≤2*q+ε)
    (rNow:finrank K (treePlus A d j)=q+j+1+d)
    (rPrev:finrank K (treePlus A d (j-1))=
      if j=q then 2*q-1+d else q+j+d) :
    ¬ (treePlus A d j).map (diag (nodes A))≤treePlus A d j := by
  intro h
  have eq:j-1+1=j := by omega
  have hnew : (treePlus A d (j-1+1)).map (diag (nodes A))≤treePlus A d (j-1+1) := by rw [eq];exact h
  by_cases hqj:j=q
  · have r := finite_reverse_gain ha ho d (j-1) 3 (by decide) (by decide) (by omega) (by omega) M.atOne hnew
    rw [eq,rNow,rPrev,ite_eq_left hqj] at r
    omega
  · have r := finite_reverse_gain ha ho d (j-1) 2 (by decide) (by decide) (by omega) (by omega) M.atOne hnew
    rw [eq,rNow,rPrev,ite_eq_right hqj] at r
    omega

theorem band_step_short (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:6≤q) (M:Margin A b q ε d)
    {a j n:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hlo:q≤j) (hhi:j+4≤2*q+ε) (ha':a+1≤j) (hn:0<n) (hU:U.map (diag (nodes A))≤U)
    (E:treePlus A d j=polyBand A a⊔chain (diag (nodes A)) U w n)
    (rNow:finrank K (treePlus A d j)=q+j+1+d)
    (rPrev:finrank K (treePlus A d (j-1))=
      if j=q then 2*q-1+d else q+j+d) :
    treePlus A d (j+1)=polyBand A a⊔chain (diag (nodes A)) U w (n+1) ∧
      finrank K (treePlus A d (j+1))=q+(j+1)+1+d := by
  let Z:=treePlus A d j⊔(treePlus A d j).map (diag (nodes A))
  have hne : treePlus A d j<Z := lt_of_le_of_ne le_sup_left
    (fun e=>edge_noninvariant_short ha ho hq M hlo hhi rNow rPrev (le_sup_right.trans (le_of_eq e.symm)))
  have hin : Z≤treePlus A d (j+1) := sup_le (Eplus_mono A d (by omega)) (Eplus_clock A d j)
  have low := Submodule.finrank_lt_finrank_of_lt hne
  have mid := Submodule.finrank_mono hin
  have high := M.cap (j+1) (by omega)
  have eq := Submodule.eq_of_le_of_finrank_le hin (by omega)
  exact ⟨eq.symm.trans (Eplus_band_growth ha' hn hU E),by omega⟩

theorem band_staircase_short (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε))
    (hq:6≤q) (M:Margin A b q ε d)
    {a l:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}
    (hlo:q≤a+1) (hL:0<l) (hU:U.map (diag (nodes A))≤U)
    (E:treePlus A d (a+1)=polyBand A a⊔chain (diag (nodes A)) U w l)
    (rNow:finrank K (treePlus A d (a+1))=q+(a+1)+1+d)
    (rPrev:finrank K (treePlus A d ((a+1)-1))=
      if a+1=q then 2*q-1+d else q+(a+1)+d) :
    ∀ k,a+1+k≤2*q+ε-3→
      treePlus A d (a+1+k)=polyBand A a⊔chain (diag (nodes A)) U w (l+k) ∧
      finrank K (treePlus A d (a+1+k))=q+(a+1+k)+1+d ∧
      finrank K (treePlus A d ((a+1+k)-1))=
        if a+1+k=q then 2*q-1+d else q+(a+1+k)+d := by
  intro k
  induction k with
  | zero => intro _;simpa only [Nat.add_zero] using And.intro E (And.intro rNow rPrev)
  | succ n ih =>
    intro bound
    obtain ⟨e,r,prev⟩:=ih (by omega)
    obtain ⟨e',r'⟩:=band_step_short ha ho hq M (j:=a+1+n) (n:=l+n)
      (by omega) (by omega) (by omega) (by omega) hU e r prev
    have eq:a+1+(n+1)=a+1+n+1 := by omega
    rw [eq,show a+1+n+1-1=a+1+n by omega,ite_eq_right (by omega)]
    exact ⟨e',r',by omega⟩

end RKCert.Paired.FiniteMidpoint
