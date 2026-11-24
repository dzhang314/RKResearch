module

public import RKCert.ERKLogarithmic
public import RKCert.ExplicitOrderTwelve
public import RKCert.FixedKnotCases
public import RKCert.FreeQuasiGate

@[expose] public section

/-! # Exact midfield rank census for the finite ERK threshold
The midpoint of the physical order 2q+ε is separated through q.
We keep saturated tableaux and the trailing coordinate explicit. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired Polynomial Module

variable {K:Type*} [Field K] [CharZero K]
variable {s p:ℕ} {A : Fin s→Fin s→K} {b : Vec K s}

noncomputable def polyBand (A : Fin s→Fin s→K) (q:ℕ) : Submodule K (Vec K s) :=
  LinearMap.range (polyEval A q)

omit [CharZero K] in
theorem polyBand_le (A : Fin s→Fin s→K) {q j:ℕ} (h:q≤j) :
    polyBand A q≤treeSpace A j := by
  rintro _ ⟨a,rfl⟩
  exact treeSpace_mono A h (polyEval_mem_treeSpace A q a)

omit [CharZero K] in
theorem eval_polyBand {A:Fin s→Fin s→K} {q:ℕ} {P:K[X]} (h:P.natDegree≤q) :
    evalNodes A P∈polyBand A q := ⟨_,(evalNodes_eq_polyEval A P h).symm⟩

omit [CharZero K] in
theorem treeSpace_sup (ha:HasTreeOrderAtLeast A b p) {q:ℕ} (hq:q+1≤p) :
    treeSpace A q=polyBand A q⊔zeroSpace A q := by
  apply le_antisymm ?_ (sup_le (polyBand_le A le_rfl) (zeroSpace_le_treeSpace A q))
  intro v hv
  obtain ⟨a,hz⟩:=exists_poly_zeroSpace ha hq hv
  exact Submodule.mem_sup.mpr ⟨polyEval A q a,⟨a,rfl⟩,v-polyEval A q a,hz,by abel⟩

omit [CharZero K] in
theorem poly_band_rank_add {A:Fin s→Fin s→K} {q:ℕ} {Z:Submodule K (Vec K s)}
    (h: ∀ a:Fin (q+1)→K, polyEval A q a∈Z → a=0) :
    finrank K ↥(polyBand A q⊔Z)=q+1+finrank K Z := by
  have hi : Function.Injective (polyEval A q) :=
    (injective_iff_map_eq_zero _).mpr fun a e=>h a (e ▸ Z.zero_mem)
  have hr : finrank K (polyBand A q)=q+1 := by
    unfold polyBand
    rw [LinearMap.finrank_range_of_inj hi,Module.finrank_fin_fun]
  have hinf : polyBand A q⊓Z=⊥ := by
    refine le_antisymm (fun v hv=>?_ ) bot_le
    obtain ⟨a,rfl⟩:=hv.1
    rw [h a hv.2,map_zero]
    exact Submodule.zero_mem _
  have hx:=Submodule.finrank_sup_add_finrank_inf_eq (polyBand A q) Z
  rw [hr,Submodule.finrank_eq_zero.mpr hinf,Nat.add_zero] at hx
  exact hx

omit [CharZero K] in
theorem tree_rank_eq (ho:HasTreeOrderAtLeast A b p) {q:ℕ}
    (hsep:Separated A q) (hq:q+1≤p) :
    finrank K (treeSpace A q)=q+1+finrank K (zeroSpace A q) := by
  rw [treeSpace_sup ho hq]
  exact poly_band_rank_add ((separated_iff_coeff A q).mp hsep)

theorem strict_rank_interval {A:Fin s→Fin s→K} (ha:StrictLower A)
    {q:ℕ} (hs:Separated A q) (n d:ℕ) (hn:1≤n) (h:n+d≤q) :
    finrank K (zeroSpace A n)+d≤finrank K (zeroSpace A (n+d)) := by
  induction d with
  | zero => simp only [Nat.add_zero,le_refl]
  | succ d ih =>
    have h1:=ih (by omega)
    have h2:=Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separated ha hs
      (j:=n+d) (by omega) h)
    change finrank K (zeroSpace A (n+d))<finrank K (zeroSpace A (n+d+1)) at h2
    change finrank K (zeroSpace A n)+(d+1)≤finrank K (zeroSpace A (n+d+1))
    omega

structure Saturated (A : Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) (q ε:ℕ) : Prop where
  size : s+1=3*q+2*ε-1
  lastLive : b (Fin.last s)≠0
  separated : Separated A q
  fRank : ∀j,5≤j→j≤q→finrank K (zeroSpace A j)=j
  eMid : finrank K (treeSpace A q)=2*q+1
  ePrev : finrank K (treeSpace A (q-1))=2*q-1
  seedCap : finrank K (back A b 0)≤ε

theorem saturated {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (hq:8≤q) (he:ε≤1)
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

theorem midpoint_noninvariant {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (S:Saturated A b q ε)
    (hq:8≤q) {j:ℕ} (hj:5≤j) (uq:j≤q) :
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

structure HeadChart (A : Fin (s+1)→Fin (s+1)→K) (q r:ℕ)
    (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) : Prop where
  two : 2≤r
  rank : finrank K U+r=5
  stable : U.map (diag (nodes A))≤U
  early : U≤zeroSpace A 5
  norm : ∀ x,Clock.fiber (nodes A) x w∈U→Clock.fiber (nodes A) x w=0
  paid : ∀ j,5≤j→j≤q→zeroSpace A j=OneEscape.chain (diag (nodes A)) U w (r+(j-5))
  edge : (zeroSpace A q⊔(zeroSpace A q).map (diag (nodes A))) =
    OneEscape.chain (diag (nodes A)) U w (r+(q-4))
  edgeRank : finrank K ↥(zeroSpace A q⊔(zeroSpace A q).map (diag (nodes A)))=q+1

theorem head_chart {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {q ε:ℕ}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (2*q+ε)) (S:Saturated A b q ε)
    (hq:8≤q) : ∃ r U w,HeadChart A q r U w := by
  let C:=diag (nodes A)
  let F:=zeroSpace A
  have flat (j:ℕ) (h:5≤j) (hj:j<q) : finrank K (F (j+1))≤finrank K (F j)+1 := by
    change finrank K (zeroSpace A (j+1))≤finrank K (zeroSpace A j)+1
    rw [S.fRank (j+1) (by omega) (by omega),S.fRank j h hj.le]
  obtain ⟨r,U,w,rp,hU,he,_,h5,_,_,hr,hn,_⟩:=Clock.ordinary_normal_head A 5 (flat 5 le_rfl (by omega))
    (midpoint_noninvariant ha ho S hq le_rfl (by omega))
  have G:=RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=5) (by omega) U he
    (fun x hx=>hU (Submodule.mem_map_of_mem hx))
  change finrank K U+3≤finrank K (zeroSpace A 6) at G
  rw [S.fRank 6 (by omega) (by omega)] at G
  rw [S.fRank 5 le_rfl (by omega)] at hr
  have hchart:=Clock.ordinary_staircase hU rp h5
    (h:=q-5) (fun k hk=>flat _ (by omega) (by omega))
    (fun k hk=>midpoint_noninvariant ha ho S hq (by omega) (by omega))
  have p (j:ℕ) (hj:5≤j) (hjq:j≤q) : zeroSpace A j=OneEscape.chain C U w (r+(j-5)) := by
    have H:=hchart (j-5) (by omega)
    rwa [show 5+(j-5)=j by omega] at H
  have eq : r+(q-5)+1=r+(q-4) := by omega
  have e : F q⊔(F q).map C = OneEscape.chain C U w (r+(q-4)) := by
    change zeroSpace A q⊔(zeroSpace A q).map C=_
    rw [p q (by omega) le_rfl,OneEscape.chain_sup_map hU (by omega),eq]
  have lt : F q<F q⊔(F q).map C := lt_of_le_of_ne le_sup_left
    (fun hh=>midpoint_noninvariant ha ho S hq (by omega) le_rfl (le_sup_right.trans (le_of_eq hh.symm)))
  have cap:=RKCert.Paired.OrderTwelve.chain_rank_cap (A:=A) (U:=U) (w:=w) (r+(q-4))
  have rk:=Submodule.finrank_lt_finrank_of_lt lt
  change finrank K (zeroSpace A q)<finrank K ↥(F q⊔(F q).map C) at rk
  rw [S.fRank q (by omega) le_rfl] at rk
  rw [←e] at cap
  have sum_rank : finrank K ↥(F q⊔(F q).map C)=q+1 := by omega
  exact ⟨r,U,w,by omega,hr.symm,hU,he,hn,p,e,sum_rank⟩

end RKCert.Paired.FiniteMidpoint

