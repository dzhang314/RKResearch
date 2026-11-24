module
public import RKCert.ERKOrder13JointAffine
public import RKCert.ERKOrder13JointPencil
public import RKCert.GradeFiveSpace

@[expose] public section
/-! # Two short-head branches with actual quadratic-seed payments -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape RKCert.Paired.OrderTwelve
  RKCert.Endpoint Module Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 3900000

theorem marked13_F3_not_invariant (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (h4:finrank K (zeroSpace A 4)=3) :
    ¬(defectPlus A 1 3).map (diag (nodes A))≤defectPlus A 1 3 := by
  let D:=diag (nodes A)
  have f3:=grade_three_eq_two_13 ha ho S h4
  intro h
  have raw : (zeroSpace A 3).map D≤zeroSpace A 3 := by
    rintro _ ⟨v,hv,rfl⟩
    have vF : v∈defectPlus A 1 3 := (show zeroSpace A 3≤defectPlus A 1 3 from le_sup_left) hv
    have dF:D v∈defectPlus A 1 3 := h (Submodule.mem_map_of_mem vF)
    obtain ⟨u,hu,e,he,eq⟩:=Submodule.mem_sup.mp dF
    have both : (zeroSpace A 4)⊓tailPlane K s 1=⊥ :=
      disjoint_tail_of_order ho S.lastLive (V:=zeroSpace A 4) le_rfl (by decide)
    have pay:e∈zeroSpace A 4 := by
      have form:e=D v-u := by rw [←eq];abel
      rw [form]
      exact (zeroSpace A 4).sub_mem (diag_zeroSpace A 3 hv) (zeroSpace_mono A (by decide) hu)
    have e0:e=0 := (Submodule.mem_bot K).mp (both ▸ ⟨pay,he⟩)
    rw [e0,add_zero] at eq
    rwa [←eq]
  have jump:=forward_invariant_hermite_rank ha ho (j:=3) (by decide) (zeroSpace A 3)
    le_rfl (fun _ hv=>raw (Submodule.mem_map_of_mem hv))
  change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at jump
  omega

theorem marked13_no_invariant_quadratic_line (ha:StrictLower A)
    (hS:Separated A 6) :
    ¬(mat A (qdef A)∈(K ∙ qdef A) ∧ diag (nodes A) (qdef A)∈(K ∙ qdef A)) := by
  rintro ⟨am,cd⟩
  let W : Submodule K (Vec K (s+1)) := K ∙ qdef A
  have put (N:Vec K (s+1)→ₗ[K] Vec K (s+1)) (hn:N (qdef A)∈W) :
      ∀v∈W,N v∈W := by
    intro v vv
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp vv
    rw [map_smul]
    exact W.smul_mem _ hn
  have seed : (2:K) • mat A (diag (nodes A) 1)-diag (nodes A) (diag (nodes A) 1)∈W := by
    rw [←qdef_seed]
    exact W.smul_mem _ (Submodule.mem_span_singleton_self _)
  have act:=mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 W
    (put _ am) (put _ cd) seed
  have leF : W≤zeroSpace A 6 := (Submodule.span_singleton_le_iff_mem ..).mpr
    (zeroSpace_mono A (by decide) (qdef_mem A))
  have e : diag (nodes A) (1:Vec K (s+1))=nodes A := by ext i;simp
  rw [e] at act
  exact nodes_not_zeroSpace hS (by decide) (leF act)

theorem marked13_short_affine_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (hr:3≤r) {k:ℕ} (sk:k≤3) (budget:r+k≤6)
    {v:Vec K (s+1)} (vk:v∈defectPlus A 1 k) (vn:v∉U)
    (head:v∈chain (diag (nodes A)) U w 1)
    (sq:v*v∈chain (diag (nodes A)) U w (k+1)) : False := by
  have v3 := Fplus_mono A 1 sk vk
  have v5 := Fplus_mono A 1 (by omega : k≤5) vk
  have hm:=marked13_multiplier_stable ha ho S M C v3
  obtain ⟨α,u,P,an,hu,aff,pn,pd,mult⟩:=affine_profile_of_square (by omega) hm vn head sq
  obtain ⟨Q,Qd,fact⟩:=marked13_affine_literal C hr hm α an u hu aff pn (by omega) mult
  have gn:G≠0 := by intro z;have g:=C.meshDegree;rw [z,natDegree_zero] at g;omega
  have qn:Q≠0 := by
    intro e
    rw [e,mul_zero,smul_eq_zero] at fact
    exact gn (fact.resolve_left an)
  have pf : P∣G := by
    refine ⟨α⁻¹•Q,?_⟩
    have f:=congrArg (fun z:K[X]=>α⁻¹•z) fact
    simpa only [smul_smul,inv_mul_cancel₀ an,one_smul,mul_smul_comm] using f
  rcases C.shape with rfl|⟨rfl,_⟩
  · have g:=congrArg natDegree fact
    rw [natDegree_smul G an,C.meshDegree,natDegree_mul pn qn] at g
    exact marked13_joint_unaliased_impossible ha ho S M C hm mult v5 pn (by omega) pf
      (fun B h=>Fplus_mono A 1 (by omega) (marked_weight_from_grade B vk))
      (fun B h=>Fplus_mono A 1 (by omega) (marked_weight_from_grade B vk))
  · have pay : weightedEval (nodes A) v X∈defectPlus A 1 5 :=
      Fplus_mono A 1 (by rw [natDegree_X];omega) (marked_weight_from_grade X vk)
    exact marked13_joint_alias_impossible ha S M C hm mult v5 pay pn (by omega) pf

theorem marked13_rank_three_low_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 3 U w G)
    (h4:finrank K (zeroSpace A 4)=3) : False := by
  let d:=qdef A
  let v:=mat A d
  let I:=U⊓zeroSpace A 3
  have Ud : finrank K U=3 := by have h:=C.marked.rank;omega
  have F3:=grade_three_eq_two_13 ha ho S h4
  have d2:d∈zeroSpace A 2:=qdef_mem A
  have dn:d≠0:=qdef_ne_zero ha (S.separated.mono (by decide : 5≤6))
  have dU:d∈U := marked13_lower_into_core ho S M C.marked (k:=2) (by decide) (by decide)
    ((show zeroSpace A 2≤defectPlus A 1 2 from le_sup_left) d2)
  have not_all : ¬zeroSpace A 3≤U := by
    intro inc
    have f3p:finrank K (defectPlus A 1 3)=3 := by rw [marked13_defect_rank ho M S 3 (by decide),F3]
    have incl:defectPlus A 1 3≤U:=sup_le inc (marked13_terminal_in_core C)
    have eq := Submodule.eq_of_le_of_finrank_le incl (by omega)
    exact marked13_F3_not_invariant ha ho S h4 (by rw [eq];exact C.marked.stable)
  have Ilt:I<zeroSpace A 3 := lt_of_le_of_ne inf_le_right (by
    intro e
    have inc:I≤U:=inf_le_left
    rw [e] at inc
    exact not_all inc)
  have Idim := Submodule.finrank_lt_finrank_of_lt Ilt
  have dI : d∈I := Submodule.mem_inf.mpr ⟨dU,zeroSpace_mono A (by decide) d2⟩
  have eqId : (K ∙ d)=I := by
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr dI)
    rw [finrank_span_singleton dn]
    omega
  have v3:v∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 d2
  have vn:v∉U := by
    intro hv
    have vI : v∈I:=⟨hv,v3⟩
    have cI : diag (nodes A) d∈I := ⟨C.marked.stable ⟨d,dU,rfl⟩,diag_zeroSpace A 2 d2⟩
    rw [←eqId] at vI cI
    exact marked13_no_invariant_quadratic_line ha S.separated ⟨vI,cI⟩
  have vp:v∈defectPlus A 1 3 := (show zeroSpace A 3≤defectPlus A 1 3 from le_sup_left) v3
  have h:v∈chain (diag (nodes A)) U w 1 :=
    marked13_lower_into_core ho S M C.marked (k:=3) (by decide) (by decide) vp
  have raw:v*v∈defectPlus A 1 6 := Fplus_mul (j:=3) (k:=3) vp vp
  rw [C.marked.paid 6 (by decide) le_rfl] at raw
  exact marked13_short_affine_impossible ha ho S M C (by decide) (by decide) (by decide) vp vn h raw

theorem marked13_rank_four_outside_impossible (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a 4 U w G)
    (outside:qdef A∉U) : False := by
  let d:=qdef A
  have dp:d∈defectPlus A 1 2 := (show zeroSpace A 2≤defectPlus A 1 2 from le_sup_left) (qdef_mem A)
  have h:d∈chain (diag (nodes A)) U w 1 :=
    marked13_lower_into_core ho S M C.marked (k:=2) (by decide) (by decide) dp
  have s:d*d∈chain (diag (nodes A)) U w 3 :=
    marked13_lower_into_core ho S M C.marked (k:=4) (by decide) (by decide) (Fplus_mul (j:=2) (k:=2) dp dp)
  exact marked13_short_affine_impossible ha ho S M C (by decide) (by decide) (by decide) dp outside h s

end RKCert.Paired.FiniteMidpoint
