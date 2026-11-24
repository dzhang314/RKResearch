module
public import RKCert.ERKFiniteStart
public import RKCert.ERKFinitePackets

@[expose] public section

/-! # Moment equations of the marked physical defects -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K] {s p q ε d j : ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}


theorem probe_eval_moment (ho : HasTreeOrderAtLeast A b p) (P:K[X]) (k:ℕ)
    (hk:k+P.natDegree+1≤p) :
    probe A b k (evalNodes A P)=scalarMoment P k := by
  classical
  rw [evalNodes_eq_polyEval A P le_rfl,probe_polyEval ho hk,scalarMoment]
  let a : Fin (P.natDegree+1)→K := fun i=>P.coeff i.val
  have h : ofFn (P.natDegree+1) a=P :=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have hm := primitive_monomial_moment a (1:K) k
  rw [h] at hm
  rw [hm]
  simp [moment,a,Nat.add_comm]

omit [CharZero K] in
theorem marked_eval_origin (ha:StrictLower A) (hs:s≠0) (P:K[X])
    (h:evalNodes A P∈defectPlus A d j) : P.coeff 0=0 := by
  obtain ⟨v,hv,t,ht,eq⟩ := Submodule.mem_sup.mp h
  have hn : (0:Fin (s+1))≠Fin.last s := by
    intro h
    have e := congrArg Fin.val h
    change 0=s at e
    exact hs e.symm
  have v0 : v (0:Fin (s+1))=0 := origin_zeroSpace A ha j hv
  have t0 := tail_supported ht hn
  have h0 : nodes A 0=0 := by
    unfold nodes
    exact Finset.sum_eq_zero fun i _ => ha _ _ (Fin.zero_le i)
  have e := congrFun eq (0:Fin (s+1))
  rw [coeff_zero_eq_eval_zero]
  simpa only [Pi.add_apply,v0,t0,add_zero,evalNodes_apply,h0] using e.symm

theorem marked_eval_moments (ho : HasTreeOrderAtLeast A b p) (P:K[X])
    (h:evalNodes A P∈defectPlus A d j) (jdeg : P.natDegree ≤ j)
    (atOne : d≠0→nodes A (Fin.last s)=1) :
    ∃ μ:K,(d=0→μ=0) ∧ ∀ k,k+j+1≤p→scalarMoment P k=μ := by
  classical
  obtain ⟨v,hv,t,ht,eq⟩ := Submodule.mem_sup.mp h
  by_cases dh:d=0
  · have tz : t=0 := (Submodule.mem_bot K).mp (by simpa [tailPlane,dh] using ht)
    refine ⟨0,fun _=>rfl,?_⟩
    intro k hk
    rw [← probe_eval_moment ho P k (by omega), ←eq,tz,add_zero]
    exact probe_zeroSpace ho hk hv
  · rw [tailPlane,ite_eq_right dh] at ht
    obtain ⟨α,rfl⟩:=Submodule.mem_span_singleton.mp ht
    refine ⟨α*b (Fin.last s),fun hd=>False.elim (dh hd),?_⟩
    intro k hk
    rw [←probe_eval_moment ho P k (by omega), ←eq,map_add,probe_zeroSpace ho hk hv,zero_add,
      map_smul,smul_eq_mul]
    unfold probe
    rw [row_terminal,atOne dh,one_pow,mul_one]

theorem marked_moment_zero (ho : HasTreeOrderAtLeast A b p) (P:K[X])
    (h:evalNodes A P∈defectPlus A 0 j) (hd : P.natDegree≤j) {k:ℕ} (hk:k+j+1≤p) :
    scalarMoment P k=0 := by
  obtain ⟨μ,h0,hm⟩:=marked_eval_moments ho P h hd (fun hn=>False.elim (hn rfl))
  exact (hm k hk).trans (h0 rfl)

theorem marked_moment_difference (ho : HasTreeOrderAtLeast A b p) (P:K[X])
    (h:evalNodes A P∈defectPlus A d j) (hd : P.natDegree≤j) (atOne:d≠0→nodes A (Fin.last s)=1)
    {k:ℕ} (hk:k+j+2≤p) : scalarMoment P k-scalarMoment P (k+1)=0 := by
  obtain ⟨μ,_,hm⟩:=marked_eval_moments ho P h hd atOne
  rw [hm k (by omega),hm (k+1) (by omega),sub_self]

end RKCert.Paired.FiniteMidpoint

