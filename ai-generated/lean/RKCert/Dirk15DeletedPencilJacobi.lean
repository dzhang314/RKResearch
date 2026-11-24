module

public import RKCert.Dirk15DeletedPencil
public import RKCert.EndpointJacobiTwoBand

@[expose] public section

/-! # The fixed degree-six Jacobi shape or the genuine degree-seven pencil

The terminal-deleted relation is reconstructed from the original paid
spaces. Its polynomial shape is derived over an arbitrary field of
characteristic zero. No free-pencil arithmetic exclusion is asserted.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}
namespace Order15MinimalHead.DeletedPencil
variable {h : Order15MinimalHead A b} (P : h.DeletedPencil)

theorem head_profile :
    ∃ u∈h.U, ∃ R : K[X],R.natDegree≤h.length ∧ ∀ i : Fin 20,i≠Fin.last 19 →
      P.D.eval (nodes A i)=u i+R.eval (nodes A i)*h.w i := by
  obtain ⟨u,hu,R,dR,eqR⟩ := Clock.exists_head_poly P.genuine
  refine ⟨u,hu,R,?_,?_⟩
  · by_cases e : R=0
    · simp [e]
    · have t := (natDegree_lt_iff_degree_lt e).mpr dR
      omega
  · intro i
    refine Fin.lastCases (fun hf => (hf rfl).elim) (fun j _ => ?_) i
    have eq := congrFun P.eq j
    change P.D.eval (nodes A j.castSucc)=P.v j.castSucc at eq
    rw [eq,eqR]

theorem jacobi_shape :
    (deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7 ∧
      ∃ a : K,a≠0 ∧ P.D=C a*(X*jacobiTwo K 6)) ∨
    (deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∉deletedTreeSpace A 7 ∧
      ∃ a t : K,a≠0 ∧ P.D=C a*(X*(jacobiTwo K 7+C t*jacobiTwo K 6))) := by
  have dz : X∣P.D := by
    have e : X-C (0:K)∣P.D := dvd_iff_isRoot.mpr P.origin
    simpa only [map_zero,sub_zero] using e
  obtain ⟨Q,eqQ⟩ := dz
  have Qne : Q≠0 := by
    intro eq0
    have t := P.dmin
    rw [eqQ,eq0,mul_zero,natDegree_zero] at t
    omega
  have qd : P.D.natDegree=1+Q.natDegree := by
    rw [eqQ,natDegree_mul X_ne_zero Qne,natDegree_X]
  have quiet (R : K[X]) (rd : R.natDegree≤5) : jacobiPair Q R=0 := by
    have t := P.quiet R rd
    rwa [eqQ,show X*Q*((1-X)*R)=X*(1-X)*Q*R by ac_rfl] at t
  have gr := P.growth
  by_cases e : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7
  · refine Or.inl ⟨e,?_⟩
    simp only [e,ite_true] at gr
    have q6 : Q.natDegree≤6 := by omega
    have qu := jacobiTwo_top_one (by decide : 0<6) q6 quiet
    refine ⟨Q.coeff 6,fun h => Qne ?_,?_⟩
    · rw [qu,h,map_zero,zero_mul]
    · rw [eqQ]
      calc
        X*Q = X*(C (Q.coeff 6)*jacobiTwo K 6) := congrArg (fun P : K[X] => X*P) qu
        _ = _ := by ac_rfl
  · refine Or.inr ⟨e,?_⟩
    simp only [e,ite_false] at gr
    have q7 : Q.natDegree≤7 := by omega
    obtain ⟨a,b,eq⟩ := jacobiTwo_top_two (by decide : 2≤7) q7 quiet
    have an : a≠0 := by
      intro z
      have t : Q.natDegree≤6 := by
        rw [eq,z,map_zero,zero_mul,zero_add]
        exact (natDegree_C_mul_le _ _).trans (jacobiTwo_degree 6).le
      omega
    refine ⟨a,b/a,an,?_⟩
    rw [eqQ,eq]
    change X*(C a*jacobiTwo K 7+C b*jacobiTwo K 6)=_
    rw [show C a*(X*(jacobiTwo K 7+C (b/a)*jacobiTwo K 6)) =
      X*(C a*jacobiTwo K 7+C (a*(b/a))*jacobiTwo K 6) by rw [map_mul]; ring,
      show a*(b/a)=b by rw [mul_comm,div_mul_cancel₀ _ an]]

end Order15MinimalHead.DeletedPencil
end
end RKCert.Paired
