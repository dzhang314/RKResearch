module
public import RKCert.FiveDebutRows
public import RKCert.FiveDebutFourAtoms
@[expose] public section
namespace RKCert.FiveDebut.FiveData
open RKCert.Paired RKCert.Paired.Clock RKCert.Paired.Pivot RKCert.OneEscape RKCert.FourDebut Polynomial
variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Fin s→Fin s→K}
variable {U : Submodule K (Vec K s)} {w : Vec K s}
open scoped Classical
noncomputable section
variable (h : FiveData A U w)

/-- Actual amplitudes at the first four nonzero outside debuts, with their
common scale. Two paired cuts suffice; no extra fourth-frontier cut. -/
theorem actual_scale (ha : LowerArray A) (inv : U.map (diag (nodes A))≤U)
    (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (band : ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) U w (1+k)) :
    ∃ scale : K, scale≠0 ∧ ∀ i,w (h.i4 i)=scale*(h.z4 i)^2*(Lagrange.nodal Finset.univ h.z4).derivative.eval (h.z4 i) := by
  have t3:=h.third_singular ha inv alg inc (band 0 (by decide)).ge (band 1 (by decide)).le
  obtain ⟨nn,z1,z2⟩:=h.fifth_kernel ha inv alg (inc.trans (zeroSpace_mono A (by decide : 5≤6)))
    (band 1 (by decide)).ge (band 2 (by decide)).le
  let a:=fun i=>h.z3 i^2/h.W3 i
  let B:=fun i=>h.z4 i^2/h.W4 i
  let A4:=nodes A h.u^2/w h.u
  let c:=nodes A h.u
  let v:=nodes A h.v
  have step (l:ℕ):sumPower h.z4 B l=sumPower h.z3 a l+A4*c^l := by
    unfold sumPower
    rw [Fin.sum_univ_castSucc]
    simp only [a,B,A4,c,z4,W4,i4,z3,W3,Fin.snoc_castSucc,Fin.snoc_last]
  have nz: A4≠0 := div_ne_zero (pow_ne_zero _ h.d4.nz) (by simpa only [i4,W4,Fin.snoc_last] using nn (Fin.last 3))
  have fresh:c≠v:=fun e=>h.d5.fresh (by rw [show nodes A h.v=nodes A h.u from e.symm];exact Finset.mem_insert_self ..)
  change sumPower h.z3 a 0*sumPower h.z3 a 2=(sumPower h.z3 a 1)^2 at t3
  change sumPower h.z4 B 1=v*sumPower h.z4 B 0 at z1
  change sumPower h.z4 B 2=v*sumPower h.z4 B 1 at z2
  simp only [step,pow_zero,mul_one,pow_one] at z1 z2
  obtain ⟨e0,e1,e2⟩:=fourth_atom_zero t3 nz fresh z1 z2
  apply four_atoms_normalized h.inj4 h.nz4 nn
  intro k
  change sumPower h.z4 B k.val=0
  rw [step];fin_cases k <;> first | simpa using e0 | simpa using e1 | simpa using e2

/-- The three actual primitive observations needed by the remaining purely
four-knot scalar theorem. No refund is assumed on the fourth row. -/
theorem actual_observations (ha : LowerArray A) (inv : U.map (diag (nodes A))≤U)
    (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (f₆ : zeroSpace A 6≤chain (diag (nodes A)) U w 2)
    (f₇ : zeroSpace A 7≤chain (diag (nodes A)) U w 3) :
    let T := Lagrange.nodal Finset.univ h.z3
    let V := Lagrange.nodal Finset.univ h.z4
    (∃ Q:K[X],Q.degree<(2:WithBot ℕ) ∧ ∀i,(primitive (X*T)).eval (h.z3 i)=h.W3 i*Q.eval (h.z3 i)) ∧
    (∃ Q:K[X],Q.degree<(2:WithBot ℕ) ∧ ∀i,(primitive (X*V)).eval (h.z5 i)=h.W5 i*Q.eval (h.z5 i)) ∧
    (∃ Q:K[X],Q.degree<(3:WithBot ℕ) ∧ ∀i,(primitive (X^2*V)).eval (h.z5 i)=h.W5 i*Q.eval (h.z5 i)) := by
  let T:=Lagrange.nodal Finset.univ h.z3
  let V:=Lagrange.nodal Finset.univ h.z4
  have dt:T.natDegree=3:=by simp [T]
  have dv:V.natDegree=4:=by simp [V]
  have ts (a:K) (mem:a∈Finset.univ.image h.z3) : T.eval a=0:=by
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp mem
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ k)
  have vs (a:K) (mem:a∈insert (nodes A h.u) (Finset.univ.image h.z3)) : V.eval a=0:=by
    rw [←h.roots4] at mem
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp mem
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ k)
  obtain ⟨x,xu,pre,_⟩:=masked_at_debut inv alg h.d4 (P:=X*T) (by simp) (fun a mem=>by simp [ts a mem])
  have tr:OrdinaryTrace A 5 x (X*T):=⟨natDegree_mul_le.trans (by rw [natDegree_X,dt];decide),inc xu⟩
  obtain ⟨R,dr,_,g⟩:=response_at_paid ha f₆ tr pre
  have also (i:Fin 5):h.i5 i≤h.v:= (h.pay5 i).elim le_of_lt (fun a=>a.1.le)
  have lx:(X*V).natDegree≤5:=natDegree_mul_le.trans (by rw [natDegree_X,dv])
  have lxx:(X^2*V).natDegree≤6:=natDegree_mul_le.trans (by rw [natDegree_X_pow,dv])
  obtain ⟨B,db,bv⟩:=masked_primitive h.d5 ha inv alg inc f₆ h.diag5 lx (by simp) (fun a mem=>by simp [vs a mem])
  obtain ⟨D,dd,dbv⟩:=masked_primitive h.d5 ha inv alg (inc.trans (zeroSpace_mono A (by decide : 5≤6))) f₇ h.diag5 lxx (by simp) (fun a mem=>by simp [vs a mem])
  exact ⟨⟨R,dr,fun i=>g _ (Or.inl (h.before i)) (h.outside i)⟩,
    ⟨B,db,fun i=>bv _ (also i) (h.out5 i)⟩,⟨D,dd,fun i=>dbv _ (also i) (h.out5 i)⟩⟩

end
end RKCert.FiveDebut.FiveData
