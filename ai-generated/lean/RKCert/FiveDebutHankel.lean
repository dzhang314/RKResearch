module
public import RKCert.FourDebutBarycentric
@[expose] public section
namespace RKCert.FiveDebut
open Polynomial RKCert.Paired RKCert.FourDebut
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
noncomputable section

/-- With one (or more) extra powers beyond the exact cardinal budget, the
surviving primitive is a nodal polynomial times a directly bounded factor. -/
theorem double_origin_factor (z : Fin n→K) (inj : Function.Injective z) (nz : ∀ i,z i≠0)
    {P : K[X]} {e : ℕ} (pn : P≠0) (p0 : P.eval 0=0) (degree : P.natDegree≤n+1+e)
    (zeros : ∀ k,(primitive P).eval (z k)=0) :
    ∃ H : K[X], H≠0 ∧ H.natDegree≤e ∧ primitive P=X^2*Lagrange.nodal Finset.univ z*H := by
  classical
  let F:=primitive P
  have f0:F.eval 0=0:=by rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero]
  have der:F.derivative=P:=derivative_integral P
  have fn:F≠0:=fun ze=>pn (by rw [←der,ze,derivative_zero])
  obtain ⟨Q,eqn⟩:=X_dvd_iff.mpr ((coeff_zero_eq_eval_zero _).trans f0)
  have q0:Q.eval 0=0:=by rw [←der,eqn,derivative_mul] at p0;simpa using p0
  obtain ⟨R,eqr⟩:=X_dvd_iff.mpr ((coeff_zero_eq_eval_zero _).trans q0)
  have form:F=X^2*R:=by rw [eqn,eqr];ring
  have rn:R≠0:=fun ze=>fn (by rw [form,ze,mul_zero])
  have rz (k:Fin n):R.eval (z k)=0:=by
    have v:F.eval (z k)=0:=zeros k
    rw [form,eval_mul,eval_pow,eval_X] at v
    exact (mul_eq_zero.mp v).resolve_left (pow_ne_zero _ (nz k))
  have dvd:Lagrange.nodal Finset.univ z ∣ R:=by
    rw [Lagrange.nodal_eq]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ ne
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (inj.ne ne)).isUnit
    · intro k _;exact dvd_iff_isRoot.mpr (rz k)
  obtain ⟨H,eh⟩:=dvd
  have hn:H≠0:=fun ze=>rn (by rw [eh,ze,mul_zero])
  have deg:F.natDegree≤(n+1+e)+1:=primitive_natDegree_le degree
  rw [form,natDegree_mul (pow_ne_zero _ X_ne_zero) rn,natDegree_X_pow,eh,
    natDegree_mul Lagrange.nodal_ne_zero hn,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin] at deg
  exact ⟨H,hn,by omega,by change F=_;rw [form,eh];ring⟩

def denomin (z : Fin n→K) (j : Fin n) : K := ∏ l∈Finset.univ.erase j,(z j-z l)

omit [CharZero K] in
theorem denom_ne_zero {z : Fin n→K} (inj : Function.Injective z) (j : Fin n) : denomin z j≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl;exact sub_ne_zero.mpr (inj.ne (Finset.mem_erase.mp hl).1.symm)

omit [CharZero K] in
theorem nodal_derivative (z : Fin n→K) (j : Fin n) :
    (Lagrange.nodal Finset.univ z).derivative.eval (z j)=denomin z j := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j),Lagrange.eval_nodal];rfl

theorem derivative_on_old (z : Fin n→K) {P G:K[X]}
    (factor : primitive P=X^2*Lagrange.nodal Finset.univ z*G) (i : Fin n) :
    P.eval (z i)=z i^2 * denomin z i * G.eval (z i) := by
  rw [←derivative_integral P,factor,derivative_mul,derivative_mul]
  simp only [eval_add,eval_mul,eval_X,eval_pow,Lagrange.eval_nodal_at_node (Finset.mem_univ i),
    nodal_derivative,zero_mul,mul_zero,zero_add,add_zero]

omit [CharZero K] in
/-- Mathlib's top interpolation coefficient gives all zero low-degree
barycentric moments, without constructing or solving a Vandermonde matrix. -/
theorem low_barycentric {z : Fin (n+1)→K} (inj : Function.Injective z) {Q : K[X]} {g : Fin (n+1)→K}
    (de : Q.natDegree<n) (values : ∀i,Q.eval (z i)=denomin z i*g i) :
    ∑i,g i=0 := by
  have h:=Lagrange.coeff_eq_sum inj.injOn (s:=Finset.univ) (P:=Q)
    (by rw [Finset.card_univ,Fintype.card_fin];exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (show Q.natDegree<n+1 by omega)))
  have ze:Q.coeff n=0:=coeff_eq_zero_of_natDegree_lt de
  simp only [Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel,ze] at h
  change 0=∑ i,Q.eval (z i)/denomin z i at h
  simpa only [values,mul_div_cancel_left₀ _ (denom_ne_zero inj _)] using h.symm

omit [CharZero K] in
theorem barycentric_moment_pair {z : Fin (n+1)→K} (inj : Function.Injective z)
    {Q : K[X]} {g : Fin (n+1)→K} (de : Q.natDegree+2≤n)
    (values : ∀i,Q.eval (z i)=denomin z i*g i) :
    (∑i,g i)=0 ∧ (∑i,z i*g i)=0 := by
  refine ⟨low_barycentric inj (by omega) values,low_barycentric (Q:=X*Q) inj ?_ ?_⟩
  · exact natDegree_mul_le.trans_lt (by rw [natDegree_X];omega)
  · intro i;rw [eval_mul,eval_X,values];ring

def sumPower (z a : Fin n→K) (k : ℕ) : K := ∑i, a i*(z i)^k

omit [CharZero K] in
theorem affine_annihilator {z a : Fin n→K} {G : K[X]} (gn:G≠0) (dg:G.natDegree≤1)
    (s0 : (∑i, a i*G.eval (z i))=0) (s1 : (∑i, z i*(a i*G.eval (z i)))=0) :
    sumPower z a 0*sumPower z a 2=(sumPower z a 1)^2 := by
  have val (x:K) : G.eval x=G.coeff 0+G.coeff 1*x:=by
    rw [eval_eq_sum_range' (n:=2) (by omega),Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero];simp
  have e0 : sumPower z a 0*G.coeff 0+sumPower z a 1*G.coeff 1=0 := by
    convert s0 using 1
    simp only [sumPower,Finset.sum_mul,←Finset.sum_add_distrib,val]
    apply Finset.sum_congr rfl;intro i _;ring
  have e1 : sumPower z a 1*G.coeff 0+sumPower z a 2*G.coeff 1=0 := by
    convert s1 using 1
    simp only [sumPower,Finset.sum_mul,←Finset.sum_add_distrib,val]
    apply Finset.sum_congr rfl;intro i _;ring
  apply sub_eq_zero.mp
  by_cases b:G.coeff 1=0
  · have c:G.coeff 0≠0:=by
      intro both;apply gn;ext k
      rcases k with _|_ |k
      · simpa using both
      · simpa using b
      · exact (coeff_eq_zero_of_natDegree_lt (by omega)).trans (coeff_zero _).symm
    exact (mul_eq_zero.mp (show (sumPower z a 0*sumPower z a 2-sumPower z a 1^2)*G.coeff 0=0 by
      linear_combination (sumPower z a 2)*e0-(sumPower z a 1)*e1)).resolve_right c
  · exact (mul_eq_zero.mp (show (sumPower z a 0*sumPower z a 2-sumPower z a 1^2)*G.coeff 1=0 by
      linear_combination (sumPower z a 0)*e1-(sumPower z a 1)*e0)).resolve_right b

end
end RKCert.FiveDebut
