module

public import RKCert.ReviewedNative.DIRKC2PairedCut
public import RKCert.FourDebutScalar

@[expose] public section

/-! # Actual reviewed primitives supply the frozen scalar four-debut port
The imported scalar contradiction is Mathlib-only and unchanged. This
module reads its numerical-field inputs from the native primitive and
the complete physical-prefix cut. -/
namespace RKResearch.Certified.Graded.OuterHead

open Polynomial Module RKCert.FourDebut
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]

private theorem derivative_native (P : K[X]) : (primitive P).derivative=P := by
  ext n
  rw [coeff_derivative,primitive_coeff_succ]
  have nz : (((n+1:ℕ):K))≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ (P.coeff n) nz

private theorem double_origin_nodal {n : ℕ} (z : Fin n → K) (inj : Function.Injective z)
    (nz : ∀ i,z i≠0) {P : K[X]} (pn : P≠0) (p0 : P.eval 0=0)
    (dp : P.natDegree≤n+1) (roots : ∀ i,(primitive P).eval (z i)=0) :
    ∃ a : K, a≠0 ∧ primitive P=X^2*Lagrange.nodal Finset.univ z*C a := by
  let F := primitive P
  have df : F.derivative=P := derivative_native _
  have nf : F≠0 := fun h => pn (by rw [←df,h,derivative_zero])
  obtain ⟨Q,hQ⟩ := X_dvd_iff.mpr (primitive_coeff_zero P)
  have q0 : Q.coeff 0=0 := by
    have h : (primitive P).coeff 1=0 := by
      rw [show (1:ℕ)=0+1 from rfl,primitive_coeff_succ,coeff_zero_eq_eval_zero,p0,zero_div]
    rw [hQ,show (1:ℕ)=0+1 from rfl,coeff_X_mul] at h
    exact h
  obtain ⟨T,hT⟩ := X_dvd_iff.mpr q0
  have ft : F=(X:K[X])^2*T := by change primitive P=_; rw [hQ,hT,pow_two,mul_assoc]
  have tn : T≠0 := fun z => nf (by rw [ft,z,mul_zero])
  have tr (i : Fin n) : T.eval (z i)=0 := by
    have h : F.eval (z i)=0 := roots i
    rw [ft,eval_mul,eval_pow,eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (nz i))
  have dvd : Lagrange.nodal Finset.univ z ∣ T := by
    rw [Lagrange.nodal_eq]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ ne
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (inj.ne ne)).isUnit
    · intro j _
      exact dvd_iff_isRoot.mpr (tr j)
  obtain ⟨R,eq⟩ := dvd
  have Rn : R≠0 := fun q => tn (by rw [eq,q,mul_zero])
  have dF : F.natDegree≤n+2 := primitive_natDegree_le dp
  rw [ft,natDegree_mul (pow_ne_zero _ X_ne_zero) tn,natDegree_X_pow,eq,
    natDegree_mul Lagrange.nodal_ne_zero Rn,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin] at dF
  have er := eq_C_of_natDegree_eq_zero (show R.natDegree=0 by omega)
  refine ⟨R.coeff 0,fun q => Rn (by rw [er,q,C_0]),?_⟩
  change F=_
  rw [ft,eq,←er,mul_assoc]

/-- Barycentric edge from one actual paid scalar-plus-head cut. -/
theorem barycentric_native {k : ℕ} (z w : Fin (k+1) → K) (u : K)
    (inj : Function.Injective z) (fresh : ∀ i,u≠z i)
    (nu : u≠0) (nz : ∀ i,z i≠0) (nw : ∀ i,w i≠0)
    {P Q : K[X]} (pn : P≠0) (dp : P.natDegree≤k+3) (p0 : P.eval 0=0)
    (dq : Q.degree < (k : WithBot ℕ)) (fit : ∀ i,P.eval (z i)=w i*Q.eval (z i))
    (un : (primitive P).eval u=0) (roots : ∀ i,(primitive P).eval (z i)=0) :
    (∑ i, (z i^2/w i)*(z i-u))=0 := by
  let Z : Fin ((k+1)+1) → K := Fin.cons u z
  have iZ : Function.Injective Z := by
    intro i
    refine Fin.cases ?_ (fun a=>?_) i
    · intro j
      exact Fin.cases (fun _ => rfl) (fun b e => (fresh b e).elim) j
    · intro j
      exact Fin.cases (fun e => (fresh a e.symm).elim) (fun b e => congrArg Fin.succ (inj e)) j
  obtain ⟨r,rn,e⟩ := double_origin_nodal Z iZ (Fin.cases nu nz) pn p0 dp (Fin.cases un roots)
  let H := Lagrange.nodal Finset.univ z
  have ff : Lagrange.nodal Finset.univ Z=(X-C u)*H := by
    rw [Lagrange.nodal_eq,Fin.prod_univ_succ]
    simp only [Z,Fin.cons_zero,Fin.cons_succ,H,Lagrange.nodal_eq]
  rw [ff] at e
  let D (i : Fin (k+1)) := ∏ j∈Finset.univ.erase i,(z i-z j)
  have Dn (i : Fin (k+1)) : D i≠0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (inj.ne (Finset.ne_of_mem_erase hj).symm)
  have df (i : Fin (k+1)) : H.derivative.eval (z i)=D i := by
    rw [show H=Lagrange.nodal Finset.univ z from rfl,
      Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i),Lagrange.eval_nodal]
  have pp (i : Fin (k+1)) : P.eval (z i)=r*z i^2*(z i-u)*D i := by
    rw [←derivative_native P,e,derivative_mul,derivative_mul,derivative_mul]
    simp only [eval_add,eval_mul,eval_pow,eval_X,derivative_C,eval_C,eval_sub,df i,
      show H.eval (z i)=0 from Lagrange.eval_nodal_at_node (Finset.mem_univ _),mul_zero,zero_add,add_zero]
    ring
  have form (i : Fin (k+1)) : Q.eval (z i)/D i=r*((z i^2/w i)*(z i-u)) := by
    apply (div_eq_iff (Dn i)).mpr
    apply mul_left_cancel₀ (nw i)
    rw [←fit,pp]
    field_simp [nw i]
  have top := Lagrange.coeff_eq_sum inj.injOn (s:=Finset.univ) (P:=Q)
    (by simp; exact dq.trans (by exact_mod_cast Nat.lt_succ_self k))
  have q0 : Q.coeff k=0 := coeff_eq_zero_of_degree_lt dq
  simp only [Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel,q0] at top
  change 0=∑ i,Q.eval (z i)/D i at top
  simp_rw [form] at top
  rw [←Finset.mul_sum] at top
  exact (mul_eq_zero.mp top.symm).resolve_left rn

omit [CharZero K] in
private theorem Jterm (a : K) (n : ℕ) :
    primitive (C a*X^n)=C (a/((n+1:ℕ):K))*X^(n+1) := by
  rw [C_mul_X_pow_eq_monomial,primitive_monomial,C_mul_X_pow_eq_monomial]

noncomputable abbrev nodes2 (a b : K) : K[X] := (X-C a)*(X-C b)
noncomputable abbrev nodes3 (a b u : K) : K[X] := (X-C a)*(X-C b)*(X-C u)

theorem J_nodes2 (a b x : K) :
    (primitive (X*nodes2 a b)).eval x=x^2*L2 a b x := by
  have e : X*nodes2 a b=C 1*X^3-C (a+b)*X^2+C (a*b)*X^1 := by
    simp only [nodes2,map_one,map_add,map_mul]; ring
  rw [e,map_add,map_sub,Jterm,Jterm,Jterm]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,L2]
  norm_num; ring

theorem J_nodes3 (a b u x : K) :
    (primitive (X*nodes3 a b u)).eval x=B1 a b u x := by
  have e : X*nodes3 a b u=C 1*X^4-C (a+b+u)*X^3+C (a*b+u*(a+b))*X^2-C (a*b*u)*X^1 := by
    simp only [nodes3,map_one,map_add,map_mul]; ring
  rw [e,map_sub,map_add,map_sub,Jterm,Jterm,Jterm,Jterm]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,B1]
  norm_num; ring

theorem J2_nodes3 (a b u x : K) :
    (primitive (X^2*nodes3 a b u)).eval x=B2 a b u x := by
  have e : X^2*nodes3 a b u=C 1*X^5-C (a+b+u)*X^4+C (a*b+u*(a+b))*X^3-C (a*b*u)*X^2 := by
    simp only [nodes3,map_one,map_add,map_mul]; ring
  rw [e,map_sub,map_add,map_sub,Jterm,Jterm,Jterm,Jterm]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,B2]
  norm_num; ring

omit [CharZero K] in
theorem eval_const_head {P : K[X]} (d : P.degree < (1:WithBot ℕ)) (x : K) :
    P.eval x=P.coeff 0 := by
  by_cases z : P=0
  · simp [z]
  have t : P.natDegree<1 := (natDegree_lt_iff_degree_lt z).mpr d
  exact (congrArg (fun Q : K[X] => Q.eval x) (eq_C_of_natDegree_eq_zero (by omega : P.natDegree=0))).trans (eval_C ..)

omit [CharZero K] in
theorem eval_linear_head {P : K[X]} (d : P.degree < (2:WithBot ℕ)) (x : K) :
    P.eval x=P.coeff 1*x+P.coeff 0 := by
  by_cases z : P=0
  · simp [z]
  rw [eval_eq_sum_range' ((natDegree_lt_iff_degree_lt z).mpr d)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one]
  ring

omit [CharZero K] in
theorem eval_quadratic_head {P : K[X]} (d : P.degree < (3:WithBot ℕ)) (x : K) :
    P.eval x=P.coeff 2*x^2+P.coeff 1*x+P.coeff 0 := by
  by_cases z : P=0
  · simp [z]
  rw [eval_eq_sum_range' ((natDegree_lt_iff_degree_lt z).mpr d)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one]
  ring

end RKResearch.Certified.Graded.OuterHead
