module
public import RKCert.FourDebutCut
public import RKCert.FourDebutScalar
@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired Polynomial Module
variable {K : Type*} [Field K] [CharZero K]

theorem derivative_integral (P : Polynomial K) : (primitive P).derivative=P := by
  ext n
  rw [Polynomial.coeff_derivative,primitive_coeff_succ]
  push_cast
  have h : (n:K)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
  exact div_mul_cancel₀ _ h

/-- The recovered primitive is a scalar multiple of the forced monic
double-origin nodal polynomial; Lagrange's native nodal polynomial supplies
the distinct-root calculus. -/
theorem double_origin_shape {n : ℕ} (z : Fin n→K) (inj : Function.Injective z)
    (nz : ∀j,z j≠0) {P : Polynomial K} (Pn : P≠0) (P0 : P.eval 0=0)
    (hd : P.natDegree≤n+1) (val : ∀j,(primitive P).eval (z j)=0) :
    ∃ lam : K, lam≠0 ∧ primitive P = X^2*Lagrange.nodal Finset.univ z*C lam := by
  classical
  let F := primitive P
  have F0 : F.eval 0=0 := by rw [←Polynomial.coeff_zero_eq_eval_zero,primitive_coeff_zero]
  have Fp : F.derivative=P := derivative_integral P
  have hn : F≠0 := fun hf => Pn (by rw [←Fp,hf,Polynomial.derivative_zero])
  have hX : X∣F := Polynomial.X_dvd_iff.mpr ((Polynomial.coeff_zero_eq_eval_zero _).trans F0)
  obtain ⟨Q,eqQ⟩ := hX
  have Q0 : Q.eval 0=0 := by
    rw [←Fp,eqQ,Polynomial.derivative_mul] at P0
    simpa using P0
  obtain ⟨R,eqR⟩ := Polynomial.X_dvd_iff.mpr ((Polynomial.coeff_zero_eq_eval_zero _).trans Q0)
  have form : F=X^2*R := by rw [eqQ,eqR]; ring
  have Rn : R≠0 := fun hr => hn (by rw [form,hr,mul_zero])
  have flow (j : Fin n) : R.eval (z j)=0 := by
    have e : F.eval (z j)=0 := val j
    rw [form,eval_mul,eval_pow,eval_X] at e
    exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ (nz j))
  have divi : Lagrange.nodal Finset.univ z ∣ R := by
    rw [Lagrange.nodal_eq]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ he
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (inj.ne he)).isUnit
    · intro j _
      exact dvd_iff_isRoot.mpr (flow j)
  obtain ⟨D,eqD⟩ := divi
  have Dn : D≠0 := fun h => Rn (by rw [eqD,h,mul_zero])
  have deg : F.natDegree≤n+2 := primitive_natDegree_le hd
  rw [form,natDegree_mul (pow_ne_zero _ X_ne_zero) Rn,natDegree_X_pow,eqD,
    natDegree_mul Lagrange.nodal_ne_zero Dn,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin] at deg
  have dc := Polynomial.eq_C_of_natDegree_eq_zero (show D.natDegree=0 by omega)
  refine ⟨D.coeff 0,fun e=>Dn (by rw [dc,e]; simp),?_⟩
  change F=_
  rw [form,eqD,←dc]; ring

/-- Differentiating the recovered primitive at each actual sampled abscissa
gives the barycentric numerator with the *same* nonzero common scale. -/
theorem sampled_derivative {n : ℕ} (z : Fin n→K) (inj : Function.Injective z)
    (nz : ∀j,z j≠0) {P : Polynomial K} (Pn : P≠0) (P0 : P.eval 0=0)
    (hd : P.natDegree≤n+1) (val : ∀j,(primitive P).eval (z j)=0) :
    ∃ r : K, r≠0 ∧ ∀ j, P.eval (z j) =
      r*(z j)^2*(∏ t∈Finset.univ.erase j,(z j-z t)) := by
  classical
  obtain ⟨r,rn,h⟩ := double_origin_shape z inj nz Pn P0 hd val
  refine ⟨r,rn,fun j=>?_⟩
  rw [←derivative_integral P,h,derivative_mul,derivative_mul]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.derivative_C,Polynomial.eval_C,
    Lagrange.eval_nodal_at_node (Finset.mem_univ j),mul_zero,zero_add,add_zero,
    Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j),Lagrange.eval_nodal]
  ring

/-- Conversion of the genuine paired kernel to the consecutive barycentric
debut cut, using Mathlib's Lagrange top-coefficient theorem. -/
theorem barycentric_sum {k : ℕ} (z w : Fin (k+1)→K) (u : K)
    (inj : Function.Injective z) (fresh : ∀j,u≠z j) (nu : u≠0) (nz : ∀j,z j≠0) (nw : ∀j,w j≠0)
    {P Q : Polynomial K} (Pn : P≠0) (dp : P.natDegree≤k+3) (P0 : P.eval 0=0)
    (dq : Q.degree < (k:WithBot ℕ)) (matchq : ∀j,P.eval (z j)=w j*Q.eval (z j))
    (nv : (primitive P).eval u=0) (vals : ∀j,(primitive P).eval (z j)=0) :
    (∑ j, (z j^2/w j)*(z j-u))=0 := by
  classical
  let zz : Fin ((k+1)+1)→K := Fin.cons u z
  have injall : Function.Injective zz := by
    intro i
    refine Fin.cases ?_ (fun a=>?_) i
    · intro j
      exact Fin.cases (fun _=>rfl) (fun t h=>False.elim (fresh t h)) j
    · intro j
      exact Fin.cases (fun h=>False.elim (fresh a h.symm)) (fun t h=>congrArg Fin.succ (inj h)) j
  obtain ⟨r,rn,F⟩ := double_origin_shape zz injall (Fin.cases nu nz) Pn P0 dp (Fin.cases nv vals)
  let H := Lagrange.nodal Finset.univ z
  have fac : Lagrange.nodal Finset.univ zz = (X-C u)*H := by
    rw [Lagrange.nodal_eq,Fin.prod_univ_succ]
    simp only [zz,Fin.cons_zero,Fin.cons_succ,H,Lagrange.nodal_eq]
  rw [fac] at F
  let D (j : Fin (k+1)) := ∏ l∈Finset.univ.erase j, (z j-z l)
  have Dn (j) : D j≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    exact sub_ne_zero.mpr (inj.ne (Finset.mem_erase.mp hl).1.symm)
  have der (j) : H.derivative.eval (z j)=D j := by
    rw [show H=Lagrange.nodal Finset.univ z from rfl,
      Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j),Lagrange.eval_nodal]
  have pp (j) : P.eval (z j) = r*(z j)^2*(z j-u)*D j := by
    rw [←derivative_integral P,F,derivative_mul,derivative_mul,derivative_mul]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.derivative_C,Polynomial.eval_C,eval_sub,der j,
      show H.eval (z j)=0 from Lagrange.eval_nodal_at_node (Finset.mem_univ _),mul_zero,zero_add,add_zero]
    ring
  have qr (j) : Q.eval (z j)/D j = r*((z j^2/w j)*(z j-u)) := by
    apply (div_eq_iff (Dn j)).mpr
    apply mul_left_cancel₀ (nw j)
    rw [←matchq,pp]
    field_simp [nw j]
  have hcoeff := Lagrange.coeff_eq_sum inj.injOn
    (s:=Finset.univ) (P:=Q) (by simp; exact dq.trans (by exact_mod_cast Nat.lt_succ_self k))
  have q0 : Q.coeff k=0 := Polynomial.coeff_eq_zero_of_degree_lt dq
  simp only [Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel,q0] at hcoeff
  change 0 = ∑ j, Q.eval (z j)/D j at hcoeff
  simp_rw [qr] at hcoeff
  rw [←Finset.mul_sum] at hcoeff
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left rn

end RKCert.FourDebut
