module
public import RKCert.Dirk17ThreePortTable
public import RKCert.DirkTrace
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
@[expose] public section
namespace RKCert.RadauEight.EarlyPort
open Polynomial RKCert.Paired RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K:Type*} [Field K] [CharZero K]

private theorem expand_moment (P:K[X]) (dP:P.natDegree≤5) (u:K) (k:ℕ) (hk:k≤3) :
    (∑j:Fin 6,P.coeff j.val*moment j k u)=(2520:K)*(Paired.primitive (X^k*P)).eval u:=by
  rw [←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul _ _ _ dP,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  have divi:((2520/(j.val+k+1):ℕ):K)=(2520:K)/((j.val+k+1:ℕ):K):=by
    fin_cases j <;> interval_cases k <;> norm_num
  rw [moment,divi];ring

private theorem observed_rows (P:K[X]) (dP:P.natDegree≤5) (u v z:K)
    (g₁:(Paired.primitive (X*((X-C u)*P))).eval v=0)
    (g₂:(Paired.primitive (X^2*((X-C u)*P))).eval v=0)
    (h₁:(Paired.primitive (X*((X-C u)*((X-C v)*P)))).eval z=0) :
    ∀i:Fin 3,(∑j:Fin 6,P.coeff j.val*remaining u v z i j)=0:=by
  have e1:X*((X-C u)*P)=X^2*P-u • (X*P):=by rw [smul_eq_C_mul];ring
  have e2:X^2*((X-C u)*P)=X^3*P-u • (X^2*P):=by rw [smul_eq_C_mul];ring
  have e3:X*((X-C u)*((X-C v)*P))=X^3*P-(u+v) • (X^2*P)+(u*v) • (X*P):=by
    simp only [smul_eq_C_mul,map_add,map_mul];ring
  have sm (a:K) (Q:K[X]) (x:K):(Paired.primitive (a • Q)).eval x=a*(Paired.primitive Q).eval x:=by
    rw [map_smul,smul_eq_C_mul,eval_mul,eval_C]
  have a1:(Paired.primitive (X^2*P)).eval v-u*(Paired.primitive (X*P)).eval v=0:=by
    rwa [e1,map_sub,eval_sub,sm] at g₁
  have a2:(Paired.primitive (X^3*P)).eval v-u*(Paired.primitive (X^2*P)).eval v=0:=by
    rwa [e2,map_sub,eval_sub,sm] at g₂
  have a3:(Paired.primitive (X^3*P)).eval z-(u+v)*(Paired.primitive (X^2*P)).eval z
      +u*v*(Paired.primitive (X*P)).eval z=0:=by
    rwa [e3,map_add,map_sub,eval_add,eval_sub,sm,sm] at h₁
  intro i
  fin_cases i
  · change (∑j:Fin 6,P.coeff j.val*(moment j 2 v-u*moment j 1 v))=0
    simp_rw [mul_sub,show ∀j:Fin 6,P.coeff j.val*(u*moment j 1 v)=u*(P.coeff j.val*moment j 1 v) by intro j;ring]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,expand_moment P dP v 2 (by decide),expand_moment P dP v 1 (by decide)]
    simp only [pow_one]
    linear_combination (2520:K)*a1
  · change (∑j:Fin 6,P.coeff j.val*(moment j 3 v-u*moment j 2 v))=0
    simp_rw [mul_sub,show ∀j:Fin 6,P.coeff j.val*(u*moment j 2 v)=u*(P.coeff j.val*moment j 2 v) by intro j;ring]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,expand_moment P dP v 3 (by decide),expand_moment P dP v 2 (by decide)]
    linear_combination (2520:K)*a2
  · change (∑j:Fin 6,P.coeff j.val*(moment j 3 z-(u+v)*moment j 2 z+u*v*moment j 1 z))=0
    simp_rw [mul_add,mul_sub,
      show ∀j:Fin 6,P.coeff j.val*((u+v)*moment j 2 z)=(u+v)*(P.coeff j.val*moment j 2 z) by intro j;ring,
      show ∀j:Fin 6,P.coeff j.val*(u*v*moment j 1 z)=(u*v)*(P.coeff j.val*moment j 1 z) by intro j;ring]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
       expand_moment P dP z 3 (by decide),expand_moment P dP z 2 (by decide),expand_moment P dP z 1 (by decide)]
    simp only [pow_one]
    linear_combination (2520:K)*a3

omit [CharZero K] in
private theorem moment_scale (j:Fin 6) (k:ℕ) (c z:K) :
    moment j k (c*z)=c^(j.val+k+1)*moment j k z:=by rw [moment,mul_pow,moment];ring

omit [CharZero K] in
private theorem remaining_scale (u v z c:K) (i:Fin 3) (j:Fin 6) :
    remaining (c*u) (c*v) (c*z) i j=c^(j.val+rowDegree i)*remaining u v z i j:=by
  fin_cases i
  · change moment j 2 (c*v)-(c*u)*moment j 1 (c*v)=c^(j.val+3)*(moment j 2 v-u*moment j 1 v)
    rw [moment_scale,moment_scale,show j.val+2+1=j.val+3 by omega,
      show j.val+1+1=j.val+2 by omega,pow_succ c (j.val+2)]
    ring
  · change moment j 3 (c*v)-(c*u)*moment j 2 (c*v)=c^(j.val+4)*(moment j 3 v-u*moment j 2 v)
    rw [moment_scale,moment_scale,show j.val+3+1=j.val+4 by omega,
      show j.val+2+1=j.val+3 by omega,pow_succ c (j.val+3)]
    ring
  · change moment j 3 (c*z)-(c*u+c*v)*moment j 2 (c*z)+(c*u*(c*v))*moment j 1 (c*z)=
      c^(j.val+4)*(moment j 3 z-(u+v)*moment j 2 z+u*v*moment j 1 z)
    rw [moment_scale,moment_scale,moment_scale,show j.val+3+1=j.val+4 by omega,
      show j.val+2+1=j.val+3 by omega,show j.val+1+1=j.val+2 by omega,
      show j.val+4=(j.val+2)+2 by omega,show j.val+3=(j.val+2)+1 by omega,pow_add,pow_succ c (j.val+2)]
    ring

private theorem first_observation (P:K[X]) (dP:P.natDegree≤5) (u:K) (un:u≠0) (k:ℕ)
    (zero:(Paired.primitive (X^k*P)).eval u=0) :
    (∑j:Fin 6,P.coeff j.val*u^j.val/((k+j.val+1:ℕ):K))=0:=by
  have e:(Paired.primitive (X^k*P)).eval u=
      u^(k+1)*(∑j:Fin 6,P.coeff j.val*u^j.val/((k+j.val+1:ℕ):K)):=by
    rw [←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul _ _ _ dP,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro j _
    rw [show k+j.val+1=k+1+j.val by omega,pow_add]
    simp only [div_eq_mul_inv]
    ring
  rw [zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ un)

def colIndex (i:Fin 3):Fin 6:=⟨colDegree i,by have:=i.isLt;unfold colDegree;omega⟩

private theorem basis_recovery (a:Fin 6→K) (u:K) (un:u≠0)
    (e1:(∑j:Fin 6,a j*u^j.val/((j.val+2:ℕ):K))=0)
    (e2:(∑j:Fin 6,a j*u^j.val/((j.val+3:ℕ):K))=0)
    (e3:(∑j:Fin 6,a j*u^j.val/((j.val+4:ℕ):K))=0) :
    ∀j:Fin 6,a j=∑i:Fin 3,((coeff i j:ℤ):K)*u^(colDegree i-j.val)*(a (colIndex i)/(basisLead i:K)):=by
  norm_num [Fin.sum_univ_succ] at e1 e2 e3
  intro j
  have d:=pow_ne_zero j.val un
  apply mul_right_cancel₀ d
  fin_cases j <;> norm_num [Fin.sum_univ_succ,coeff,colDegree,colIndex,basisLead]
  · linear_combination 72*e1-240*e2+180*e3
  · apply Or.inl
    apply mul_right_cancel₀ un
    linear_combination -240*e1+900*e2-720*e3
  · apply Or.inl
    apply mul_right_cancel₀ (pow_ne_zero 2 un)
    linear_combination 180*e1-720*e2+600*e3
  · exact Or.inl (by ring)
  · exact Or.inl (by ring)
  · exact Or.inl (by ring)

theorem quintic_three_two_one (P:K[X]) (dP:P.natDegree≤5) (u v z:K)
    (un:u≠0) (vn:v≠0) (zn:z≠0) (vu:v≠u) (zu:z≠u) (zv:z≠v)
    (ur:(grid K).eval u=0) (vr:(grid K).eval v=0) (zr:(grid K).eval z=0)
    (f₁:(Paired.primitive (X*P)).eval u=0)
    (f₂:(Paired.primitive (X^2*P)).eval u=0)
    (f₃:(Paired.primitive (X^3*P)).eval u=0)
    (g₁:(Paired.primitive (X*((X-C u)*P))).eval v=0)
    (g₂:(Paired.primitive (X^2*((X-C u)*P))).eval v=0)
    (h₁:(Paired.primitive (X*((X-C u)*((X-C v)*P)))).eval z=0) : P=0:=by
  let L:K:=24310
  have Ln:L≠0:=by norm_num [L]
  let a (j:Fin 6):K:=P.coeff j.val/L^j.val
  let x (i:Fin 3):K:=a (colIndex i)/(basisLead i:K)
  have e (j:Fin 6):a j*(L*u)^j.val=P.coeff j.val*u^j.val:=by
    change (P.coeff j.val/L^j.val)*(L*u)^j.val=_
    rw [mul_pow,←mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ Ln)]
  have mix (j:Fin 6):a j=∑i:Fin 3,((coeff i j:ℤ):K)*(L*u)^(colDegree i-j.val)*x i:=by
    apply basis_recovery a (L*u) (mul_ne_zero Ln un) _ _ _ j
    · simp_rw [e]
      simpa only [pow_one,Nat.add_comm 1,Nat.add_assoc] using first_observation P dP u un 1 (by simpa only [pow_one] using f₁)
    · simp_rw [e]
      simpa only [Nat.add_comm 2,Nat.add_assoc] using first_observation P dP u un 2 f₂
    · simp_rw [e]
      simpa only [Nat.add_comm 3,Nat.add_assoc] using first_observation P dP u un 3 f₃
  have scaledRows (i:Fin 3):(∑j:Fin 6,a j*remaining (L*u) (L*v) (L*z) i j)=0:=by
    rw [←mul_zero (L^rowDegree i),←observed_rows P dP u v z g₁ g₂ h₁ i,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro j _
    simp only [a,remaining_scale,pow_add]
    calc
       _ = ((P.coeff j.val/L^j.val)*L^j.val)*(L^rowDegree i *remaining u v z i j) := by ring
       _ = _ := by rw [div_mul_cancel₀ _ (pow_ne_zero _ Ln)];ring
  let M:Matrix (Fin 3) (Fin 3) K:=portMatrix (L*u) (L*v) (L*z)
  have detNe:M.det≠0:=by
    have t:=test_at_scaled_roots u v z un vn zn vu zu zv ur vr zr
    change det3 M≠0 at t
    have eq:M.det=det3 M:=by rw [Matrix.det_fin_three,det3];ring
    rwa [eq]
  have kern:Matrix.mulVec M x=0:=by
    ext i
    change (∑k:Fin 3,portMatrix (L*u) (L*v) (L*z) i k*x k)=0
    have zz:=scaledRows i
    simp_rw [mix,Finset.sum_mul] at zz
    rw [Finset.sum_comm] at zz
    rw [show (∑k:Fin 3,portMatrix (L*u) (L*v) (L*z) i k*x k)=
        ∑ k:Fin 3,∑j:Fin 6,(((coeff k j:ℤ):K)*(L*u)^(colDegree k-j.val)*x k)*remaining (L*u) (L*v) (L*z) i j by
      apply Finset.sum_congr rfl;intro k _
      rw [portMatrix,Finset.sum_mul]
      apply Finset.sum_congr rfl;intro j _;ring]
    exact zz
  have zx:x=0:=Matrix.eq_zero_of_mulVec_eq_zero detNe kern
  ext j
  rw [coeff_zero]
  by_cases hh:j<6
  · have ze:=mix ⟨j,hh⟩
    simp [zx] at ze
    exact (div_eq_zero_iff.mp ze).resolve_right (pow_ne_zero _ Ln)
  · exact coeff_eq_zero_of_natDegree_lt (by omega)
end
end RKCert.RadauEight.EarlyPort
