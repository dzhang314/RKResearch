module
public import RKCert.DirkQuinticTools
public import RKCert.DirkLobattoQuadrature
public import RKCert.FourDebutMoments
@[expose] public section
namespace RKCert.DirkQuintic
open Polynomial RKCert.Paired RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K]
noncomputable section

def cubic (a b c:K):K[X]:=(X-C a)*(X-C b)*(X-C c)

omit [CharZero K] in
theorem cubic_form (a b c:K) : cubic a b c=X^3-C (a+b+c)*X^2+C (a*b+a*c+b*c)*X-C (a*b*c) := by
  simp [cubic];ring

omit [CharZero K] in
theorem cubic_degree (a b c:K) :(cubic a b c).natDegree=3 :=by
  dsimp [cubic]
  rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _),
    natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),natDegree_X_sub_C,natDegree_X_sub_C,natDegree_X_sub_C]

set_option maxHeartbeats 2000000 in
theorem local_moment (j:Fin 5) (a b c u:K) :
    2520*(Paired.primitive (X^(j.val+1)*cubic a b c)).eval u =
    u^(j.val+2)*momentForm (j.val+1) a b c u := by
  rw [←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul _ u _ (cubic_degree a b c).le]
  have h0:(cubic a b c).coeff 0= -(a*b*c) :=by rw [cubic_form];simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X];norm_num
  have h1:(cubic a b c).coeff 1=a*b+a*c+b*c :=by rw [cubic_form];simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X];norm_num
  have h2:(cubic a b c).coeff 2= -(a+b+c) :=by rw [cubic_form];simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X];norm_num
  have h3:(cubic a b c).coeff 3=1 :=by rw [cubic_form];simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X];norm_num
  fin_cases j <;> norm_num [Fin.sum_univ_succ,h0,h1,h2,h3,momentForm] <;> ring

omit [CharZero K] in
theorem divides_cubic {Q:K[X]} {a b c:K} (ab:a≠b) (ac:a≠c) (bc:b≠c)
    (za:Q.eval a=0) (zb:Q.eval b=0) (zc:Q.eval c=0) : cubic a b c ∣ Q := by
  obtain ⟨P,hP⟩:=dvd_iff_isRoot.mpr za
  rw [hP,eval_mul,eval_sub,eval_X,eval_C] at zb zc
  obtain ⟨R,hR⟩:=dvd_iff_isRoot.mpr ((mul_eq_zero.mp zb).resolve_left (sub_ne_zero.mpr ab.symm))
  have cr: P.eval c=0:=(mul_eq_zero.mp zc).resolve_left (sub_ne_zero.mpr ac.symm)
  rw [hR,eval_mul,eval_sub,eval_X,eval_C] at cr
  obtain ⟨S,hS⟩:=dvd_iff_isRoot.mpr ((mul_eq_zero.mp cr).resolve_left (sub_ne_zero.mpr bc.symm))
  exact ⟨S,by rw [hP,hR,hS];dsimp [cubic];ring⟩

set_option maxHeartbeats 2000000 in
/-- A nonzero fixed-knot determinant kills every quintic residual, with
arbitrary coefficients in the ambient characteristic-zero field. -/
theorem quintic_of_nonsingular {Q:K[X]} {a b c u:K} (ab:a≠b) (ac:a≠c) (bc:b≠c)
    (hu:u≠0) (z0:Q.eval a=0) (z1:Q.eval b=0) (z2:Q.eval c=0) (dq:Q.natDegree≤5)
    (localTests:∀k:Fin 3,(Paired.primitive (X^(1+k.val)*Q)).eval u=0)
    (det:obstruction a b c u≠0) : Q=0 := by
  obtain ⟨H,rep⟩:=divides_cubic ab ac bc z0 z1 z2
  by_cases hH:H=0
  · simp [rep,hH]
  have cn:cubic a b c≠0:=mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  have dp:H.natDegree≤2 := by rw [rep,natDegree_mul cn hH,cubic_degree] at dq;omega
  let h0:=H.coeff 0
  let h1:=H.coeff 1
  let h2:=H.coeff 2
  have shape:H=C h0+C h1*X+C h2*X^2:=by
    conv_lhs=>rw [H.as_sum_range' 3 (by omega)]
    simp [Finset.sum_range_succ,←C_mul_X_pow_eq_monomial,h0,h1,h2]
  let J (t:ℕ):K:=(Paired.primitive (X^t*cubic a b c)).eval u
  let M (t:ℕ):K:=momentForm t a b c u
  have ej (t:ℕ) (lo:1≤t) (hi:t≤5):2520*J t=u^(t+1)*M t := by
    have e:=local_moment (⟨t-1,by omega⟩:Fin 5) a b c u
    simpa only [show t-1+1=t by omega,show t-1+2=t+1 by omega] using e
  have sys (k:Fin 3) : M (k.val+1)*h0+M (k.val+2)*(u*h1)+M (k.val+3)*(u^2*h2)=0 := by
    let d:=k.val+1
    have test:=localTests k
    rw [Nat.add_comm 1 k.val] at test
    have mulq:X^d*Q=h0 •(X^d*cubic a b c)+h1 •(X^(d+1)*cubic a b c)+h2 •(X^(d+2)*cubic a b c) :=by
      rw [rep,shape,Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul,pow_add,pow_add]
      ring
    change (Paired.primitive (X^d*Q)).eval u=0 at test
    rw [mulq,map_add,map_add,map_smul,map_smul,map_smul,eval_add,eval_add,eval_smul,eval_smul,eval_smul] at test
    change h0*J d+h1*J (d+1)+h2*J (d+2)=0 at test
    apply (mul_eq_zero.mp (show u^(d+1)*(M d*h0+M (d+1)*(u*h1)+M (d+2)*(u^2*h2))=0 from ?_)).resolve_left (pow_ne_zero _ hu)
    calc
      _ = (u^(d+1)*M d)*h0+(u^(d+1+1)*M (d+1))*h1+(u^(d+2+1)*M (d+2))*h2 := by ring
      _ = _ := by
        rw [←ej d (by dsimp [d];omega) (by dsimp [d];have:=k.isLt;omega),
          ←ej (d+1) (by omega) (by dsimp [d];have:=k.isLt;omega),
          ←ej (d+2) (by omega) (by dsimp [d];have:=k.isLt;omega)]
        linear_combination 2520*test
  have x0:=sys 0;have x1:=sys 1;have x2:=sys 2
  change M 1*h0+M 2*(u*h1)+M 3*(u^2*h2)=0 at x0
  change M 2*h0+M 3*(u*h1)+M 4*(u^2*h2)=0 at x1
  change M 3*h0+M 4*(u*h1)+M 5*(u^2*h2)=0 at x2
  let Δ:=hankel (M 1) (M 2) (M 3) (M 4) (M 5)
  have dn:Δ≠0:=det
  have c0:h0=0:=(mul_eq_zero.mp (show Δ*h0=0 by
    dsimp only [Δ,hankel]
    linear_combination (M 3*M 5-(M 4)^2)*x0+(M 3*M 4-M 2*M 5)*x1+(M 2*M 4-(M 3)^2)*x2)).resolve_left dn
  have c1:u*h1=0:=(mul_eq_zero.mp (show Δ*(u*h1)=0 by
    dsimp only [Δ,hankel]
    linear_combination (M 3*M 4-M 2*M 5)*x0+(M 1*M 5-(M 3)^2)*x1+(M 2*M 3-M 1*M 4)*x2)).resolve_left dn
  have c2:u^2*h2=0:=(mul_eq_zero.mp (show Δ*(u^2*h2)=0 by
    dsimp only [Δ,hankel]
    linear_combination (M 2*M 4-(M 3)^2)*x0+(M 2*M 3-M 1*M 4)*x1+(M 1*M 3-(M 2)^2)*x2)).resolve_left dn
  rw [rep,shape,c0,(mul_eq_zero.mp c1).resolve_left hu,(mul_eq_zero.mp c2).resolve_left (pow_ne_zero _ hu)]
  simp
end
end RKCert.DirkQuintic
