module
public import RKCert.Dirk17RadauMinor
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.FixedFactor RKCert.DirkQuintic RKCert.Paired RKCert.Sextic
variable {K:Type*} [Field K] [CharZero K]
theorem native_of_nonsingular (v:Fin 5→K) (inj:Function.Injective v) (nv:v (Fin.last 4)≠0)
    (Q:K[X]) (dq:Q.natDegree≤5) (qoldFour:∀i:Fin 4,Q.eval (v i.castSucc)=0)
    (j₁:(primitive (X*Q)).eval (v (Fin.last 4))=0)
    (j₂:(primitive (X^2*Q)).eval (v (Fin.last 4))=0) (non:tupleFour v≠0) : Q=0 := by
  let u:=v (Fin.last 4)
  let T:=linearProduct id (oldFour v)
  have nd:(oldFour v).Nodup:=List.nodup_ofFn.mpr (inj.comp (Fin.castSucc_injective _))
  have dt:T.natDegree=4:=by change (linearProduct id (oldFour v)).natDegree=4;rw [degree_product];simp [oldFour]
  have nt:T≠0:=(mono_product id (oldFour v)).ne_zero
  obtain ⟨H,rep⟩:=linearProduct_dvd (oldFour v) nd Q (by
    intro x hx;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx;exact qoldFour i)
  change Q=T*H at rep
  by_cases hn:H=0
  · simp [rep,hn]
  have bound:H.natDegree≤1:=by rw [rep,natDegree_mul nt hn,dt] at dq;omega
  let a:=H.coeff 0
  let b:=H.coeff 1
  have form:H=C a+C b*X:=by
    conv_lhs=>rw [H.as_sum_range' 2 (by omega)]
    simp [Finset.sum_range_succ,←C_mul_X_pow_eq_monomial,a,b]
  let J (k:ℕ):K:=(primitive (X^k*T)).eval u
  let M (k:ℕ):K:=row T.coeff u k
  have eqJ (k:ℕ) (lo:1≤k) (hi:k≤3) : (2520:K)*J k=u^(k+1)*M k :=
    row_primitive _ (by omega) _ lo hi
  have sys (k:ℕ) (lo:1≤k) (hi:k≤2) (hh:(primitive (X^k*Q)).eval u=0) :
      M k*a+M (k+1)*(u*b)=0 := by
    have poly : X^k*Q=a • (X^k*T)+b • (X^(k+1)*T) :=by
      rw [rep,form,Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul,pow_succ];ring
    rw [poly,map_add,map_smul,map_smul,eval_add,eval_smul,eval_smul] at hh
    change a*J k+b*J (k+1)=0 at hh
    apply (mul_eq_zero.mp (show u^(k+1)*(M k*a+M (k+1)*(u*b))=0 from ?_)).resolve_left (pow_ne_zero _ nv)
    calc
      _ = (u^(k+1)*M k)*a+(u^(k+1+1)*M (k+1))*b := by ring
      _ = 0 := by rw [←eqJ k lo (by omega),←eqJ (k+1) (by omega) (by omega)];linear_combination 2520*hh
  have x:=sys 1 (by decide) (by decide) (by simpa only [pow_one] using j₁)
  have y:=sys 2 (by decide) (by decide) j₂
  change M 1*a+M 2*(u*b)=0 at x
  change M 2*a+M 3*(u*b)=0 at y
  have de:M 1*M 3-(M 2)^2≠0:=by
    have c:FixedFactor.coeffs (oldFour v)=T.coeff:=funext fun i=>(coeff_product (oldFour v) i).symm
    simpa only [tupleFour,c,minor,M,u] using non
  have za:a=0:=(mul_eq_zero.mp (show (M 1*M 3-(M 2)^2)*a=0 by linear_combination M 3*x-M 2*y)).resolve_left de
  have zb:u*b=0:=(mul_eq_zero.mp (show (M 1*M 3-(M 2)^2)*(u*b)=0 by linear_combination M 1*y-M 2*x)).resolve_left de
  rw [rep,form,za,(mul_eq_zero.mp zb).resolve_left nv]
  simp

end RKCert.RadauEight
