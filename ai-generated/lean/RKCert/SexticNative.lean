module
public import RKCert.SexticMomentCuts
@[expose] public section
namespace RKCert.Sextic
open Polynomial RKCert.FixedFactor RKCert.Paired
variable {K:Type*} [Field K]

/-- A nonzero polynomial vanishing on the distinct listed nodes is
divisible by the full monic node factor, including a node at zero. -/
theorem linearProduct_dvd (l:List K) (nd:l.Nodup) (Q:K[X])
    (roots:∀x∈l,Q.eval x=0) : linearProduct id l∣Q := by
  induction l generalizing Q with
  | nil=>simp [linearProduct]
  | cons a l ih=>
    have nd':=List.nodup_cons.mp nd
    obtain ⟨H,fac⟩:=dvd_iff_isRoot.mpr (roots a List.mem_cons_self)
    obtain ⟨T,rh⟩:=ih nd'.2 H (by
      intro x hx
      have e:=roots x (List.mem_cons_of_mem _ hx)
      rw [fac,eval_mul,eval_sub,eval_X,eval_C] at e
      exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr (fun eq=>nd'.1 (eq ▸ hx))))
    exact ⟨T,by rw [fac,rh];simp only [linearProduct,id_eq];ring⟩

variable [CharZero K]
/-- Two paid primitive observations remove an arbitrary sextic after
division by its five forced, distinct roots. The two coefficients of the
remaining affine factor are arbitrary elements of the base field. -/
theorem native_of_nonsingular (v:Fin 6→K) (inj:Function.Injective v) (nv:v (Fin.last 5)≠0)
    (Q:K[X]) (dq:Q.natDegree≤6) (qold:∀i:Fin 5,Q.eval (v i.castSucc)=0)
    (j₁:(primitive (X*Q)).eval (v (Fin.last 5))=0)
    (j₂:(primitive (X^2*Q)).eval (v (Fin.last 5))=0) (non:tuple v≠0) : Q=0 := by
  let u:=v (Fin.last 5)
  let T:=linearProduct id (old v)
  have nd:(old v).Nodup:=List.nodup_ofFn.mpr (inj.comp (Fin.castSucc_injective _))
  have dt:T.natDegree=5:=by change (linearProduct id (old v)).natDegree=5;rw [degree_product];simp [old]
  have nt:T≠0:=(mono_product id (old v)).ne_zero
  obtain ⟨H,rep⟩:=linearProduct_dvd (old v) nd Q (by
    intro x hx;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx;exact qold i)
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
    row_primitive _ dt.le _ lo hi
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
    have c:FixedFactor.coeffs (old v)=T.coeff:=funext fun i=>(coeff_product (old v) i).symm
    simpa only [tuple,c,minor,M,u] using non
  have za:a=0:=(mul_eq_zero.mp (show (M 1*M 3-(M 2)^2)*a=0 by linear_combination M 3*x-M 2*y)).resolve_left de
  have zb:u*b=0:=(mul_eq_zero.mp (show (M 1*M 3-(M 2)^2)*(u*b)=0 by linear_combination M 1*y-M 2*x)).resolve_left de
  rw [rep,form,za,(mul_eq_zero.mp zb).resolve_left nv]
  simp

end RKCert.Sextic
