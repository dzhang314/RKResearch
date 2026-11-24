module
public import RKCert.DirkEightPortField
public import RKCert.DirkSevenHankel
@[expose] public section
namespace RKCert.SevenPort
open Polynomial RKCert.Endpoint RKCert.EndpointPhysical RKCert.Paired
variable {K:Type*} [Field K] [CharZero K]
noncomputable section
set_option maxRecDepth 3500
set_option maxHeartbeats 1500000
def shape (a:K) (i:Fin 5):K:=match i.val with
  | 0=>(12*a-5)/70
  | 1=>(5-18*a)/14
  | 2=>18*a/7
  | 3=> -(5+6*a)/4
  | _=>1
private theorem tests_shape (a:K) (qa:15*a^2-24*a+10=0):twoTests (shape a) a 3:=by
  constructor
  · intro k;fin_cases k <;> norm_num [moment,shape,Fin.sum_univ_succ] <;> ring
  constructor
  · norm_num [moment,shape,Fin.sum_univ_succ];linear_combination -a^2*(a-1)^2*(2*a-1)/280*qa
  · norm_num [moment,shape,Fin.sum_univ_succ];linear_combination -a^3*(a-1)^2*(5*a-2)/840*qa
private theorem only_shape (c:Fin 5→K) (a:K) (an:a≠0) (a1:a≠1) (h:twoTests c a 3)
    (qa:15*a^2-24*a+10=0):∀i,c i=c 4*shape a i:=by
  let v:Fin 4→K:=fun i=>c i.castSucc-c 4*shape a i.castSucc
  have eqn(x:K)(k:ℕ):moment v x k=moment c x k-c 4*moment (shape a) x k:=by simp [v,moment,shape,Fin.sum_univ_succ];ring
  have sh:=tests_shape a qa
  have hv:twoTests v a 3:=by
    refine ⟨fun i=>?_,?_,?_⟩
    · rw [eqn,h.1 i,sh.1 i];ring
    · rw [eqn,eqn];linear_combination h.2.1-c 4*sh.2.1
    · rw [eqn,eqn];linear_combination h.2.2-c 4*sh.2.2
  have van:=match3 v a an a1 hv
  have zz(i:Fin 4):c i.castSucc=c 4*shape a i.castSucc:=sub_eq_zero.mp (congrFun van i)
  intro i;fin_cases i
  · exact zz 0
  · exact zz 1
  · exact zz 2
  · exact zz 3
  · simp [shape]

def body (t u:K):K[X]:=∑i:Fin 7,C (ec t i*u^(6-i.val))*X^i.val

theorem shape_body (a u:K):body (15*a) u=C (31500:K)*(X-C u)*(X-C (a*u))*
    (∑i:Fin 5,C (shape a i*u^(4-i.val))*X^i.val):=by
  let : Infinite K:=Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective
  apply Polynomial.funext;intro x
  simp [body,ec,shape,Fin.sum_univ_succ]
  ring

/-- Native 3+2 primitive measurements force a specific monic exceptional
quartic up to scaling; multiply by the two distinct physical linear factors
to obtain the integer homogeneous sixth-degree pencil for the rank test. -/
theorem native_shape (Q:K[X]) (dq:Q.natDegree≤4) (nz:Q≠0) {u v:K}(un:u≠0)(vn:v≠0)(diff:v≠u)
    (first:∀k:Fin 3,(primitive (X^(k.val+1)*Q)).eval u=0)
    (next:∀k:Fin 2,(primitive (X^(k.val+1)*((X-C u)*Q))).eval v=0):
    ∃a d:K,v=a*u ∧ d≠0 ∧ 15*a^2-24*a+10=0 ∧
      (X-C u)*(X-C v)*Q=C d*body (15*a) u:=by
  let a:=v/u
  let c:Fin 5→K:=fun i=>Q.coeff i.val
  have tests(k:ℕ)(t:K):(primitive (X^k*Q)).eval t=moment c t k:=by
    rw [←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul Q t k dq]
    apply Finset.sum_congr rfl;intro i _;simp only [c,Nat.add_comm k i.val]
  have next'(k:Fin 2):moment c v (k.val+2)-u*moment c v (k.val+1)=0:=by
    have h:=next k
    have eqn:X^(k.val+1)*((X-C u)*Q)=X^(k.val+2)*Q-u • (X^(k.val+1)*Q):=by
      rw [show k.val+2=(k.val+1)+1 by omega,pow_succ,Polynomial.smul_eq_C_mul];ring
    rwa [eqn,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,tests,tests] at h
  have measured:=normalize (c:=c) (d:=3) un ⟨fun k=>(tests _ _).symm.trans (first k),next' 0,next' 1⟩
  have rn:a≠0:=div_ne_zero vn un
  have r1:a≠1:=fun h=>diff ((div_eq_one_iff_eq un).mp h)
  have cn:c≠0:=by
    intro z;apply nz;ext n
    by_cases small:n<5
    · simpa [c] using congrFun z (⟨n,small⟩:Fin 5)
    · rw [coeff_zero,coeff_eq_zero_of_natDegree_lt (by omega:Q.natDegree<n)]
  have qa:15*a^2-24*a+10=0:=(quartic_three_two _ a rn r1 measured).resolve_left (fun z=>cn ((rescale_eq_zero_iff c un).mp z))
  have sc:=only_shape _ a rn r1 measured qa
  have vv:v=a*u:=by dsimp [a];field_simp
  have eqc(i:Fin 5):c i=c 4*(shape a i*u^(4-i.val)):=by
    apply mul_right_cancel₀ (pow_ne_zero i.val un)
    have e:u^(4-i.val)*u^i.val=u^4:=by rw [←pow_add,show 4-i.val+i.val=4 by have:=i.isLt;omega]
    calc
      c i*u^i.val=(c 4*u^4)*shape a i:=sc i
      _= c 4*(shape a i*u^(4-i.val))*u^i.val:=by rw [←e];ring
  have lead:c 4≠0:=by
    intro z;apply cn;funext i;rw [eqc i,z,zero_mul];rfl
  have form:Q=C (c 4)*(∑i:Fin 5,C (shape a i*u^(4-i.val))*X^i.val):=by
    conv_lhs=>rw [Q.as_sum_range' 5 (by omega),←Fin.sum_univ_eq_sum_range]
    rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
    rw [←C_mul_X_pow_eq_monomial,←mul_assoc,←C_mul,←eqc]
  refine ⟨a,c 4/31500,vv,div_ne_zero lead (by norm_num),qa,?_⟩
  rw [shape_body,form,←vv]
  have cf:C (c 4/31500)*C (31500:K)=C (c 4):=by rw [←C_mul,div_mul_cancel₀ _ (by norm_num)]
  linear_combination -((X-C u)*(X-C v)*(∑i:Fin 5,C (shape a i*u^(4-i.val))*X^i.val))*cf
end
end RKCert.SevenPort
