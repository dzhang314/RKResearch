module
public import RKCert.ERKOrder13PencilData
public import RKCert.ERKOrder13MarkedPureMasks
public import RKCert.FactorPrimitiveScale

@[expose] public section

/-! # Exact bridge from the paired physical moments to the integer tape
The two divisions are ordinary synthetic division by the actual detected
roots. There is no split-field premise, and the numerical certificate sees
no Runge–Kutta tableau entries. -/
namespace RKCert.Paired.FiniteMidpoint.Pencil13
open RKCert.Paired Polynomial RKCert.OrderTwelve RKCert.GoodPrimeDense
  RKCert.DenseCommonRoot RKCert.FixedFactor
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 9000000
set_option maxRecDepth 16000

def f1 (u:K) := -27*dFive u-20*dSixValue u
def f2 (u:K) := 225*dFive u+120*dSixValue u
def f3 (u:K) := -825*dFive u-300*dSixValue u
def f4 (u:K) := 1485*dFive u+330*dSixValue u
def f5 (u:K) := -1287*dFive u-132*dSixValue u
def f6 (u:K) := 429*dFive u

def t5 (u:K) := f6 u
def t4 (u:K) := f5 u+u*t5 u
def t3 (u:K) := f4 u+u*t4 u
def t2 (u:K) := f3 u+u*t3 u
def t1 (u:K) := f2 u+u*t2 u
def t0 (u:K) := f1 u+u*t1 u

def q4 (u _v:K) := t5 u
def q3 (u v:K) := t4 u+v*q4 u v
def q2 (u v:K) := t3 u+v*q3 u v
def q1 (u v:K) := t2 u+v*q2 u v
def q0 (u v:K) := t1 u+v*q1 u v
def rem (u v:K) := t0 u+v*q0 u v

noncomputable def syntheticQuartic (u v:K) : K[X] :=
  ofCoeffList [q0 u v,q1 u v,q2 u v,q3 u v,q4 u v]

def m₀ (u v z:K) : K :=
  q0 u v/2+z*(q1 u v/3+z*(q2 u v/4+z*(q3 u v/5+z*q4 u v/6)))

def m₁ (u v z:K) : K :=
  q0 u v/3+z*(q1 u v/4+z*(q2 u v/5+z*(q3 u v/6+z*q4 u v/7)))

omit [CharZero K] in
theorem anchor_eval (u:K) : read (Int.castRingHom K) u anchor=dFive u := by
  norm_num [anchor,GoodPrimeDense.read,dFive]
  ring

omit [CharZero K] in
theorem omitted_eval (u v:K) :
    read (read (Int.castRingHom K) u) v omitted=rem u v := by
  norm_num [omitted,GoodPrimeDense.read,rem,q0,q1,q2,q3,q4,t0,t1,t2,t3,t4,t5,
    f1,f2,f3,f4,f5,f6,dFive,dSixValue]
  ring

theorem firstMoment_eval (u v:K) :
    read (read (Int.castRingHom K) u) v firstMoment=60*m₀ u v u := by
  norm_num [firstMoment,GoodPrimeDense.read,m₀,q0,q1,q2,q3,q4,t0,t1,t2,t3,t4,t5,
    f1,f2,f3,f4,f5,f6,dFive,dSixValue]
  ring

theorem crossMoment_eval (u v:K) :
    read (read (Int.castRingHom K) u) v crossMoment=
      420*(dFive u*(v^2*m₁ u v v-u*v*m₀ u v v)-dFive v*u^2*m₁ u v u) := by
  norm_num [crossMoment,GoodPrimeDense.read,m₀,m₁,q0,q1,q2,q3,q4,t0,t1,t2,t3,t4,t5,
    f1,f2,f3,f4,f5,f6,dFive,dSixValue]
  ring

theorem synthetic_identity (u v:K) :
    dFive u • (dSixPoly:K[X])-dSixValue u • dFivePoly =
      (X-C u)*((X-C v)*syntheticQuartic u v+C (rem u v)) := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro z
  norm_num [syntheticQuartic,ofCoeffList_cons,ofCoeffList_nil,dFivePoly,dSixPoly,eval_smul,
    rem,q0,q1,q2,q3,q4,t0,t1,t2,t3,t4,t5,f1,f2,f3,f4,f5,f6,dFive,dSixValue]
  ring

omit [CharZero K] in
private theorem synthetic_degree (u v:K) : (syntheticQuartic u v).natDegree≤4 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [syntheticQuartic,coeff_ofCoeffList,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp;omega)]
  rfl

omit [CharZero K] in
theorem synthetic_mom₀ (u v z:K) :
    (primitive (X*syntheticQuartic u v)).eval z=z^2*m₀ u v z := by
  rw [weighted_primitive_sum 4 _ (synthetic_degree u v)]
  norm_num [syntheticQuartic,coeff_ofCoeffList,Finset.sum_range_succ,m₀,List.getD_eq_getElem?_getD]
  ring

omit [CharZero K] in
theorem synthetic_mom₁ (u v z:K) :
    (primitive (X*(X*syntheticQuartic u v))).eval z=z^3*m₁ u v z := by
  have p : (X*syntheticQuartic u v).natDegree≤5 :=
    natDegree_mul_le.trans (by have := synthetic_degree u v;rw [natDegree_X];omega)
  rw [weighted_primitive_sum 5 _ p]
  norm_num [coeff_X_mul_zero,coeff_X_mul,syntheticQuartic,coeff_ofCoeffList,Finset.sum_range_succ,
    m₁,List.getD_eq_getElem?_getD]
  ring

omit [CharZero K] in
theorem primitive_linear_mask (P:K[X]) (u v:K) :
    (primitive ((X-C u)*(X*P))).eval v =
      (primitive (X*(X*P))).eval v-u*(primitive (X*P)).eval v := by
  rw [sub_mul,←smul_eq_C_mul,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul]

/-- The three algebraic equations consumed by the checked exact tape. -/
theorem physical_pair_to_integer (θ u v τ:K) (P:K[X])
    (un:u≠0) (vn:v≠0) (an:(dFivePoly:K[X]).eval u≠0)
    (fit:markPencil θ=(X-C u)*(X-C v)*P)
    (f0:(primitive (X*P)).eval u=0)
    (f1':(primitive (X*(X*P))).eval u=τ*u*(dFivePoly:K[X]).eval u)
    (f2:(primitive ((X-C u)*(X*P))).eval v=τ*v*(dFivePoly:K[X]).eval v) :
    read (Int.castRingHom K) u anchor≠0 ∧
      read (read (Int.castRingHom K) u) v omitted=0 ∧
      read (read (Int.castRingHom K) u) v firstMoment=0 ∧
      read (read (Int.castRingHom K) u) v crossMoment=0 := by
  have ev5 (z:K) : (dFivePoly:K[X]).eval z=dFive z := by simp [dFivePoly,dFive]
  rw [ev5] at an
  have rt:=congrArg (Polynomial.eval u) fit
  simp only [markPencil,eval_add,eval_mul,eval_C,eval_X,eval_sub,sub_self,zero_mul,
    ev5,dSixPoly_eval] at rt
  have eq : dFive u • (dSixPoly:K[X])-dSixValue u • dFivePoly =
      dFive u • markPencil θ := by
    rw [markPencil,smul_add,sub_eq_add_neg,←neg_smul]
    simp only [smul_eq_C_mul]
    rw [←mul_assoc (C (dFive u)),←C_mul]
    have aux : -(dSixValue u)=dFive u*θ := by linear_combination -rt
    rw [aux]
  have e := (synthetic_identity u v).symm.trans (eq.trans (congrArg (fun Q : K[X]=>dFive u • Q) fit))
  have e' : (X-C v)*syntheticQuartic u v+C (rem u v) =
      (X-C v)*(dFive u • P) := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero u)
    simpa only [mul_assoc,mul_smul_comm] using e
  have rr := congrArg (Polynomial.eval v) e'
  simp only [eval_add,eval_mul,eval_X,eval_C,eval_sub,sub_self,zero_mul,zero_add] at rr
  have qq : syntheticQuartic u v=dFive u • P := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero v)
    simpa only [rr,C_0,add_zero] using e'
  have lt (B:K[X]) (z:K) :
      (primitive (B*syntheticQuartic u v)).eval z=dFive u*(primitive (B*P)).eval z := by
    rw [qq,mul_smul_comm,map_smul,eval_smul,smul_eq_mul]
  have z0 : u^2*m₀ u v u=0 := by
    rw [←synthetic_mom₀,lt,f0,mul_zero]
  have z1 : u^3*m₁ u v u=dFive u*(τ*u*dFive u) := by
    rw [←synthetic_mom₁,←mul_assoc,lt,mul_assoc,f1',ev5]
  have z2 : v^3*m₁ u v v-u*(v^2*m₀ u v v)=dFive u*(τ*v*dFive v) := by
    rw [←synthetic_mom₀,←synthetic_mom₁,←primitive_linear_mask,←mul_assoc,lt,mul_assoc,f2,ev5]
  have a0 : m₀ u v u=0 := (mul_eq_zero.mp z0).resolve_left (pow_ne_zero _ un)
  refine ⟨by rwa [anchor_eval],by rwa [omitted_eval],by rw [firstMoment_eval,a0,mul_zero],?_⟩
  rw [crossMoment_eval]
  have b0 : dFive u*(v^2*m₁ u v v-u*v*m₀ u v v)-dFive v*u^2*m₁ u v u=0 := by
    apply mul_left_cancel₀ (mul_ne_zero un vn)
    rw [mul_zero]
    linear_combination (u*dFive u)*z2-(v*dFive v)*z1
  rw [b0,mul_zero]

end RKCert.Paired.FiniteMidpoint.Pencil13
