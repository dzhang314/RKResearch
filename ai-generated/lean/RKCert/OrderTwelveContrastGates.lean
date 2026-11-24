module
public import RKCert.OrderTwelveChronologicalContrast
public import RKCert.OrderTwelveGhost

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {r:ℕ} {U:Submodule K (Vec K (s+1))} {w v:Vec K (s+1)}

theorem low_contrast_exclusion (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0)
    (hh:HeadData A r U w) (hV:U.map (diag v)≤U)
    (P:K[X]) (hP:P≠0) (dP:P.natDegree≤2) (hv:v∈zeroSpace A 2)
    (fit:v*w-weightedEval (nodes A) w P∈U) : False := by
  have pay (R:K[X]) (dR:R.natDegree≤3) : weightedEval (nodes A) v R∈zeroSpace A 5 :=
    zeroSpace_mono A (by omega : 2+R.natDegree≤5)
      (stage_weighted_grade ho R (by omega) hv)
  have leak (R:K[X]) (dR:R.natDegree≤3) :
      contrastResidual A v P R-((0:K)*R.coeff 3) • evalNodes A ghost7∈escape7 A := by
    simp only [zero_mul,zero_smul,sub_zero]
    have h := contrast_residual_grade (A:=A) (v:=v) P R
      (natDegree_mul_le.trans (by omega : R.natDegree+P.natDegree≤5)) (pay R dR)
    exact (show zeroSpace A 6≤escape7 A from le_sup_left) h
  obtain ⟨k,hu,_,eq⟩ := chronological_multiplier_contrast ha ho hs hi hh hV
    P X hP X_ne_zero (by omega) (by simp)
    (zeroSpace_mono A (by decide : 5≤6) (pay X (by simp))) fit 0 leak
  let u:=nodes A k
  have hu' : u≠0 := by simpa only [eval_X] using hu
  classical
  let a:Fin 3→K:=fun j=>P.coeff j.val
  have a_eq : ofFn 3 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have val (i:Fin 3) : moment a u (i.val+1)=0 := by
    have e := eq (X^i.val) (by
      rw [←pow_succ,natDegree_X_pow]
      have := i.isLt
      omega)
    rw [←pow_succ,←a_eq,primitive_monomial_moment,zero_mul,zero_mul] at e
    exact e
  let A' := EndpointPhysical.rescale a u
  have m (i:Fin 3) : (∑j:Fin 3,A' j/((i.val+j.val+2:ℕ):K))=0 := by
    have e := EndpointPhysical.moment_rescale a u 1 (i.val+1)
    rw [mul_one,val i] at e
    have h := (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hu')
    simpa only [A',moment,one_pow,mul_one,show ∀j:Fin 3,
      j.val+(i.val+1)+1=i.val+j.val+2 from fun j=>by omega] using h
  have a0' := shifted_hilbert_kernel (d:=2) (by decide) A' m
  have a0 : a=0 := by
    ext j
    have h := congrFun a0' j
    change a j*u^j.val=0 at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hu')
  apply hP
  rw [←a_eq,a0,map_zero]

omit [CharZero K] in
theorem mesh_eligible (u:K) (hu:u≠0) (hm:u=1∨(mesh6:K[X]).eval u=0) :
    RKCert.OrderTwelve.endpoint u=0 := by
  rcases hm with h|h
  · simp [RKCert.OrderTwelve.endpoint,h]
  · rw [mesh_factor,eval_mul,eval_X,RKCert.OrderTwelve.eval_dFivePoly] at h
    unfold RKCert.OrderTwelve.endpoint
    rw [(mul_eq_zero.mp h).resolve_left hu,mul_zero]

theorem cubic_contrast_exclusion (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b (Fin.last s)≠0)
    (hh:HeadData A r U w) (hV:U.map (diag v)≤U)
    (P:K[X]) (hP:P≠0) (dP:P.natDegree≤3)
    (fit:v*w-weightedEval (nodes A) w P∈U)
    (cheap:∀ R:K[X],R.natDegree≤2→weightedEval (nodes A) v R∈zeroSpace A 5)
    (high:weightedEval (nodes A) v (X^3)∈zeroSpace A 6) :
    False := by
  classical
  obtain ⟨α,leak⟩:=cubic_single_leak ha ho hs hi P dP cheap high
  have hc (Q:K[X]) (hq:Q≠0) (dQ:Q.natDegree≤2) :=
    chronological_multiplier_contrast ha ho hs hi hh hV P Q hP hq dP (by omega)
      (zeroSpace_mono A (by decide : 5≤6) (cheap Q dQ)) fit α leak
  obtain ⟨k,hu,mesh,ak⟩:=hc X X_ne_zero (by simp)
  let u:=nodes A k
  have h_u : u≠0 := by simpa only [eval_X] using hu
  let Q:K[X]:=X*(X-C u)
  have nq : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  have dq : Q.natDegree=2 := by unfold Q;rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero _),natDegree_X,natDegree_X_sub_C]
  obtain ⟨j,ha',meshA,bj⟩:=hc Q nq (by rw [dq])
  let x:=nodes A j
  have hxa : x≠0 ∧ x≠u := by
    change Q.eval x≠0 at ha'
    simpa [Q,sub_ne_zero] using (mul_ne_zero_iff.mp (show x*(x-u)≠0 by simpa [Q] using ha'))
  let a:Fin 4→K:=fun j=>P.coeff j.val
  have a_eq : ofFn 4 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have value (z:K) (k:ℕ) :
     (Paired.primitive (X^k*P)).eval z=RKCert.OrderTwelve.cubicMoment z k a := by
    rw [←a_eq,primitive_monomial_moment]
    rfl
  have ev1 := ak (1:K[X]) (by simp)
  have ev2 := ak X (by
    have e : (X:K[X])*X=X^2 := by ring
    rw [e,natDegree_X_pow]
    decide)
  have ev3 := ak (X^2) (by rw [←pow_succ,natDegree_X_pow])
  have V1 : RKCert.OrderTwelve.cubicMoment u 1 a=0 := by
    rw [one_mul] at ev1
    have e1 := value u 1
    rw [pow_one] at e1
    have h : (X:K[X]).coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X];decide)
    rwa [e1,h,mul_zero,zero_mul] at ev1
  have V2 : RKCert.OrderTwelve.cubicMoment u 2 a=0 := by
    rw [show (X:K[X])*X=X^2 by ring,value,coeff_X_pow] at ev2
    simpa using ev2
  have V3 : RKCert.OrderTwelve.cubicMoment u 3 a+(-α)*RKCert.OrderTwelve.leakSeven u=0 := by
    rw [←pow_succ,value,coeff_X_pow,ite_eq_left rfl,mul_one,ghost7_val] at ev3
    linear_combination ev3
  have ec1 : (1:K[X])*Q=X^2-u • X := by rw [one_mul,Polynomial.smul_eq_C_mul];dsimp [Q];ring
  have ec2 : X*Q=X^3-u • X^2 := by rw [Polynomial.smul_eq_C_mul];dsimp [Q];ring
  have e4 := bj 1 (by rw [one_mul,dq];decide)
  have e5 := bj X (by exact natDegree_mul_le.trans (by rw [natDegree_X,dq]))
  have ev4 : RKCert.OrderTwelve.cubicMoment x 2 a-u*RKCert.OrderTwelve.cubicMoment x 1 a=0 := by
    -- Normalize the coefficient separately so the polynomial moment remains one fold.
    have cf : ((1:K[X])*Q).coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by rw [one_mul,dq];decide)
    rw [cf,mul_zero,zero_mul,ec1,sub_mul,smul_mul_assoc,map_sub,map_smul,eval_sub,eval_smul,value,
      ←pow_one (X:K[X]),value,smul_eq_mul] at e4
    exact e4
  have ev5 : RKCert.OrderTwelve.cubicMoment x 3 a-u*RKCert.OrderTwelve.cubicMoment x 2 a+
      (-α)*RKCert.OrderTwelve.leakSeven x=0 := by
    have cf : (X*Q).coeff 3=1 := by
      rw [ec2,coeff_sub,Polynomial.smul_eq_C_mul,Polynomial.coeff_C_mul,coeff_X_pow,coeff_X_pow]
      norm_num
    rw [cf,mul_one,ghost7_val,ec2,sub_mul,smul_mul_assoc,map_sub,map_smul,eval_sub,eval_smul,value,value,smul_eq_mul] at e5
    linear_combination e5
  have e := (RKCert.OrderTwelve.ghost_five_tests_zero u x
    (mesh_eligible u h_u mesh) (mesh_eligible x hxa.1 meshA) hxa.2
    a (-α) V1 V2 V3 ev4 ev5).1
  apply hP
  rw [←a_eq,e,map_zero]

end RKCert.Paired.OrderTwelve

