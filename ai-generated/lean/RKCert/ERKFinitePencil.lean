module
public import RKCert.ERKFiniteEndpointData
public import RKCert.FreeQuasiGate

@[expose] public section

/-! # Feed the actual prefix mesh to the free Jacobi pencil certificate -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 2500000

private def exceptionalVector (a : K) : Fin 5 → K :=
  ![(12*a-5)/70,(5-18*a)/14,18*a/7,-(5+6*a)/4,1]

private theorem exceptional_tests (a : K) (hq : 15*a^2-24*a+10=0) :
    twoTests (exceptionalVector a) a 3 := by
  refine ⟨?_,?_,?_⟩
  · intro k; fin_cases k <;> norm_num [moment,exceptionalVector,Fin.sum_univ_succ] <;> ring
  · norm_num [moment,exceptionalVector,Fin.sum_univ_succ]
    linear_combination -a^2*(a-1)^2*(2*a-1)/280*hq
  · norm_num [moment,exceptionalVector,Fin.sum_univ_succ]
    linear_combination -a^3*(a-1)^2*(5*a-2)/840*hq

/-- At an exceptional ratio the tested nonzero quartic has nonzero intercept.
The constant-term interface is not exported by the existing scalar gate. -/
theorem exceptional_constant (c : Fin 5 → K) (a : K) (ha : a≠0) (ha1 : a≠1) (ct : c 4≠0)
    (h : twoTests c a 3) (hq : 15*a^2-24*a+10=0) : c 0≠0 := by
  let e : Fin 4→K := fun i=>c i.castSucc-c 4*exceptionalVector a i.castSucc
  have hsplit (x : K) (k : ℕ) :
      moment e x k=moment c x k-c 4*moment (exceptionalVector a) x k := by
    simp [moment,e,exceptionalVector,Fin.sum_univ_succ]
    ring
  have eh := exceptional_tests a hq
  have tests : twoTests e a 3 := by
    refine ⟨fun k=>by rw [hsplit,h.1 k,eh.1 k,mul_zero,sub_zero],?_,?_⟩
    · rw [hsplit,hsplit]; linear_combination h.2.1-c 4*eh.2.1
    · rw [hsplit,hsplit]; linear_combination h.2.2-c 4*eh.2.2
  have e0 := congrFun (match3 e a ha ha1 tests) (0:Fin 4)
  have ec : c 0=c 4*((12*a-5)/70) := sub_eq_zero.mp e0
  have n : 12*a-5≠0 := by
    intro hz
    have ea : a=5/12 := by linear_combination (1/12)*hz
    rw [ea] at hq
    norm_num at hq
  rw [ec]
  exact mul_ne_zero ct (div_ne_zero n (by norm_num))

noncomputable def nativeD7 : K[X] :=
  from11 ![-72,2520,-27720,138600,-360360,504504,-360360,102960,0,0,0]

noncomputable def nativeD8 : K[X] :=
  from11 ![90,-3960,55440,-360360,1261260,-2522520,2882880,-1750320,437580,0,0]

omit [CharZero K] in
theorem nativeD7_eval (x : K) : (nativeD7:K[X]).eval x=jacDerivative7 x := by
  classical
  rw [nativeD7,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,jacDerivative7]
  ring

omit [CharZero K] in
theorem nativeD8_eval (x : K) : (nativeD8:K[X]).eval x=jacDerivative8 x := by
  classical
  rw [nativeD8,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,jacDerivative8]
  ring

theorem origin_pencil {G : K[X]} (t α : K) (g : G=t•dx7+α•dx8) :
    G=X*(t•nativeD7+α•nativeD8) := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ => (n:K)) Nat.cast_injective)
  intro x
  rw [g,eval_mul,eval_X,eval_add,eval_add,eval_smul,eval_smul,eval_smul,eval_smul,
    dx7_eval,dx8_eval,nativeD7_eval,nativeD8_eval]
  simp only [smul_eq_mul]
  ring

omit [CharZero K] in
theorem eval_rescale {n : ℕ} {P : K[X]} (e : Fin n→K) (ep : ofFn n e=P) (u x : K) :
    value (EndpointPhysical.rescale e u) x=P.eval (u*x) := by
  classical
  rw [←ep,ofFn_eq_sum_monomial,eval_finsetSum,value]
  apply Finset.sum_congr rfl
  intro i _
  simp [EndpointPhysical.rescale,mul_pow,mul_assoc]

theorem free_pencil_factor {P G : K[X]} {u v : K} {e : Fin 5→K}
    (J : KnotPair P G 8 u v) (pd : P.natDegree=4) (gd : G.natDegree=9) (fac : P∣G)
    (p0 : P.eval 0≠0) (ep : ofFn 5 e=P)
    (t α : K) (g : G=t•dx7+α•dx8) :
    ∃ q0 q1 q2 : K, ∀ x : K, jacDerivative8 (u*x)+(t/α)*jacDerivative7 (u*x)=
      (x-1)*(x-v/u)*value (EndpointPhysical.rescale e u) x*(q0+q1*x+q2*x^2) := by
  classical
  have u0:=J.u_ne
  have α0 : α≠0 := by
    intro hz
    have d := natDegree_smul_le t (dx7:K[X])
    rw [dx7_degree] at d
    rw [g,hz,zero_smul,add_zero] at gd
    omega
  obtain ⟨Q,qeq⟩ := fac
  have pr (x : K) (hx : P.eval x≠0) (hg : G.eval x=0) : Q.eval x=0 := by
    rw [qeq,eval_mul] at hg
    exact (mul_eq_zero.mp hg).resolve_left hx
  have gg := origin_pencil t α g
  have r0 : Q.eval 0=0 := pr 0 p0 (by simp [gg])
  have d0 : (X:K[X])∣Q := by
    simpa using (dvd_iff_isRoot (a:=(0:K))).mpr r0
  obtain ⟨Q0,q0eq⟩ := d0
  have qu : Q0.eval u=0 := (mul_eq_zero.mp (by simpa [q0eq] using pr u J.u_head J.u_mesh)).resolve_left J.u_ne
  have qv : Q0.eval v=0 := (mul_eq_zero.mp (by simpa [q0eq] using pr v J.v_head J.v_mesh)).resolve_left J.v_ne
  obtain ⟨Q1,q1eq⟩ := (dvd_iff_isRoot (a:=u)).mpr qu
  have q1v : Q1.eval v=0 := (mul_eq_zero.mp (by simpa [q1eq] using qv)).resolve_left (sub_ne_zero.mpr J.different)
  obtain ⟨R,q2eq⟩ := (dvd_iff_isRoot (a:=v)).mpr q1v
  let Z := (X-Polynomial.C u)*((X-Polynomial.C v)*R)
  have ge : G=X*(P*Z) := by rw [qeq,q0eq,q1eq,q2eq]; dsimp [Z]; ring
  have G0 : G≠0 := by
    intro z; rw [z,natDegree_zero] at gd; omega
  have pn : P≠0 := by
    intro z; rw [z,natDegree_zero] at pd; omega
  have rn : R≠0 := by
    intro z
    exact G0 (by simp [ge,Z,z])
  have zn : Z≠0 := mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _) rn)
  have rd : R.natDegree=2 := by
    rw [ge,natDegree_X_mul (mul_ne_zero pn zn),natDegree_mul pn zn,pd] at gd
    have zd : Z.natDegree=1+(1+R.natDegree) := by
      dsimp [Z]
      rw [natDegree_mul (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _) rn),
        natDegree_mul (X_sub_C_ne_zero _) rn,natDegree_X_sub_C,natDegree_X_sub_C]
    omega
  have eq : t•nativeD7+α•nativeD8=P*Z := mul_left_cancel₀ X_ne_zero (gg.symm.trans ge)
  let T := (u^2/α) • R.comp (Polynomial.C u*X)
  have Td : T.natDegree<3 := by
    have h := natDegree_comp_le (p:=R) (q:=Polynomial.C u*X)
    have qd : (Polynomial.C u*X).natDegree≤1 := natDegree_mul_le.trans (by simp)
    have Tle := natDegree_smul_le (u^2/α) (R.comp (Polynomial.C u*X))
    rw [rd] at h
    exact lt_of_le_of_lt (Tle.trans (h.trans (Nat.mul_le_mul_left 2 qd))) (by decide)
  refine ⟨T.coeff 0,T.coeff 1,T.coeff 2,fun x=>?_⟩
  have Cheb : T.eval x=T.coeff 0+T.coeff 1*x+T.coeff 2*x^2 := by
    rw [eval_eq_sum_range' Td x]
    simp [Finset.sum_range_succ,add_assoc]
  rw [←Cheb,eval_rescale e ep]
  have tv : T.eval x=(u^2/α)*R.eval (u*x) := by simp [T,eval_smul,eval_comp]
  rw [tv]
  have raw := congrArg (fun p:K[X]=>p.eval (u*x)) eq
  change (t•nativeD7+α•nativeD8:K[X]).eval (u*x)=(P*Z).eval (u*x) at raw
  simp only [eval_add,eval_smul,smul_eq_mul,nativeD7_eval,nativeD8_eval,Z,eval_mul,eval_sub,eval_X,eval_C] at raw
  apply mul_left_cancel₀ α0
  calc
    α * (jacDerivative8 (u*x)+(t/α)*jacDerivative7 (u*x)) =
        t*jacDerivative7 (u*x)+α*jacDerivative8 (u*x) := by
      field_simp
      ring
    _ = P.eval (u*x)*((u*x-u)*((u*x-v)*R.eval (u*x))) := raw
    _ = α*((x-1)*(x-v/u)*P.eval (u*x)*(u^2/α*R.eval (u*x))) := by
      field_simp

theorem prefix8_no_profile {P G : K[X]} {u v : K} (J : KnotPair P G 8 u v)
    (dP : P.natDegree≤4) (Gd : G.natDegree=9) (fac : P∣G)
    (t α : K) (g : G=t•dx7+α•dx8) : P=0 := by
  classical
  by_cases small:P.natDegree≤3
  · exact cubic_no_profile (by decide) J small
  have pd : P.natDegree=4 := by omega
  let e : Fin 5→K := fun i=>P.coeff i.val
  have ep : ofFn 5 e=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  let c := EndpointPhysical.rescale e u
  let a := v/u
  have ta : twoTests c a 3 := EndpointPhysical.normalize J.u_ne (endpoint_tests_three J (by decide) e ep)
  have a0 : a≠0 := div_ne_zero J.v_ne J.u_ne
  have a1 : a≠1 := fun h=>J.different ((div_eq_one_iff_eq J.u_ne).mp h)
  have of_zero (z : c=0) : P=0 := by
    have ee := (EndpointPhysical.rescale_eq_zero_iff e J.u_ne).mp z
    rw [←ep,ee,map_zero]
  rcases quartic_three_two c a a0 a1 ta with hz|hq
  · exact of_zero hz
  have P4 : P.coeff 4≠0 := by
    rw [←pd,coeff_natDegree,leadingCoeff_ne_zero]
    intro z; rw [z,natDegree_zero] at pd; omega
  have c4 : c 4≠0 := mul_ne_zero P4 (pow_ne_zero _ J.u_ne)
  have c0 := exceptional_constant c a a0 a1 c4 ta hq
  have P0 : P.eval 0≠0 := by simpa [c,EndpointPhysical.rescale,e,←coeff_zero_eq_eval_zero] using c0
  exact of_zero (freeQuasi17_quartic_gate c a u (t/α) a0 a1 J.u_ne ta
    (free_pencil_factor J pd Gd fac P0 ep t α g))

end RKCert.Paired.FiniteMidpoint

