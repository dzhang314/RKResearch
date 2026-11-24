module
public import RKCert.ERKOrderFifteenChart
public import RKCert.Dirk15ArithmeticSpecialize
public import RKCert.Dirk15Replay.PairF6K4E0

@[expose] public section

/-! # The ERK free pencil is exactly the shared degree-120 companion pair.
No new arithmetic tape, interlacing premise, or split-root assumption. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.FixedPolynomial Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem dx6_integer_pencil : (dx6:K[X])=X*fieldJacobi K 6 := by
  ext i
  by_cases hi:i≤7
  · interval_cases i <;> norm_num [dx6_coeff,coeff_X_mul,coeff_map,integerJacobi_coeff,Nat.choose]
  · have h : (X*fieldJacobi K 6).natDegree=7 := by
      rw [natDegree_X_mul (fieldJacobi_nonzero 6),fieldJacobi_degree]
    rw [coeff_eq_zero_of_natDegree_lt (by rw [dx6_degree];omega),
      coeff_eq_zero_of_natDegree_lt (by rw [h];omega)]

theorem dx7_integer_pencil : (dx7:K[X])=X*fieldJacobi K 7 := by
  ext i
  by_cases hi:i≤8
  · interval_cases i <;> norm_num [dx7_coeff,coeff_X_mul,coeff_map,integerJacobi_coeff,Nat.choose]
  · have h : (X*fieldJacobi K 7).natDegree=8 := by
      rw [natDegree_X_mul (fieldJacobi_nonzero 7),fieldJacobi_degree]
    rw [coeff_eq_zero_of_natDegree_lt (by rw [dx7_degree];omega),
      coeff_eq_zero_of_natDegree_lt (by rw [h];omega)]

theorem marked_seven_integer_pencil {G:K[X]} (mesh:OddSevenMesh G 1) (gd:G.natDegree=8) :
    ∃ t a:K,t≠0 ∧ G=C t*(X*fieldPencil K 6 a) := by
  cases mesh with
  | marked v u eq =>
    have un:u≠0 := by
      intro z
      rw [z,zero_smul,add_zero] at eq
      have h := (natDegree_smul_le v (dx6:K[X])).trans_eq dx6_degree
      rw [←eq,gd] at h
      omega
    refine ⟨u,v/u,un,?_⟩
    have hc : C u*C (v/u)=C v := by
      rw [←map_mul,mul_comm u (v/u),div_mul_cancel₀ _ un]
    rw [eq,dx6_integer_pencil,dx7_integer_pencil,smul_eq_C_mul,smul_eq_C_mul]
    change C v*(X*fieldJacobi K 6)+C u*(X*fieldJacobi K 7)=
      C u*(X*(fieldJacobi K 7+C (v/u)*fieldJacobi K 6))
    rw [←hc]
    ring

theorem variable_fifteen_pencil_gate {P G:K[X]} {u:K}
    (mesh:OddSevenMesh G 1) (gd:G.natDegree=8) (pd:P.natDegree=4)
    (pf:P∣G) (p0:P.eval 0≠0) (un:u≠0) (pu:P.eval u≠0) (gu:G.eval u=0)
    (h1:(primitive (X*P)).eval u=0) (h2:(primitive (X*(X*P))).eval u=0) : False := by
  obtain ⟨t,a,tn,ge⟩:=marked_seven_integer_pencil mesh gd
  let H:=fieldPencil K 6 a
  have ge' : G=C t*(X*H) := ge
  have hu : H.eval u=0 := by
    rw [ge',eval_mul,eval_C,eval_mul,eval_X] at gu
    exact (mul_eq_zero.mp ((mul_eq_zero.mp gu).resolve_left tn)).resolve_left un
  have hd : P∣H := by
    obtain ⟨Q,e⟩:=pf
    have er := congrArg (fun R:K[X]=>R.eval 0) (ge'.symm.trans e)
    simp only [eval_mul,eval_X,eval_C,zero_mul,mul_zero] at er
    have q0 := (mul_eq_zero.mp er.symm).resolve_left p0
    obtain ⟨R,rEq⟩:= (show (X:K[X])∣Q from by
      simpa using (dvd_iff_isRoot (a:=(0:K))).mpr q0)
    have pair : C t*H=P*R := by
      apply mul_left_cancel₀ X_ne_zero
      calc
        X*(C t*H)=G := by rw [ge']; ring
        _ = P*Q := e
        _ = X*(P*R) := by rw [rEq]; ring
    exact ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr tn)).dvd_mul_left).mp ⟨R,pair⟩
  have p1 : Signature.paidMoment ((1-X)^0*P) u 1=0 := by
    simpa only [Signature.paidMoment,RKCert.Endpoint.formalPrimitive_eq_treePrimitive,
      pow_zero,pow_one,one_mul] using h1
  have p2 : Signature.paidMoment ((1-X)^0*P) u 2=0 := by
    rw [Signature.paidMoment,RKCert.Endpoint.formalPrimitive_eq_treePrimitive,pow_zero,
      one_mul,pow_two,mul_assoc]
    exact h2
  have z1 := nodeMomentNorm_zero (n:=6) (k:=4) (j:=1) (w:=0) (by decide) (by decide)
    un pd hu hd pu p1
  have z2 := nodeMomentNorm_zero (n:=6) (k:=4) (j:=2) (w:=0) (by decide) (by decide)
    un pd hu hd pu p2
  have cap (j:ℕ) : (nodeMomentNorm 6 4 j 0).natDegree≤120 := by
    rw [←show momentCap 6 4 0=120 by decide]
    exact nodeMomentNorm_degree (n:=6) (k:=4) (by decide) (by decide) j 0
  exact FixedReplay.F6K4E0.no_common (cap 1) (cap 2) u z1 z2

end RKCert.Paired.FiniteMidpoint
