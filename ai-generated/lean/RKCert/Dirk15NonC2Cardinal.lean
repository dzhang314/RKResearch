module

public import RKCert.Dirk15NonC2FullFlag
public import RKCert.RadauRightDivisor
public import RKCert.DirkOneEndpointHilbert

@[expose] public section

/-! # Actual right-Radau scalar profile of the true terminal cardinal -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint RKCert.OneEscape
open RKCert.FixedPolynomial.Radau77569
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

def normalizedRightRadau7 : K[X] :=
  C ((rightRadau7 : K[X]).eval 1)⁻¹ * rightRadau7

theorem rightRadau7_one_ne : (rightRadau7 : K[X]).eval 1≠0 := by
  rw [eval_rightRadau7,sub_self]
  exact radau_left_zero_ne

theorem normalizedRightRadau7_one : (normalizedRightRadau7 : K[X]).eval 1=1 := by
  rw [normalizedRightRadau7,eval_mul,eval_C,inv_mul_cancel₀ rightRadau7_one_ne]

theorem normalizedRightRadau7_degree : (normalizedRightRadau7 : K[X]).natDegree=7 := by
  have left : (radauLeft7 : K[X]).natDegree=7 := by
    rw [←map_reproducer,natDegree_map_eq_of_injective Int.cast_injective,degree_reproducer]
  have rev : (rightRadau7 : K[X]).natDegree=(radauLeft7 : K[X]).natDegree := by
    apply le_antisymm (reflectPolynomial_degree _)
    have h := reflectPolynomial_degree (reflectPolynomial (radauLeft7 : K[X]))
    rwa [reflectPolynomial_involutive] at h
  rw [normalizedRightRadau7,natDegree_C_mul (inv_ne_zero rightRadau7_one_ne),rev,left]

theorem normalizedRightRadau7_zero_test (Q : K[X]) (dQ : Q.natDegree≤7) (h0 : Q.eval 1=0) :
    unitIntegral ((normalizedRightRadau7 : K[X])*Q)=0 := by
  unfold normalizedRightRadau7
  rw [show (C ((rightRadau7 : K[X]).eval 1)⁻¹*rightRadau7)*Q=
       ((rightRadau7 : K[X]).eval 1)⁻¹ • (Q*rightRadau7) by rw [smul_eq_C_mul]; ring,
    map_smul,smul_eq_mul,unitIntegral_apply]
  change _*(formalPrimitive (Q*reflectPolynomial (radauLeft7 : K[X]))).eval 1=0
  rw [radauRight7_reproduces _ dQ,h0,mul_zero]

set_option maxHeartbeats 1000000 in
/-- In the actual non-C(2) chart, the genuine terminal cardinal has the
normalized right Radau polynomial as its ordinary scalar profile. -/
theorem order15_nonC2_terminal_profile (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) :
    terminalCardinal K 19-evalNodes A (normalizedRightRadau7 : K[X])∈zeroSpace A 7 := by
  have H := order15_nonC2_rank_chart ha ho hq
  obtain ⟨P,dP,pure⟩ := exists_poly_zeroSpace_charZero A H.terminal_mem
  have tr : OrdinaryTrace A 7 (terminalCardinal K 19) P := ⟨dP,pure⟩
  have p1 : P.eval 1=1 := by
    have e := H.terminal_pure_zero _ pure
    change _ - P.eval (nodes A (Fin.last 19))=0 at e
    rw [H.terminal.node_one,show terminalCardinal K 19 (Fin.last 19)=(1:K) by simp only [terminalCardinal,Pi.single_eq_same]] at e
    exact (sub_eq_zero.mp e).symm
  have test (Q : K[X]) (dQ : Q.natDegree≤7) (q1 : Q.eval 1=0) :
      unitIntegral (P*Q)=0 := by
    have t := tr.pair_polynomial ho Q (by omega)
    rw [row_single_right,weightedEval_apply,H.terminal.node_one,q1,zero_mul] at t
    exact t.symm
  have every (Q : K[X]) (dQ : Q.natDegree≤7) :
      unitIntegral (P*Q)=unitIntegral P * Q.eval 1 := by
    let Q' := Q-C (Q.eval 1)
    have dq' : Q'.natDegree≤7 :=
      (natDegree_sub_le _ _).trans (max_le dQ (by simp))
    have q1' : Q'.eval 1=0 := by simp [Q']
    have e := test Q' dq' q1'
    rw [show P*Q'=P*Q-(Q.eval 1) • P by dsimp only [Q']; rw [smul_eq_C_mul]; ring,
      map_sub,map_smul,smul_eq_mul,sub_eq_zero] at e
    rw [e,mul_comm]
  let M := P-C (unitIntegral P)*rightRadau7
  have dm : M.natDegree≤7 := (natDegree_sub_le _ _).trans <|
    max_le dP ((natDegree_C_mul_le _ _).trans rightRadau7_degree_le)
  have mz : M=0 := by
    apply primitive_shift_detect M (k:=0) dm 1 one_ne_zero
    intro i
    simp only [zero_add]
    change unitIntegral (X^i.val*M)=0
    have ix : (X^i.val : K[X]).natDegree≤7 := by rw [natDegree_X_pow]; omega
    change unitIntegral (X^i.val*(P-C (unitIntegral P)*rightRadau7))=0
    have rr : (formalPrimitive ((X^i.val : K[X])*rightRadau7)).eval 1=(X^i.val : K[X]).eval 1 :=
      radauRight7_reproduces _ ix
    rw [mul_sub,map_sub,show X^i.val*(C (unitIntegral P)*rightRadau7) =
      (unitIntegral P) • ((X^i.val : K[X])*rightRadau7) by rw [smul_eq_C_mul]; ring,
      map_smul,smul_eq_mul,unitIntegral_apply (K:=K) ((X^i.val : K[X])*rightRadau7),
      rr,←every _ ix,mul_comm (X^i.val : K[X]) P,sub_self]
  have pEq : P=C (unitIntegral P)*rightRadau7 := sub_eq_zero.mp mz
  have ev := congrArg (eval 1) pEq
  rw [p1,eval_mul,eval_C] at ev
  have norm : unitIntegral P=((rightRadau7 : K[X]).eval 1)⁻¹ := by
    apply mul_right_cancel₀ rightRadau7_one_ne
    rw [inv_mul_cancel₀ rightRadau7_one_ne]
    exact ev.symm
  have pG : P=normalizedRightRadau7 := by rw [pEq,norm,normalizedRightRadau7]
  rwa [←pG]

/-- Multiplying the actual cardinal by 1-C produces a genuine paid relation
for the degree-eight Radau polynomial; not just a relation after deletion. -/
theorem order15_nonC2_radau_reduction (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) (h : Order15NonC2Head A b) :
    evalNodes A ((1-X)*(normalizedRightRadau7 : K[X]))∈
      chain (diag (nodes A)) (nonC2Ghosts A b) h.head 5 := by
  let v := terminalCardinal K 19-evalNodes A (normalizedRightRadau7 : K[X])
  have hv : v∈zeroSpace A 7 := order15_nonC2_terminal_profile ha ho hq
  have H := order15_nonC2_rank_chart ha ho hq
  let C' := diag (nodes A)
  have id : evalNodes A ((1-X)*(normalizedRightRadau7 : K[X]))=C' v-v := by
    ext i
    by_cases hi : i=Fin.last 19
    · subst i
      simp only [C',v,evalNodes_apply,eval_mul,eval_sub,eval_one,eval_X,diag_apply,Pi.sub_apply,
        H.terminal.node_one]
      ring
    · simp only [C',v,evalNodes_apply,eval_mul,eval_sub,eval_one,eval_X,diag_apply,Pi.sub_apply,
        terminalCardinal_apply_ne hi]
      ring
  have cc : chain C' (nonC2Ghosts A b) h.head 4 ⊔
      (chain C' (nonC2Ghosts A b) h.head 4).map C'=
      chain C' (nonC2Ghosts A b) h.head 5 := chain_sup_map h.core.2.1 (by decide)
  have base : zeroSpace A 7=chain C' (nonC2Ghosts A b) h.head 4 := h.band 2 (by decide)
  rw [id,←cc,←base]
  exact (zeroSpace A 7⊔(zeroSpace A 7).map C').sub_mem
    ((le_sup_right : (zeroSpace A 7).map C'≤_) (Submodule.mem_map_of_mem hv))
    ((le_sup_left : zeroSpace A 7≤_) hv)

end
end RKCert.Paired
