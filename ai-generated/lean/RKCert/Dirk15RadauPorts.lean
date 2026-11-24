module

public import RKCert.Dirk15RankChart
public import RKCert.DirkPolynomialMarked

@[expose] public section

/-! # The true reverse Radau port at order fifteen
The fixed reproducing polynomial is checked by eight rational moment
identities, algebraically over any characteristic-zero field. The support
condition in the port theorem is explicitly separate. -/
namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

def radauLeft7_coeff : Fin 8 → K := ![64, -2016, 20160, -92400, 221760, -288288, 192192, -51480]

def radauLeft7 : K[X] := ofFn 8 radauLeft7_coeff

omit [CharZero K] in
theorem radauLeft7_degree_le : (radauLeft7 : K[X]).natDegree≤7 := by
  have h := ofFn_natDegree_lt (by decide : 0<8) (radauLeft7_coeff (K:=K))
  change (radauLeft7 : K[X]).natDegree<8 at h
  omega

theorem radauLeft7_power (k : Fin 8) :
    (formalPrimitive (X^k.val*(radauLeft7 : K[X]))).eval 1 =
      if k.val=0 then 1 else 0 := by
  rw [primitive_eval_power_mul _ _ _ (radauLeft7_degree_le (K:=K))]
  simp only [one_pow,mul_one]
  have hc (j : Fin 8) : (radauLeft7 : K[X]).coeff j.val = radauLeft7_coeff j :=
    ofFn_coeff_eq_val_of_lt radauLeft7_coeff j.isLt
  simp only [hc]
  fin_cases k <;> norm_num [radauLeft7_coeff,Fin.sum_univ_succ]

theorem radauLeft7_reproduces (Q : K[X]) (hd : Q.natDegree≤7) :
    (formalPrimitive (Q*radauLeft7)).eval 1=Q.eval 0 := by
  let L := (leval (1:K)).comp (formalPrimitiveLinear.comp (LinearMap.mulLeft K (radauLeft7 : K[X])))
  have h0 : L Q=(formalPrimitive (Q*radauLeft7)).eval 1 := by
    change (formalPrimitive (radauLeft7*Q)).eval 1=_
    rw [mul_comm]
  rw [←h0]
  let M := leval (0:K)
  change L Q=M Q
  conv_lhs => rw [Q.as_sum_range]
  conv_rhs => rw [Q.as_sum_range]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j<8 := by have := Finset.mem_range.mp hj; omega
  have he : monomial j (Q.coeff j)=Q.coeff j • (X^j:K[X]) := by
    rw [smul_eq_C_mul,C_mul_X_pow_eq_monomial]
  rw [he,map_smul,map_smul]
  congr 1
  change (formalPrimitive (radauLeft7*X^j)).eval 1=(X^j : K[X]).eval 0
  rw [eval_pow,eval_X]
  rw [mul_comm]
  have h := radauLeft7_power (K:=K) (⟨j,hj'⟩ : Fin 8)
  change (formalPrimitive (X^j*radauLeft7)).eval 1 = if j=0 then 1 else 0 at h
  rw [h]
  split <;> simp_all

omit [CharZero K] in
theorem reflectPolynomial_involutive (P : K[X]) :
    reflectPolynomial (reflectPolynomial P)=P := by
  unfold reflectPolynomial
  rw [comp_assoc]
  have h : (1-X : K[X]).comp (1-X)=X := by simp
  rw [h,comp_X]

theorem radauRight7_reproduces (Q : K[X]) (hd : Q.natDegree≤7) :
    (formalPrimitive (Q*reflectPolynomial (radauLeft7 : K[X]))).eval 1=Q.eval 1 := by
  have h := reflectPolynomial_integral (Q*reflectPolynomial (radauLeft7 : K[X]))
  have he : reflectPolynomial (Q*reflectPolynomial (radauLeft7 : K[X])) =
      reflectPolynomial Q*radauLeft7 := by
    change (Q*reflectPolynomial (radauLeft7 : K[X])).comp (1-X)=_
    rw [mul_comp]
    change reflectPolynomial Q * reflectPolynomial (reflectPolynomial (radauLeft7 : K[X]))=_
    rw [reflectPolynomial_involutive]
  rw [←h,he,radauLeft7_reproduces _ ((reflectPolynomial_degree Q).trans hd)]
  simp [reflectPolynomial,eval_comp]

/-- The literal final-coordinate Dirac minus the reproducing row belongs
to the ACTUAL full marked space at grade seven of a non-C(2) extremizer. -/
theorem nonC2_radau_residual (ho : HasTreeOrderAtLeast A b 15) (h : Order15NonC2Chart A b) :
    terminalCardinal K 19-weightedEval (mirror A) b (radauLeft7 : K[X])∈marked A 15 7 := by
  apply mem_annih.mpr
  intro v hv
  change v∈treeSpace A 7 at hv
  obtain ⟨P,hP,hPV⟩ := exists_poly_zeroSpace_charZero A hv
  have hvtrace : OrdinaryTrace A 7 v P := ⟨hP,hPV⟩
  have terminal := h.terminal_pure_zero _ hPV
  change v (Fin.last 19) - P.eval (nodes A (Fin.last 19))=0 at terminal
  have hv1 : v (Fin.last 19)=P.eval 1 := by
    simpa only [h.terminal.node_one,sub_eq_zero] using terminal
  have he : row (weightedEval (mirror A) b (radauLeft7 : K[X])) v = P.eval 1 := by
    rw [weightedEval_reflect,hvtrace.pair_polynomial ho _ (by
      have hh := (reflectPolynomial_degree (radauLeft7 : K[X])).trans (radauLeft7_degree_le (K:=K))
      omega),radauRight7_reproduces P hP]
  change rowL (terminalCardinal K 19-weightedEval (mirror A) b (radauLeft7 : K[X])) v=0
  rw [map_sub,LinearMap.sub_apply,rowL_apply,rowL_apply,row_single_left,hv1,he,sub_self]

/-- An active tau-clean physical row must be a fixed Radau port provided
every actually paid reverse row vanishes on that tau-clean coordinate.
This is not a claim about tau-dirty or zero-weight stages. -/
theorem nonC2_radau_port (ho : HasTreeOrderAtLeast A b 15) (h : Order15NonC2Chart A b)
    (i : Fin 20) (hi : b i≠0) (clean : ∀ w∈marked A 15 7,w i=0) :
    mirror A i=0 ∨ (radauLeft7 : K[X]).eval (mirror A i)=0 := by
  by_cases e : i=Fin.last 19
  · exact Or.inl (e ▸ terminal_mirror_zero h.terminal)
  right
  have hz := clean _ (nonC2_radau_residual ho h)
  have hcard : terminalCardinal K 19 i=0 := terminalCardinal_apply_ne e
  simp only [Pi.sub_apply,hcard,weightedEval_apply,zero_sub,neg_eq_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_right hi

end
end RKCert.Paired
