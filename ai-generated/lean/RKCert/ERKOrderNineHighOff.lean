module

public import RKCert.ERKOrderNineHighOffTerminal

@[expose] public section

/-! # Actual high-off contradiction at order nine

The first physical ordinary clean row and the exact two-endpoint moments
leave a fixed cubic or the free Jacobi quartic, according to the head
degree. No order on the tableau weights or node interval is assumed.
-/
namespace RKCert.Paired
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

theorem lobatto_cubic_ratio_two_thirds (h : K) (p : lobattoCubic.eval h=0)
    (q : lobattoCubic.eval (2*h/3)=0) : False := by
  simp [lobattoCubic] at p q
  have hp : 14*h^3-21*h^2+9*h-1=0 := by linear_combination 14*p
  have hq : 112*h^3-252*h^2+162*h-27=0 := by linear_combination 378*q
  have hz : (85:K)=0 := by
    linear_combination (3360*h^2-5544*h+1724)*hp+(-420*h^2+378*h-67)*hq
  exact (by norm_num : (85:K)≠0) hz

theorem lobatto_cubic_complement_primitive_ne_zero {h d a : K} {P : K[X]}
    (dp : P.natDegree=1) (hn : h≠0)
    (fac : lobattoCubic=(X-C h)*((X-C d)*(C a*P))) :
    (primitive (X*P)).eval h≠0 := by
  intro test
  obtain ⟨v,_,w,eP⟩ := natDegree_eq_one.mp dp
  have c0 : P.coeff 0=w := by rw [←eP]; simp
  have c1 : P.coeff 1=v := by rw [←eP]; simp
  have c2 : P.coeff 2=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [primitive_eval_X_quadratic P (by omega),c0,c1,c2] at test
  have hz : h^2*(3*w+2*v*h)=0 := by linear_combination 6*test
  have eq := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hn)
  have root : P.eval (2*h/3)=0 := by
    rw [←eP]
    simp only [eval_add,eval_mul,eval_X,eval_C]
    linear_combination eq/3
  exact lobatto_cubic_ratio_two_thirds h (by rw [fac]; simp)
    (by rw [fac]; simp [root])

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
/-- No actual order-nine twelve-stage tableau over an ordered field has
eight or more distinct quadratic-defect abscissas. -/
theorem order9_no_eight_or_more_off {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    (supportedNodes A (qdef A)).card<8 := by
  by_contra! N
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,dP,pn,_,hF,fit⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨n,m,pdeg,notOn⟩ := order9_high_off_head_form ha ho N hF P dP pn fit
  obtain ⟨hi,hc,hu⟩ := order9_high_off_terminal ha ho m n P dP fit notOn
  obtain ⟨h,d,hn,hd,hprim,htest⟩ := order9_high_off_two_root_tests ha ho m hF P dP pn fit hi hc hu
  let a := P.leadingCoeff
  let W := C a⁻¹*P
  let H := (X-C h)*((X-C d)*W)
  have na : a≠0 := leadingCoeff_ne_zero.mpr pn
  have wM : W.Monic := by
    change (C a⁻¹*P).leadingCoeff=1
    rw [leadingCoeff_mul,leadingCoeff_C]
    exact inv_mul_cancel₀ na
  have hM : H.Monic := (monic_X_sub_C _).mul ((monic_X_sub_C _).mul wM)
  have eD : H.natDegree=2+P.natDegree := by
    change ((X-C h)*((X-C d)*W)).natDegree=2+P.natDegree
    rw [natDegree_mul (X_sub_C_ne_zero _) ((monic_X_sub_C _).mul wM).ne_zero,
      natDegree_mul (X_sub_C_ne_zero _) wM.ne_zero,natDegree_X_sub_C,natDegree_X_sub_C]
    have eW : W.natDegree=P.natDegree := natDegree_C_mul (inv_ne_zero na)
    rw [eW]
    omega
  rcases pdeg with e|e
  · have d3 : H.natDegree=3 := by omega
    have c3 : H.coeff 3=1 := by rw [←d3]; exact hM.coeff_natDegree
    have f := beta_cubic_from_actual_probes ho (by decide) H d3.le htest
    have f' : H=lobattoCubic := by simpa [c3] using f
    exact lobatto_cubic_complement_primitive_ne_zero e hn f'.symm hprim
  · have d4 : H.natDegree=4 := by omega
    have c4 : H.coeff 4=1 := by rw [←d4]; exact hM.coeff_natDegree
    have f := beta_quartic_decoder H d4.le c4 (fun k =>
      beta_probe_coeff ho H d4.le (by have := k.isLt; omega) (htest k))
    exact lobattoPencil_complement_primitive_ne_zero dP hn hd f.symm hprim

end Ordered
end RKCert.Paired
