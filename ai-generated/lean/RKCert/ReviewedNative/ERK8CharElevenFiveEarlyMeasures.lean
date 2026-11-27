module
public import RKCert.ReviewedNative.ERK8CharElevenFiveEarlyNewton
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Paid quotient measurements for the first three or four off rows. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem earlyBary_quotient_coeff
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {m : ℕ} (m4 : m≤4) (P Q : K[X]) (Qd : Q.natDegree < m)
    (eval : ∀ x∈earlyNodes A m, P.eval x=(exceptionalQuadratic : K[X]).eval x*Q.eval x) :
    earlyBary A m P=Q.coeff (m-1) := by
  have c := earlyNodes_card five cleanFive H m4
  have e := coeff_last_barycentric (earlyNodes A m) Q (c.symm ▸ Qd)
  rw [c] at e
  rw [e]
  unfold earlyBary
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hic⟩ := Finset.mem_image.mp hx
  have qn : (exceptionalQuadratic : K[X]).eval x≠0 :=
    hic ▸ exceptional_quadratic_ne_off T (earlyRows_off H m4 hi)
  rw [eval x hx,mul_comm ((exceptionalQuadratic : K[X]).eval x),mul_div_cancel_right₀ _ qn]
  rfl

theorem earlyBary_qmul
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {m : ℕ} (m4 : m≤4) (Q : K[X]) (Qd : Q.natDegree < m) :
    earlyBary A m ((exceptionalQuadratic : K[X])*Q)=Q.coeff (m-1) :=
  earlyBary_quotient_coeff five cleanFive T H m4 _ Q Qd (fun _ _ => eval_mul)

theorem earlyBary_q_recurrences
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {m : ℕ} (ml : 3≤m) (mh : m≤4) :
    earlyBary A m (X^2)-earlyBary A m X+8*earlyBary A m 1=0 ∧
      earlyBary A m (X^3)-earlyBary A m (X^2)+8*earlyBary A m X=0 := by
  have one : (1:K[X]).natDegree < m := by simp; omega
  have Xn : (X:K[X]).natDegree < m := by simp; omega
  have z0 := earlyBary_qmul five cleanFive T H mh 1 one
  have z1 := earlyBary_qmul five cleanFive T H mh X Xn
  have m2 : 1 < m-1 := by omega
  rw [mul_one,coeff_eq_zero_of_natDegree_lt (by simpa using (show 0<m-1 by omega :
    0<m-1))] at z0
  rw [coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_X] using m2)] at z1
  have form : ((exceptionalQuadratic : K[X])*X)=X^3-X^2+C 8*X := by
    simp only [exceptionalQuadratic]
    ring
  rw [exceptionalQuadratic,earlyBary_add,earlyBary_sub,earlyBary_C] at z0
  rw [form,earlyBary_add,earlyBary_sub,earlyBary_Cmul] at z1
  exact ⟨z0,z1⟩

/-- A low remainder of the literal early hull yields two row-measure
identities, the second with a unit leading coefficient. -/
theorem earlyBary_hull_receipt
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5)
    {m : ℕ} (m3 : 3≤m) (m4 : m≤4) {beta a c : K} (bn : beta≠0) {U : K[X]}
    (shape : nodalHull (earlyNodes A m)=C beta*(C a+C c*X)+exceptionalQuadratic*U) :
    a*earlyBary A m 1+c*earlyBary A m X=0 ∧
      beta*(a*earlyBary A m X+c*earlyBary A m (X^2))+1=0 := by
  let F := nodalHull (earlyNodes A m)
  let V : K[X] := C beta*(C a+C c*X)
  let q : K[X] := exceptionalQuadratic
  have fd : F.natDegree=m := (natDegree_nodalHull _).trans (earlyNodes_card five cleanFive H m4)
  have fc : F.coeff m=1 := by
    have r : F.coeff F.natDegree=1 := (monic_nodalHull _).coeff_natDegree
    rwa [fd] at r
  have vd : V.natDegree≤1 := (natDegree_C_mul_le _ _).trans (affine_degree_le _ _)
  change F=V+q*U at shape
  have ud : U.natDegree≤m-2 := by
    by_cases u : U=0
    · simp [u]
    have d : (q*U).natDegree≤m := by
      have exactD : q*U=F-V := by linear_combination -shape
      rw [exactD]
      have vdm : V.natDegree≤m := vd.trans (by omega)
      rw [show m=max m m by simp]
      exact natDegree_sub_le_of_le fd.le vdm
    have qne : q≠0 := by intro e; have D := quadratic_exact_degree (K:=K); simp [←show q=exceptionalQuadratic from rfl,e] at D
    rw [natDegree_mul qne u,show q.natDegree=2 from quadratic_exact_degree] at d
    omega
  have uc : U.coeff (m-2)=1 := by
    have eq := congrArg (fun P : K[X] => P.coeff m) shape
    have top : (q*U).coeff m=q.coeff 2*U.coeff (m-2) := by
      convert (coeff_mul_add_eq_of_natDegree_le (show q.natDegree≤2 from exceptionalQuadratic_degree) ud) using 2; omega
    have q2 : q.coeff 2=1 := by simp [q,exceptionalQuadratic,coeff_X,coeff_X_pow]
    rw [fc,coeff_add,coeff_eq_zero_of_natDegree_lt (vd.trans_lt (by omega)),top,q2,one_mul,zero_add] at eq
    exact eq.symm
  have z0 : earlyBary A m F=0 := earlyBary_of_zero A m F (fun _ hx => nodalHull_eval_of_mem hx)
  have z1 : earlyBary A m (X*F)=0 := by
    apply earlyBary_of_zero
    intro x hx
    rw [eval_mul,show F.eval x=0 from nodalHull_eval_of_mem hx,mul_zero]
  have u0 := earlyBary_qmul five cleanFive T H m4 U (by omega)
  rw [coeff_eq_zero_of_natDegree_lt (ud.trans_lt (by omega))] at u0
  have xud : (X*U).natDegree < m := by
    have z := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) ud
    omega
  have u1 := earlyBary_qmul five cleanFive T H m4 (X*U) xud
  rw [show m-1=(m-2)+1 by omega,coeff_X_mul,uc] at u1
  have first : beta*(a*earlyBary A m 1+c*earlyBary A m X)=0 := by
    rw [shape,earlyBary_add,u0,add_zero] at z0
    simpa only [V,earlyBary_add,earlyBary_Cmul,earlyBary_C] using z0
  have Xform : X*F=C beta*(C a*X+C c*X^2)+q*(X*U) := by rw [shape]; dsimp only [V]; ring
  rw [Xform,earlyBary_add,u1] at z1
  simp only [earlyBary_add,earlyBary_Cmul] at z1
  exact ⟨(mul_eq_zero.mp first).resolve_left bn,z1⟩

/-- Four off rows before the center force their monic hull to have the
same nonzero linear remainder as the primitive of Xq. -/
theorem early_four_hull_of_center_five
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (T : ExceptionalHead A theta) (H : CenterPrefix A 5) :
    ∃ beta : K, beta≠0 ∧ ∃ U : K[X],
      nodalHull (earlyNodes A 4)=C beta*(C 3+C 9*X)+exceptionalQuadratic*U := by
  obtain ⟨R,Rd,fit⟩ := high_precenter_xq_profile ha ho T H
  let q : K[X] := exceptionalQuadratic
  let W := primitive (X*q)-q*R
  let F := nodalHull (earlyNodes A 4)
  have wn : W≠0 := q_times_linear_nf_nonzero ho p R
  have pd : (primitive (X*q)).natDegree≤4 :=
    primitive_natDegree_le (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp)
      exceptionalQuadratic_degree)
  have wd : W.natDegree≤4 :=
    natDegree_sub_le_of_le pd (natDegree_mul_le_of_le exceptionalQuadratic_degree Rd)
  have f : ∀ x∈earlyNodes A 4, W.eval x=0 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have lt : i<5 := by
      have ub := (mem_earlyRows.mp hi).2
      exact Nat.lt_succ_of_le ub
    simp [W,q,fit i lt (earlyRows_off H (by decide) hi)]
  obtain ⟨gamma,e⟩ := polynomial_hull_of_test_zeros _ W (by
    rw [earlyNodes_card five cleanFive H (by decide)]; exact wd) f
  change W=C gamma*F at e
  have gn : gamma≠0 := fun g => wn (by simp [e,g])
  have c : (C gamma⁻¹*C gamma : K[X])=1 := by rw [←map_mul,inv_mul_cancel₀ gn,map_one]
  refine ⟨gamma⁻¹,inv_ne_zero gn,C gamma⁻¹*(C 3*X^2-X+1-R),?_⟩
  change F=_
  have h : F=C gamma⁻¹*W := by rw [e,←mul_assoc,c,one_mul]
  rw [h]
  dsimp only [W,q]
  rw [primitive_xq_remainder ho p]
  ring

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.earlyBary_hull_receipt
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.early_four_hull_of_center_five
