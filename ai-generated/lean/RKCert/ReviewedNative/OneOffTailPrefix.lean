module

public import RKCert.ReviewedNative.OneOffTailCurve

@[expose] public section

/-! # The genuine next two distinct on-clock rows, with no later-stage assumptions -/
namespace RKResearch.Certified.Graded.OneOff.Seven
open RKResearch Polynomial Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

noncomputable def jSourcePoly (d z : K) : K[X] :=
  C ((z-d)/(4*d))*X^3+C (-(d*(3*z-2*d))/(4*d))*X^2+C ((2*d^2*z)/(4*d))*X

theorem jSource_poly_eval (d z x : K) : (jSourcePoly d z).eval x=jSource d z x := by
  simp only [jSourcePoly,jSource,eval_add,eval_mul,eval_pow,eval_X,eval_C]
  ring

omit [CharZero K] in
theorem jSource_poly_degree (d z : K) : (jSourcePoly d z).natDegree≤3 := by
  unfold jSourcePoly
  apply natDegree_add_le_of_le (m:=3) (n:=3)
  · apply natDegree_add_le_of_le (m:=3) (n:=3)
    · exact natDegree_C_mul_X_pow_le _ _
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by decide)
  · rw [←pow_one (X:K[X])]
    exact (natDegree_C_mul_X_pow_le _ _).trans (by decide)

noncomputable def newFibreTest (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) : Fin 12 → K :=
  (diag (nodes A) (scaledH A a)-(2*d) • scaledH A a)-evalNodes A (jSourcePoly d z)+
    (jSource d z a/baseAmp a) • g A

theorem newFibreTest_eval (a d z : K) (r : Fin 12) :
    newFibreTest A a d z r=(nodes A r-2*d)*scaledH A a r-jSource d z (nodes A r)+
      (jSource d z a/baseAmp a)*g A r := by
  simp only [newFibreTest,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,
    evalNodes_apply,jSource_poly_eval]
  ring

theorem newFibreTest_mem (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) :
    newFibreTest A a d z∈treeSpace A 4 := by
  have H : scaledH A a∈zeroSpace A 3 := (zeroSpace A 3).smul_mem _ (h_in_grade_three A)
  have HD := zeroSpace_le_treeSpace A 4 (diag_zeroSpace A 3 H)
  have HS := zeroSpace_le_treeSpace A 4 (zeroSpace_mono A (by decide : 3≤4) H)
  have gd := treeSpace_mono A (by decide : 2≤4) (zeroSpace_le_treeSpace A 2 (mDef_mem A 1))
  exact (treeSpace A 4).add_mem
    ((treeSpace A 4).sub_mem ((treeSpace A 4).sub_mem HD ((treeSpace A 4).smul_mem _ HS))
      (evalNodes_mem_treeSpace A _ ((jSource_poly_degree d z).trans (by decide))))
    ((treeSpace A 4).smul_mem _ gd)

theorem order9_first_seven_independent (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12))) :
    IndependentBefore (treeSpace A 4) (7:Fin 12) := by
  let z := nodes A (5:Fin 12)
  let T := newFibreTest A a d z
  have sixth := order9_sixth_feature ha ho D F
  have C4 := order9_clean_four ha ho D F
  have old (l : Fin 12) (lt : l < (6:Fin 12)) : T l=0 := by
    change newFibreTest A a d z l=0
    rw [newFibreTest_eval]
    have e := (source_interpolation D.base.origin.a_ne D.base.dn
      (order9_native_sources ha ho D F l lt)).1
    linear_combination e
  have ve : T (6:Fin 12)=(z-2*d)*(scaledH A a (6:Fin 12)-scaledH A a (5:Fin 12)) := by
    have e := old (5:Fin 12) (by decide)
    change newFibreTest A a d z (5:Fin 12)=0 at e
    rw [newFibreTest_eval,C4.node5,C4.g5,mul_zero,add_zero] at e
    change newFibreTest A a d z (6:Fin 12)=_
    rw [newFibreTest_eval,D7.node7,D7.g7,mul_zero,add_zero]
    linear_combination e
  have vn : T (6:Fin 12)≠0 := by
    rw [ve]
    exact mul_ne_zero (sub_ne_zero.mpr sixth.2.2.2.1) (sub_ne_zero.mpr D7.Hdiff)
  exact extend_independent_before (j:=(6:Fin 12)) (r:=(7:Fin 12)) rfl
    sixth.2.2.2.2.2 (newFibreTest_mem A a d z) old vn

omit [CharZero K] in
theorem tailPoly_eval (d t z x : K) :
    (tailPolynomial d t z).eval x=x*(x-d)*(x-t)*(x-z) := by
  simp only [tailPolynomial,fibrePoly,eval_mul,eval_sub,eval_X,eval_C]
  ring

noncomputable def physicalTail (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) : Fin 12 → K :=
  evalNodes A (tailPolynomial d (2*d) z)-
    ((tailPolynomial d (2*d) z).eval a/baseAmp a) • g A

omit [CharZero K] in
theorem physicalTail_defect (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) :
    physicalTail A a d z-evalNodes A (tailPolynomial d (2*d) z)∈zeroSpace A 4 := by
  have e : physicalTail A a d z-evalNodes A (tailPolynomial d (2*d) z)=
      -(((tailPolynomial d (2*d) z).eval a/baseAmp a) • g A) := by
    unfold physicalTail
    abel
  rw [e]
  exact (zeroSpace A 4).neg_mem ((zeroSpace A 4).smul_mem _
    (zeroSpace_mono A (by decide : 2≤4) (mDef_mem A 1)))

omit [CharZero K] in
theorem physicalTail_mem (A : Matrix (Fin 12) (Fin 12) K) (a d z : K) : physicalTail A a d z∈treeSpace A 4 := by
  simpa only [sub_add_cancel] using (treeSpace A 4).add_mem
    (zeroSpace_le_treeSpace A 4 (physicalTail_defect A a d z))
    (evalNodes_mem_treeSpace A _ (tailPolynomial_degree d (2*d) z).le)

omit [CharZero K] in
theorem physicalTail_on (a d z : K) {r : Fin 12} (gr : g A r=0) :
    physicalTail A a d z r=(tailPolynomial d (2*d) z).eval (nodes A r) := by
  simp only [physicalTail,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,gr,mul_zero,sub_zero]

theorem physicalTail_off {a d z : K} {i j r : Fin 12} (D : GlobalNormal A a d i j)
    (gr : g A r≠0) : physicalTail A a d z r=0 := by
  have den : baseAmp a≠0 :=
    div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 D.base.origin.a_ne)) (by norm_num)
  simp only [physicalTail,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,
    D.base.origin.off_support r gr,amplitude_value D.base.amplitude gr,div_mul_cancel₀ _ den,sub_self]

theorem order9_tail_initial_zero (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12))) (l : Fin 12) (lt : l < (7:Fin 12)) :
    physicalTail A a d (nodes A (5:Fin 12)) l=0 := by
  let z := nodes A (5:Fin 12)
  change physicalTail A a d z l=0
  have ln : l.val<7 := lt
  by_cases hh : l.val<6
  · rcases order9_native_sources ha ho D F l hh with h|h|h|h|h
    · rw [physicalTail_on a d z h.2.1,tailPoly_eval,h.1]
      ring
    · apply physicalTail_off D
      rw [h.2.1]
      exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 D.base.origin.a_ne)) (by norm_num)
    · rw [physicalTail_on a d z h.2.1,tailPoly_eval,h.1]
      ring
    · rw [physicalTail_on a d z h.2,tailPoly_eval,h.1]
      ring
    · rw [physicalTail_on a d z h.2.1,tailPoly_eval,h.1]
      change z*(z-d)*(z-2*d)*(z-z)=0
      ring
  · have h : l=(6:Fin 12) := Fin.ext (by omega)
    subst l
    rw [physicalTail_on a d z D7.g7,tailPoly_eval,D7.node7]
    change z*(z-d)*(z-2*d)*(z-z)=0
    ring

end RKResearch.Certified.Graded.OneOff.Seven
