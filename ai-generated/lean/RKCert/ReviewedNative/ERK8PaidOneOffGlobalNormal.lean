module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffNormalScalars

@[expose] public section

/-! # Global one-off normal form for actual p8 and p9 tableaux -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open RKResearch Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

theorem four_feature_residuals (ha : ∀ i j, i ≤ j → A i j = 0)
    {a d e : K} {i j : Fin s} (D : ConstantAmplitude A a d i j)
    (cal : NormalCalibration A a d e) (r : Fin s)
    (pre : ∀ l, l < r → NormalFour a d e (twoHd a d) (normHe a d e)
      (nodes A l) (g A l) (h A l)) :
    normAPoly a d e (nodes A r) (g A r) (h A r)=0 ∧
    normQPoly a d e (nodes A r) (g A r) (h A r)=0 := by
  have an := D.origin.a_ne
  have hAct := normal_four_h ha r an D.dn cal.en cal.ed pre
  have cAct := normal_four_cubic ha r an pre
  have kr : k A r=normKap d e*((nodes A r-d)*h A r) := by
    simpa only [Pi.smul_apply,smul_eq_mul,deltaH_apply] using congrFun cal.k_eq r
  constructor
  · rw [←normal_a_scale a d e _ _ _ an D.dn cal.en cal.ed cal.dNorm]
    unfold rowM1 rowM2
    rw [←m1_relation A r,←m2_relation D.q2 r,←hAct,←kr,sub_self,mul_zero]
  · rw [←normal_q_scale a d e _ _ _ an cal.dNorm]
    unfold rowM1 rowM2 rowM3
    rw [←m1_relation A r,←m2_relation D.q2 r,←cAct,←deltaH_apply A d r,
      ←m3_relation cal.q_eq r,sub_self,mul_zero]

/-- Along the actual next independent Ag clock, the nonexceptional
alternatives would trap every row at only four distinct abscissas. -/
theorem normal_clock_doubles (ha : ∀ i j, i ≤ j → A i j = 0) (sep : PolySeparated A 4)
    {a d e : K} {i j : Fin s} (D : ConstantAmplitude A a d i j)
    (cal : NormalCalibration A a d e) : e=2*d := by
  by_contra ne
  have all (r : Fin s) : NormalFour a d e (twoHd a d) (normHe a d e)
      (nodes A r) (g A r) (h A r) := by
    refine wellFounded_lt.induction (C:=fun r=>NormalFour a d e (twoHd a d) (normHe a d e)
      (nodes A r) (g A r) (h A r)) r ?_
    intro r ih
    obtain ⟨ra,rq⟩ := four_feature_residuals ha D cal r ih
    by_cases g0 : g A r=0
    · rw [g0] at ra rq
      rcases normal_clean_clocks a d e _ _ D.origin.a_ne D.dn cal.dNorm ra rq with u|u|u
      · rw [u] at ra rq
        exact Or.inl (Or.inl ⟨u,g0,normal_clean_at_zero _ _ _ _ D.dn cal.en ra rq⟩)
      · rw [u] at ra rq
        exact Or.inl (Or.inr (Or.inr ⟨u,g0,normal_clean_at_d _ _ _ _ D.dn cal.dNorm ra rq⟩))
      · rw [u] at rq
        exact Or.inr ⟨u,g0,normal_clean_at_e _ _ _ _ D.dn cal.en ne rq⟩
    · have x := D.origin.off_support r g0
      have g := amplitude_value D.amplitude g0
      rw [x,g] at ra rq
      exact Or.inl (Or.inr (Or.inl ⟨x,g,normal_off_at_a _ _ _ _ D.dn cal.en cal.dNorm ne ra rq⟩))
  apply sep.knots_not_cover ({0,a,d,e}:Finset K)
  · exact (Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Finset.card_insert_le ..).trans
      (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp)))))
  · intro r
    rcases all r with (x|x|x)|x <;> simp [x.1]

/-- Full constant-amplitude global algebra, before separation of the
defects and before any numbered positions are imposed. -/
structure GlobalNormal (A : Matrix (Fin s) (Fin s) K) (a d : K) (i j : Fin s) : Prop where
  base : ConstantAmplitude A a d i j
  hk : k A=d • h A-diag (nodes A) (h A)
  q3 : mDef A 3=((a^2/2) • g A+((2*d^2-2*a^2)/a) • h A)-
    (d/a) • diag (nodes A) (h A)
  span_four : zeroSpace A 4=zeroSpace A 3⊔Submodule.span K {diag (nodes A) (h A)}

theorem global_normal_from_amplitude (ha : ∀ i j, i ≤ j → A i j = 0)
    (sep : PolySeparated A 4) (rank3 : finrank K (zeroSpace A 3)=2)
    (rank4 : finrank K (zeroSpace A 4)=3)
    {a d : K} {i j : Fin s} (D : ConstantAmplitude A a d i j) :
    GlobalNormal A a d i j := by
  obtain ⟨e,cal⟩ := normal_clock_calibration ha sep rank3 rank4 D
  have e' := normal_clock_doubles ha sep D cal
  subst e
  have ar : 3*d-2*(2*d)= -d := by eight_ring K
  have kappa : normKap d (2*d)= -1 := by
    unfold normKap
    rw [ar,div_neg,div_self D.dn]
  have nu : normNu a d (2*d)= -d/a := by
    unfold normNu
    rw [ar]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne,D.dn]
    eight_ring K
  have hm := h_in_grade_three A
  have cm := diag_zeroSpace A 3 hm
  have co : diag (nodes A) (h A)∉zeroSpace A 3 := by
    intro hc
    exact deltaH_small_rank_impossible ha sep rank3 rank4 D
      ((zeroSpace A 3).sub_mem hc ((zeroSpace A 3).smul_mem _ hm))
  refine ⟨D,?_,?_,extra_rank_three_span rank3 rank4 cm co⟩
  · rw [cal.k_eq,kappa,deltaH]
    ext r
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    eight_ring K
  · rw [cal.q_eq,nu,deltaH]
    ext r
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,twoMu]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,D.origin.a_ne]
    eight_ring K


end RKResearch.Certified.Graded.OneOff.PaidProof
