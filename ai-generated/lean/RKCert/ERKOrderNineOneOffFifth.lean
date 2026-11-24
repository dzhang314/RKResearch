module

public import RKCert.ERKOneOffFirstFour
public import RKCert.ERKOrderNineOneOffDefectSeparation

@[expose] public section

/-! # A fifth real row at the doubled clock
The new row has the same clock as its predecessor, but a different
value of the cubic defect. Strictness limits all tests to the first four
literal input columns; no support-size compression is assumed. -/
namespace RKCert.Paired.OneOff
open Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Fin s→Fin s→K}

theorem four_feature_residuals (ha : StrictLower A)
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

theorem normHe_doubled (a d : K) (dn : d≠0) : normHe a d (2*d)=a*d^2 := by
  unfold normHe
  field_simp [dn]
  ring

theorem four_chart_features {a d : K} {l : Fin 4} (dn : d≠0) :
    NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d))
      (chartNode a d l) (chartDefect a l) (chartH a d l) := by
  rw [normHe_doubled a d dn]
  fin_cases l <;> simp [NormalFour,ThreeFeatures,chartNode,chartDefect,chartH]

theorem firstChartBefore_four {a d : K} {r : Fin s} (size : 4≤s)
    (r4 : r.val=4) (F : FirstFour A a d size) : FirstChartBefore A a d r := by
  intro u ur
  have lt : u.val < 4 := r4 ▸ ur
  let l : Fin 4 := ⟨u.val,lt⟩
  have eq : Fin.castLE size l=u := Fin.ext rfl
  have f := F.features l
  rw [eq] at f
  exact ⟨l,rfl,f.1,f.2.1⟩

theorem order9_fifth_feature {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j)
    (F : FirstFour A a d (by decide)) :
    nodes A (4:Fin 12)=2*d ∧ g A (4:Fin 12)=0 ∧ h A (4:Fin 12)≠a*d^2 := by
  let e : Fin 4→Fin 12 := Fin.castLE (by decide)
  let r : Fin 12 := 4
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C : FirstChartBefore A a d r := firstChartBefore_four (by decide) rfl F
  have no_dup : ∀ l : Fin 4,
      nodes A (e l)=nodes A r → g A (e l)=g A r → h A (e l)=h A r → False := by
    intro l cn cg ch
    have lt : e l < r := l.isLt
    exact no_repeat_in_first_chart_at_floor (s:=11) ha ho (by decide)
      an dn D.base.q2 lt C cn cg ch
  have p : ∀ l, l < r → NormalFour a d (2*d) (twoHd a d) (normHe a d (2*d))
      (nodes A l) (g A l) (h A l) := by
    intro l lr
    obtain ⟨u,eq,cu,gu⟩ := C l lr
    have eu : e u=l := Fin.ext eq
    have fu := F.features u
    change nodes A (e u)=_ ∧ g A (e u)=_ ∧ h A (e u)=_ at fu
    rw [eu] at fu
    rw [cu,gu,fu.2.2]
    exact four_chart_features dn
  have sep : Separated A 4 := explicit_separated ha ho (by decide) (by decide)
  obtain ⟨_,h3,h4,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨x,cal⟩ := normal_clock_calibration ha sep h3 h4 D.base
  have xx := normal_clock_doubles ha sep D.base cal
  subst x
  obtain ⟨ra,rq⟩ := four_feature_residuals ha D.base cal r p
  have f0 : nodes A (e 0)=0 ∧ g A (e 0)=0 ∧ h A (e 0)=0 := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 0
  have f1 : nodes A (e 1)=a ∧ g A (e 1)=baseAmp a ∧ h A (e 1)=0 := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 1
  have f2 : nodes A (e 2)=d ∧ g A (e 2)=0 ∧ h A (e 2)=twoHd a d := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 2
  have f3 : nodes A (e 3)=2*d ∧ g A (e 3)=0 ∧ h A (e 3)=a*d^2 := by
    simpa [e,chartNode,chartDefect,chartH] using F.features 3
  have gr : g A r=0 := by
    by_contra off
    have Prod := congrFun (order9_defects_separate ha ho oneOff D) r
    change g A r*h A r=0 at Prod
    have hr := (mul_eq_zero.mp Prod).resolve_left off
    exact no_dup 1 (f1.1.trans (D.base.origin.off_support r off).symm)
      (f1.2.1.trans (amplitude_value D.base.amplitude off).symm)
      (f1.2.2.trans hr.symm)
  rw [gr] at ra rq
  rcases normal_clean_clocks a d (2*d) _ _ an dn cal.dNorm ra rq with c0|c2|c3
  · rw [c0] at ra rq
    exact (no_dup 0 (f0.1.trans c0.symm) (f0.2.1.trans gr.symm)
      (f0.2.2.trans (normal_clean_at_zero _ _ _ _ dn cal.en ra rq).symm)).elim
  · rw [c2] at ra rq
    exact (no_dup 2 (f2.1.trans c2.symm) (f2.2.1.trans gr.symm)
      (f2.2.2.trans (normal_clean_at_d _ _ _ _ dn cal.dNorm ra rq).symm)).elim
  · exact ⟨c3,gr,fun same=>no_dup 3 (f3.1.trans c3.symm) (f3.2.1.trans gr.symm)
      (f3.2.2.trans same.symm)⟩

end RKCert.Paired.OneOff
