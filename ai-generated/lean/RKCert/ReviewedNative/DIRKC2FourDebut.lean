module

public import RKCert.ReviewedNative.DIRKC2BarycentricPort
public import RKCert.ReviewedNative.DIRKCubicChronology

@[expose] public section

/-! # Close the later C(2) head, hence the full C(2) ordinary F6 surplus -/
namespace RKResearch.Certified.Graded.OuterHead

open Polynomial RKCert.OneEscape RKCert.Endpoint RKCert.FourDebut Module
open scoped Classical Matrix
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b w : Fin s → K}
variable {U : Submodule K (Fin s → K)}

/-- A grade-four exterior head cannot pass the four physical debut
cuts after a single-clock cubic core. The final scalar algebra is frozen;
all its inputs are derived here from the reviewed tableau flags. -/
theorem no_grade_four_exterior_head (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 8≤p)
    (C : CoreMask A U) (inside : U≤zeroSpace A 3)
    (D : ClockDebuts A C.mask 4)
    (f4 : zeroSpace A 4=chain (diag (nodes A)) U w 1)
    (f5 : zeroSpace A 5=chain (diag (nodes A)) U w 2)
    (f6 : zeroSpace A 6=chain (diag (nodes A)) U w 3) : False := by
  classical
  let z := nodes A ∘ D.row
  let h := w ∘ D.row
  let T0 : ExteriorStep C 0 := D.step (0:Fin 4)
  let T1 : ExteriorStep C 1 := D.step (1:Fin 4)
  let T2 : ExteriorStep C 2 := D.step (2:Fin 4)
  let T3 : ExteriorStep C 3 := D.step (3:Fin 4)
  have nz0 : h 0≠0 := early_exterior_head ha ho (by omega) inside T0 (by decide) f5.le f6.le
  have nz1 : h 1≠0 := early_exterior_head ha ho (by omega) inside T1 (by decide) f5.le f6.le
  have nz2 : h 2≠0 := early_exterior_head ha ho (by omega) inside T2 (by decide) f5.le f6.le
  have dirty2 (i : Fin 2) : w (T2.old i)≠0 := by fin_cases i <;> first | exact nz0 | exact nz1
  have dirty3 (i : Fin 3) : w (T3.old i)≠0 := by fin_cases i <;> first | exact nz0 | exact nz1 | exact nz2
  have i4 := inside.trans (zeroSpace_mono A (by decide : 3≤4))
  have i5 := inside.trans (zeroSpace_mono A (by decide : 3≤5))
  have a2 := exterior_refund ha ho T2 (by omega) inside f5.le dirty2
  have a3 := exterior_refund ha ho T3 (by omega) i4 f6.le dirty3
  obtain ⟨P2,Q2,np2,dp2,p20,dq2,m2,j2,roots2⟩ := T2.paired_cut ha i4 f4.ge f5.le a2 dirty2
  obtain ⟨P3,Q3,np3,dp3,p30,dq3,m3,j3,roots3⟩ := T3.paired_cut ha i5 f5.ge f6.le a3 dirty3
  have cut2 := barycentric_native (nodes A ∘ T2.old) (w ∘ T2.old) (nodes A T2.next)
    T2.distinct T2.fresh T2.next_nz T2.old_nz dirty2 np2 dp2 p20 dq2 m2 j2 roots2
  have cut3 := barycentric_native (nodes A ∘ T3.old) (w ∘ T3.old) (nodes A T3.next)
    T3.distinct T3.fresh T3.next_nz T3.old_nz dirty3 np3 dp3 p30 dq3 m3 j3 roots3
  have c2 : (z 0^2/h 0)*(z 0-z 2)+(z 1^2/h 1)*(z 1-z 2)=0 := by
    rw [Fin.sum_univ_two] at cut2
    exact cut2
  have c3 : (z 0^2/h 0)*(z 0-z 3)+(z 1^2/h 1)*(z 1-z 3)+(z 2^2/h 2)*(z 2-z 3)=0 := by
    rw [Fin.sum_univ_three] at cut3
    exact cut3
  have hull2 : T2.hull=nodes2 (z 0) (z 1) := by
    rw [ExteriorStep.hull,Lagrange.nodal_eq,Fin.prod_univ_two]
    rfl
  have hull3 : T3.hull=nodes3 (z 0) (z 1) (z 2) := by
    rw [ExteriorStep.hull,Lagrange.nodal_eq,Fin.prod_univ_three]
    rfl
  have degree2 : (X*T2.hull).natDegree≤3 := natDegree_mul_le.trans (by rw [natDegree_X,T2.hull_degree])
  have degree3 : (X*T3.hull).natDegree≤4 := natDegree_mul_le.trans (by rw [natDegree_X,T3.hull_degree])
  have degree5 : (X^2*T3.hull).natDegree≤5 := natDegree_mul_le.trans (by rw [natDegree_X_pow,T3.hull_degree])
  obtain ⟨L0,d0,l0⟩ := T2.masked_primitive ha inside f4.le a2 degree2
    (by simp) (fun i=>by simp [T2.hull_old i])
  obtain ⟨L1,d1,l1⟩ := T3.masked_primitive ha i4 f5.le a3 degree3
    (by simp) (fun i=>by simp [T3.hull_old i])
  obtain ⟨L2,d2,l2⟩ := T3.masked_primitive ha i5 f6.le a3 degree5
    (by simp) (fun i=>by simp [T3.hull_old i])
  have cal0 (i : Fin 4) (hi : i ≤ 2) :
      z i^2*RKCert.FourDebut.L2 (z 0) (z 1) (z i)=h i*L0.coeff 0 := by
    have eq := l0 (D.row i) (D.inc.monotone hi) (D.outside i)
    rw [hull2,J_nodes2,weightedEval_apply,eval_const_head d0,mul_comm (L0.coeff 0)] at eq
    exact eq
  have cal (i : Fin 4) :
      B1 (z 0) (z 1) (z 2) (z i)=h i*(L1.coeff 1*z i+L1.coeff 0) ∧
      B2 (z 0) (z 1) (z 2) (z i)=h i*(L2.coeff 2*(z i)^2+L2.coeff 1*z i+L2.coeff 0) := by
    have e1 := l1 (D.row i) (D.inc.monotone (Fin.le_last i)) (D.outside i)
    have e2 := l2 (D.row i) (D.inc.monotone (Fin.le_last i)) (D.outside i)
    rw [hull3,J_nodes3,weightedEval_apply,eval_linear_head d1] at e1
    rw [hull3,J2_nodes3,weightedEval_apply,eval_quadratic_head d2] at e2
    exact ⟨e1.trans (mul_comm _ _),e2.trans (mul_comm _ _)⟩
  have apart (i j : Fin 4) (ne : i≠j) : z i≠z j := D.clock_inj.ne ne
  apply fourth_impossible (a:=z 0) (b:=z 1) (u:=z 2) (v:=z 3) (wv:=h 3)
    (l₁:=L1.coeff 1) (l₀:=L1.coeff 0) (q₂:=L2.coeff 2) (q₁:=L2.coeff 1) (q₀:=L2.coeff 0)
    (D.nonzero 0) (D.nonzero 1) (D.nonzero 2) (D.nonzero 3)
    (apart 0 1 (by decide)) (apart 0 2 (by decide)) (apart 1 2 (by decide))
    (apart 0 3 (by decide)) (apart 1 3 (by decide)) (apart 2 3 (by decide))
    nz0 nz1 nz2 c2 c3 (cal0 0 (by decide)) (cal0 1 (by decide)) (cal0 2 (by decide))
  intro x y xy
  rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact cal 0
  · exact cal 1
  · exact cal 2
  · exact cal 3

end RKResearch.Certified.Graded.OuterHead

namespace RKResearch.Certified.Graded

open Module
open scoped Matrix

/-- All C(2) tableaux over any characteristic-zero field have the genuine
ordinary grade-six surplus once order eight is attained. The clock-invariant
and clock-escaping F3 branches are both derived, not chart premises. -/
theorem dirk_grade_six_surplus_C2 {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 8≤p)
    (c₂ : monomialStageDefect A 1=0) :
    finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6) := by
  by_cases inv : (zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3
  · by_contra bad
    obtain ⟨w,mul,_,band⟩ := dirk_grade_six_head_at_four ha ho (by omega) bad inv
    obtain ⟨C⟩ := OuterHead.c2_core_mask ha ho (by omega) c₂ mul inv
    obtain ⟨D⟩ := OuterHead.clockDebuts_of_card (OuterHead.outsideSites_card ho pay C le_rfl inv)
    exact OuterHead.no_grade_four_exterior_head ha ho pay C le_rfl D
      (w:=w) (band 0 (by decide)) (band 1 (by decide)) (band 2 (by decide))
  · exact dirk_grade_six_surplus_of_C2_of_grade_three_escape ha ho pay c₂ inv

end RKResearch.Certified.Graded
