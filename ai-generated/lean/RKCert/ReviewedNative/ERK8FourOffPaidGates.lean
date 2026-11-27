module

public import RKCert.ReviewedNative.ERK8FourOffPaidMeasure

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Three finite scalar tests for the actual paid Newton rows -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical

variable {K : Type*} [Field K]

def firstCleanFourGate (o : CleanOrientation) (u : K) : K :=
  clearedMoment o u 3-4*chartH o u*clearedMoment o u 2+
    4*(chartH o u)^2*clearedMoment o u 1

def firstCleanFiveGram (o : CleanOrientation) (u : K) : K :=
  clearedMoment o u 0*clearedMoment o u 2-(clearedMoment o u 1)^2

def firstCleanFiveGate (o : CleanOrientation) (u : K) : K :=
  (chartQuadratic o u).p2*clearedMoment o u 3-
    8*(chartQuadratic o u).p0*clearedMoment o u 1

structure CleanCapsNonzero (o : CleanOrientation) (u : K) : Prop where
  p0 : (chartQuadratic o u).p0≠0
  first : capFirst o u≠0
  last : capLast o u≠0
  middle : capMiddle o u≠0

structure QuadraticChartTests (o : CleanOrientation) (u : K) : Prop where
  caps : CleanCapsNonzero o u
  p2 : (chartQuadratic o u).p2≠0
  four : firstCleanFourGate o u≠0
  gram : firstCleanFiveGram o u≠0
  five : firstCleanFiveGate o u≠0

structure LinearChartTests (o : CleanOrientation) (u : K) : Prop where
  caps : CleanCapsNonzero o u
  p2 : (chartQuadratic o u).p2=0
  p1 : (chartQuadratic o u).p1≠0
  four : firstCleanFourGate o u≠0

/-- A candidate chart is rejected by its one common clean root or
is an exact quadratic or linear receipt. -/
inductive ChartResult (o : CleanOrientation) (u : K) : Prop
  | quadratic : QuadraticChartTests o u → ChartResult o u
  | linear : LinearChartTests o u → ChartResult o u
  | sharedFirst : (chartQuadratic o u).p2≠0 → (chartQuadratic o u).p0≠0 →
      capFirst o u=0 → capLast o u≠0 → capMiddle o u≠0 → ChartResult o u
  | sharedLast : (chartQuadratic o u).p2≠0 → (chartQuadratic o u).p0≠0 →
      capLast o u=0 → capFirst o u≠0 → capMiddle o u≠0 → ChartResult o u
  | sharedMiddle : (chartQuadratic o u).p2≠0 → (chartQuadratic o u).p0≠0 →
      capMiddle o u=0 → capFirst o u≠0 → capLast o u≠0 → ChartResult o u

theorem clean_eval_ne_of_caps {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2) (N : CleanCapsNonzero o u) :
    ∀ x∈cleanSites (chartH o u) (chartX o u) (chartZ o u),P.eval x≠0 := by
  rw [cleanSites_chart_eq]
  intro x hx
  simp only [cleanSites,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with h|h|h|h
  · rw [h]; exact fun z=>N.p0 (by simpa [Quad.eval] using (S.eval_zero_iff d 0).mp z)
  · rw [h]; exact fun z=>N.first ((S.eval_zero_iff d u).mp z)
  · rw [h]; exact fun z=>N.middle ((S.eval_zero_iff d (midClock K)).mp z)
  · rw [h]; exact fun z=>N.last ((S.eval_zero_iff d (1-u)).mp z)

theorem native_four_gate_of_chart_test [EightUnits K] {P : K[X]} {o : CleanOrientation} {u kap : K}
    (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2) (q : sevenQuad u=0)
    (D : CleanClocks (chartH o u) (chartX o u) (chartZ o u)) (N : CleanCapsNonzero o u)
    (hok : firstCleanFourGate o u≠0) :
    let U := fun r : ℕ=>nodalMeasure P (cleanSites (chartH o u) (chartX o u) (chartZ o u)) (X^r)
    U 4-2*chartH o u*U 3+(chartH o u)^2*U 2≠0 := by
  dsimp only
  intro z
  let h := chartH o u
  let cs := cleanSites h (chartX o u) (chartZ o u)
  let U (r : ℕ) := nodalMeasure P cs (X^r)
  let m := 3*(kap/chartScale o)*capFirst o u*capLast o u*capMiddle o u
  change U 4-2*h*U 3+h^2*U 2=0 at z
  have a : (m*2)*U 2=14*clearedMoment o u 1 := by
    simpa only [pow_one] using paid_cleared_moment S d q D N.first N.last N.middle 1
  have b : (m*4)*U 3=14*clearedMoment o u 2 := by
    have e := paid_cleared_moment S d q D N.first N.last N.middle 2
    change (m*2^2)*U 3=_ at e
    rw [show (2:K)^2=4 by ring] at e
    exact e
  have c : (m*8)*U 4=14*clearedMoment o u 3 := by
    have e := paid_cleared_moment S d q D N.first N.last N.middle 3
    change (m*2^3)*U 4=_ at e
    rw [show (2:K)^3=8 by ring] at e
    exact e
  apply hok
  unfold firstCleanFourGate
  change clearedMoment o u 3-4*h*clearedMoment o u 2+4*h^2*clearedMoment o u 1=0
  apply mul_left_cancel₀ (fourteen_paid K)
  rw [mul_zero]
  linear_combination -c+4*h*b-4*h^2*a+8*m*z

theorem native_quadratic_receipt_of_chart_tests [EightUnits K] {P : K[X]} {o : CleanOrientation}
    {u kap : K} (S : ScaledPaidHead P o u kap) (d : P.natDegree≤2) (q : sevenQuad u=0)
    (D : CleanClocks (chartH o u) (chartX o u) (chartZ o u)) (N : QuadraticChartTests o u) :
    QuadraticHeadReceipt P (chartH o u) (chartX o u) (chartZ o u) := by
  let cs := cleanSites (chartH o u) (chartX o u) (chartZ o u)
  let U (r : ℕ) := nodalMeasure P cs (X^r)
  let m := 3*(kap/chartScale o)*capFirst o u*capLast o u*capMiddle o u
  let W (r : ℕ) := clearedMoment o u r
  have a : m*U 1=14*W 0 := by
    simpa only [pow_zero,mul_one] using paid_cleared_moment S d q D N.caps.first N.caps.last N.caps.middle 0
  have b : (m*2)*U 2=14*W 1 := by
    simpa only [pow_one] using paid_cleared_moment S d q D N.caps.first N.caps.last N.caps.middle 1
  have c : (m*4)*U 3=14*W 2 := by
    have e := paid_cleared_moment S d q D N.caps.first N.caps.last N.caps.middle 2
    change (m*2^2)*U 3=_ at e
    rw [show (2:K)^2=4 by ring] at e
    exact e
  have f : (m*8)*U 4=14*W 3 := by
    have e := paid_cleared_moment S d q D N.caps.first N.caps.last N.caps.middle 3
    change (m*2^3)*U 4=_ at e
    rw [show (2:K)^3=8 by ring] at e
    exact e
  refine ⟨S.degree_two d N.p2,clean_eval_ne_of_caps S d N.caps,
    native_four_gate_of_chart_test S d q D N.caps N.four,?_,?_⟩
  · change U 1*U 3-(U 2)^2≠0
    intro z
    apply N.gram
    change W 0*W 2-(W 1)^2=0
    apply mul_left_cancel₀ (pow_ne_zero 2 (fourteen_paid K))
    rw [mul_zero]
    calc
      _ = (14*W 0)*(14*W 2)-(14*W 1)^2 := by ring
      _ = 0 := by
        rw [←a,←b,←c]
        linear_combination 4*m^2*z
  · change P.coeff 2*U 4-2*P.coeff 0*U 2≠0
    intro z
    apply N.five
    change (chartQuadratic o u).p2*W 3-8*(chartQuadratic o u).p0*W 1=0
    apply mul_left_cancel₀ (mul_ne_zero (fourteen_paid K) S.kap_ne)
    rw [mul_zero]
    calc
      _ = (kap*(chartQuadratic o u).p2)*(14*W 3)-
        8*(kap*(chartQuadratic o u).p0)*(14*W 1) := by ring
      _ = 0 := by
        rw [←f,←b,←S.eq0,←S.eq2]
        linear_combination 8*chartScale o*m*z

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.native_quadratic_receipt_of_chart_tests
