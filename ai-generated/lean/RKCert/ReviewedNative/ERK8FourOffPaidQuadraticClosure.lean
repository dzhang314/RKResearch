module

public import RKCert.ReviewedNative.ERK8CharElevenFourExclusion

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid four-off contradiction from the quadratic scalar receipt -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon ERK8PaidField ERK8CharEleven
open FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open scoped Classical Matrix

variable {K : Type*} [Field K]

variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
variable {P R : K[X]} {dup k : Fin 10}

theorem no_actual_paid_four_off_quadratic
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (M : Placement A b P dup k)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (T : CleanTerminalProfile A (quartic (nodes A k) (nodes A 6) (nodes A 7)) R)
    (Q : QuadraticHeadReceipt P (nodes A k) (nodes A 6) (nodes A 7)) : False := by
  let h := nodes A k
  let S := cleanSites h (nodes A 6) (nodes A 7)
  let e := nodes A (fourthEarlyOff k)
  let U (r : ℕ) := nodalMeasure P S (X^r)
  have Sc : S.card=4 := cleanSites_card L.roots
  have sq : nodalHull S=quartic h (nodes A 6) (nodes A 7) := cleanSites_hull L.roots
  have T' : CleanTerminalProfile A (nodalHull S) R := sq.symm ▸ T
  obtain ⟨sig,sn,eq⟩ := actual_terminal_hull_transfer M Sc Q.nonzero Q.degree T'
  obtain ⟨δ,tap,gain,t5,E⟩ := paid_newton_clean_transfer ha ho M Sc Q.nonzero Q.degree sn eq
  have cleared (r : ℕ) (r1 : 1≤r) (r3 : r≤3) :
      (((r+1:ℕ):K))*(δ*(U (r+1)-e*U r)+tap*h^r)=U (r+1) ∧
        (k=4→(((r+1:ℕ):K))*gain*(U (r+1)-e*U r)=h^(r+1)) := by
    obtain ⟨B,C⟩ := E r r1 r3
    have nz : (((r+1:ℕ):K))≠0 := (ho.natCast_isUnit (by omega) (by omega)).ne_zero
    have b₁ := congrArg (fun u : K=>((r+1:ℕ):K)*u) B
    simp only [mul_div_cancel₀ _ nz] at b₁
    refine ⟨b₁,fun k4=>?_⟩
    have b₂ := congrArg (fun u : K=>((r+1:ℕ):K)*u) (C k4)
    simp only [mul_div_cancel₀ _ nz] at b₂
    simpa only [mul_assoc] using b₂
  obtain ⟨O2,H2⟩ := cleared 1 (by decide) (by decide)
  obtain ⟨O3,H3⟩ := cleared 2 (by decide) (by decide)
  obtain ⟨O4,H4⟩ := cleared 3 (by decide) (by decide)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,pow_one] at O2 O3 O4 H2 H3 H4
  rcases M.firstAtFourOrFive with k4|k5
  · specialize H2 k4
    specialize H3 k4
    specialize H4 k4
    have gn : gain≠0 := by
      intro g0
      have z : h^2=0 := by simpa [g0] using H2.symm
      exact pow_ne_zero 2 M.firstClockNe z
    have e2 : δ*h^2+2*gain*tap*h=gain*U 2 := by
      linear_combination gain*O2-δ*H2
    have e3 : δ*h^3+3*gain*tap*h^2=gain*U 3 := by
      linear_combination gain*O3-δ*H3
    have e4 : δ*h^4+4*gain*tap*h^3=gain*U 4 := by
      linear_combination gain*O4-δ*H4
    apply Q.atFour
    change U 4-2*h*U 3+h^2*U 2=0
    apply mul_left_cancel₀ gn
    rw [mul_zero]
    linear_combination -e4+2*h*e3-h^2*e2
  · rw [t5 k5,zero_mul,add_zero] at O2 O3 O4
    have det : U 1*U 3*U 4-3*(U 2)^2*U 4+2*U 2*(U 3)^2=0 := by
      linear_combination -6*((U 3)^2-U 2*U 4)*O2-4*(U 1*U 4-U 2*U 3)*O3-
        3*((U 2)^2-U 1*U 3)*O4
    have R₁ := nodalMeasure_quadratic_recurrence M.rankData.headDegree Sc Q.nonzero 1 (by decide)
    have R₂ := nodalMeasure_quadratic_recurrence M.rankData.headDegree Sc Q.nonzero 2 (by decide)
    change P.coeff 0*U 1+P.coeff 1*U 2+P.coeff 2*U 3=0 at R₁
    change P.coeff 0*U 2+P.coeff 1*U 3+P.coeff 2*U 4=0 at R₂
    have rc : P.coeff 2*(U 2*U 4-(U 3)^2)-P.coeff 0*(U 1*U 3-(U 2)^2)=0 := by
      linear_combination U 2*R₂-U 3*R₁
    have close : (U 1*U 3-(U 2)^2)*(P.coeff 2*U 4-2*P.coeff 0*U 2)=0 := by
      linear_combination P.coeff 2*det+2*U 2*rc
    exact mul_ne_zero Q.atFiveA Q.atFiveB close

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.no_actual_paid_four_off_quadratic
