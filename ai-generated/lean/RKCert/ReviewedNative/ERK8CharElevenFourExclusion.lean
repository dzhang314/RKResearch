module

public import RKCert.ReviewedNative.ERK8CharElevenFourCenteredExclusion
public import RKCert.ReviewedNative.ERK8CharElevenFourNoncenterScalar
public import RKCert.ReviewedNative.ERK8FourOffPhysicalNewton
public import RKCert.ReviewedNative.ERK8CharElevenFiveExclusion

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The remaining native characteristic-eleven four-off contradiction
No generic noncenter chart guard is kept as a caller hypothesis:
the two algebraic orientations, leading-coefficient transfer, physical
causality and both chronological clean placements are paid in separate modules. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon ERK8PaidField ERK8CharEleven
open FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical Matrix

variable {K : Type*} [Field K]

theorem nodalMeasure_quadratic_recurrence {P : K[X]} {S : Finset K}
    (p2 : P.natDegree≤2) (s4 : S.card=4) (pv : ∀ x∈S,P.eval x≠0)
    (r : ℕ) (r2 : r≤2) :
    P.coeff 0*nodalMeasure P S (X^r)+P.coeff 1*nodalMeasure P S (X^(r+1))+
      P.coeff 2*nodalMeasure P S (X^(r+2))=0 := by
  have e : nodalMeasure P S (P*X^r)=0 := by
    have d : (X^r : K[X]).natDegree≤2 := (natDegree_X_pow_le _).trans r2
    have eq := coeff_last_barycentric S (X^r : K[X]) (by rw [s4]; omega)
    rw [s4,show (4-1:ℕ)=3 by decide,coeff_eq_zero_of_natDegree_lt (d.trans_lt (by decide))] at eq
    rw [nodalMeasure]
    refine Eq.trans ?_ eq.symm
    apply Finset.sum_congr rfl
    intro x hx
    rw [eval_mul,mul_comm (P.eval x),mul_div_cancel_right₀ _ (pv x hx)]
    rfl
  have pol : P*X^r=C (P.coeff 0)*X^r+C (P.coeff 1)*X^(r+1)+C (P.coeff 2)*X^(r+2) := by
    conv_lhs => rw [LobattoEight.quadratic_coeff_expand P p2]
    simp only [←C_mul_X_pow_eq_monomial,pow_add,pow_zero,pow_one,mul_one,add_mul]
    ring
  rwa [pol,nodalMeasure_add,nodalMeasure_add,nodalMeasure_Cmul,nodalMeasure_Cmul,nodalMeasure_Cmul] at e

variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
variable {P R : K[X]} {dup k : Fin 10}

theorem no_actual_noncenter_four_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (M : Placement A b P dup k)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (T : CleanTerminalProfile A (quartic (nodes A k) (nodes A 6) (nodes A 7)) R)
    {theta kap : K} (N : RawPaidShape P (nodes A k) (nodes A 6) (nodes A 7) theta kap)
    (q : (exceptionalQuadratic : K[X]).eval (nodes A k)=0) : False := by
  let h := nodes A k
  let S := cleanSites h (nodes A 6) (nodes A 7)
  let e := nodes A (fourthEarlyOff k)
  let U (r : ℕ) := nodalMeasure P S (X^r)
  have Sc : S.card=4 := cleanSites_card L.roots
  have sq : nodalHull S=quartic h (nodes A 6) (nodes A 7) := cleanSites_hull L.roots
  have Q := noncenter_char11_receipt p q M.rankData.headDegree M.rankData.headNonzero L.roots N
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

namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon FourOffNewton
open scoped Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- An unconditional exclusion of the literal four-off branch of an
order-eight ten-stage tableau in characteristic eleven. -/
theorem no_four_off_char11
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0) :
    (offKnots A).card≠4 := by
  intro h
  obtain ⟨P,R,dup,k,theta,scale,M,L,T,N,shape⟩ := order8_four_off_center_or_quadratic ha ho p h
  rcases shape with ⟨center,_,tn,fit,s,m⟩|quad
  · exact FourOff.no_actual_centered_four_off ha ho p M L center tn fit s m
  · exact no_actual_noncenter_four_off ha ho p M L T N quad

/-- Every literal width-ten order-eight explicit tableau in characteristic
eleven, if it exists, has exactly one off clock. -/
theorem order8_char11_only_one_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0) :
    (offKnots A).card=1 := by
  rcases order8_paid_only_one_or_four_off ha ho with c|⟨c,_⟩
  · exact c
  · exact (no_four_off_char11 ha ho p c).elim

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.no_four_off_char11
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_char11_only_one_off
