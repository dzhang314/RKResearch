module

public import RKCert.ReviewedNative.ERK8FourOffPaidLinear

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid four-off contradiction from the linear scalar receipt -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon ERK8PaidField ERK8CharEleven
open FourOffPhysical RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open scoped Classical Matrix

variable {K : Type*} [Field K]

variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
variable {P R : K[X]} {dup k : Fin 10}

theorem no_actual_paid_four_off_linear
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (M : Placement A b P dup k)
    (L : CleanPrimitivePlacement A b k 6 (nodes A 7))
    (T : CleanTerminalProfile A (quartic (nodes A k) (nodes A 6) (nodes A 7)) R)
    (p1 : P.natDegree=1)
    (n : ∀ x∈cleanSites (nodes A k) (nodes A 6) (nodes A 7),P.eval x≠0)
    (atFour : let U := fun r : ℕ=>nodalMeasure P (cleanSites (nodes A k) (nodes A 6) (nodes A 7)) (X^r)
      U 4-2*(nodes A k)*U 3+(nodes A k)^2*U 2≠0) : False := by
  let h := nodes A k
  let S := cleanSites h (nodes A 6) (nodes A 7)
  let e := nodes A (fourthEarlyOff k)
  let U (r : ℕ) := nodalMeasure P S (X^r)
  have Sc : S.card=4 := cleanSites_card L.roots
  have sq : nodalHull S=quartic h (nodes A 6) (nodes A 7) := cleanSites_hull L.roots
  have T' : CleanTerminalProfile A (nodalHull S) R := sq.symm ▸ T
  have eq := actual_linear_terminal M Sc p1 T'
  obtain ⟨δ,tap,gain,t5,E⟩ := paid_newton_clean_transfer_linear ha ho M Sc n p1 eq
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
    apply atFour
    change U 4-2*h*U 3+h^2*U 2=0
    apply mul_left_cancel₀ gn
    rw [mul_zero]
    linear_combination -e4+2*h*e3-h^2*e2

  · rw [t5 k5,zero_mul,add_zero] at O2 O3
    have p0 : P.eval 0≠0 := n 0 (by simp [S,cleanSites])
    obtain ⟨lam,ln,z0,rec⟩ := linear_moments_geometric Sc p1 n p0
    have r01 : U 1=lam*nodalMeasure P S 1 := by
      simpa only [pow_zero] using rec 0 (by decide)
    have r12 : U 2=lam*U 1 := rec 1 (by decide)
    have r23 : U 3=lam*U 2 := rec 2 (by decide)
    have un : U 3≠0 := by
      rw [r23,r12,r01]
      exact mul_ne_zero ln (mul_ne_zero ln (mul_ne_zero ln z0))
    apply un
    linear_combination -3*lam*O2+2*O3-6*δ*r23+6*δ*e*r12+3*r23

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.no_actual_paid_four_off_linear
