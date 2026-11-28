module
public import RKCert.ReviewedNative.DIRK12Q36RealMomentChecks
public import RKCert.ReviewedNative.DIRK12Q36PackedGate30
public import RKCert.ReviewedNative.DIRK12Q36PackedGate31
public import RKCert.ReviewedNative.DIRK12Q36PackedGate32
public import RKCert.ReviewedNative.DIRK12Q36PackedGate40
public import RKCert.ReviewedNative.DIRK12Q36PackedGate41
public import RKCert.ReviewedNative.DIRK12Q36PackedGate42
public import RKCert.ReviewedNative.DIRK12MidpointScalarQuadrature
import Mathlib.Tactic.FinCases

@[expose] public section

/-! The actual characteristic-zero degree-36/cubic root equations imply
both exact support moment gates. No reduction of an unknown real
tableau modulo a prime or inference from interval residuals is used. -/
namespace RKResearch.Certified.DIRK12Q36Moments

open IntegerPolyRootReplay IntegerPolyRootReplay.Packing
open DirectedRatBox DIRK12MidpointRealInterval
open DIRK12MidpointMomentTransfers (rel3 rel4)
open scoped Polynomial

theorem gates3 {K : Type*} [CommRing K] {x : K} (hx : eval Q x=0) (i : Fin 3) :
    Packing.read x (gate R3 i)=0 := by
  fin_cases i
  · exact gate30_checked hx
  · exact gate31_checked hx
  · exact gate32_checked hx

theorem gates4 {K : Type*} [CommRing K] {x : K} (hx : eval Q x=0) (i : Fin 3) :
    Packing.read x (gate R4 i)=0 := by
  fin_cases i
  · exact gate40_checked hx
  · exact gate41_checked hx
  · exact gate42_checked hx

theorem real_relations {x f : ℝ} (hx : realX x=0) (hf : realF x f=0) :
    rel3 (moments x f 0) (moments x f 1) (moments x f 2) (moments x f 3)=0 ∧
    rel4 (moments x f 0) (moments x f 1) (moments x f 2) (moments x f 3) (moments x f 4)=0 := by
  let n := moments x f
  have n0 : linEval x f N0 = (den:ℝ)*n 0 := real_lin_value momentChecks x f 0
  have n1 : linEval x f N1 = (den:ℝ)*n 1 := real_lin_value momentChecks x f 1
  have n2 : linEval x f N2 = (den:ℝ)*n 2 := real_lin_value momentChecks x f 2
  have n3 : linEval x f N3 = (den:ℝ)*n 3 := real_lin_value momentChecks x f 3
  have n4 : linEval x f N4 = (den:ℝ)*n 4 := real_lin_value momentChecks x f 4
  have h3 := from_coefficient_checks x f R3 fdNZ (f_at_real_root hf) (gates3 (q_at_real_root hx))
  have h4 := from_coefficient_checks x f R4 fdNZ (f_at_real_root hf) (gates4 (q_at_real_root hx))
  rw [r3_read,n0,n1,n2,n3] at h3
  rw [r4_read,n0,n1,n2,n3,n4] at h4
  have e3 : rel3 ((den:ℝ)*n 0) ((den:ℝ)*n 1) ((den:ℝ)*n 2) ((den:ℝ)*n 3) =
      (den:ℝ)^3* rel3 (n 0) (n 1) (n 2) (n 3) := by
    unfold rel3 DIRK12MidpointMomentTransfers.B
    ring
  have e4 : rel4 ((den:ℝ)*n 0) ((den:ℝ)*n 1) ((den:ℝ)*n 2) ((den:ℝ)*n 3) ((den:ℝ)*n 4) =
      (den:ℝ)^3* rel4 (n 0) (n 1) (n 2) (n 3) (n 4) := by
    unfold rel4 DIRK12MidpointMomentTransfers.A
    ring
  rw [e3] at h3
  rw [e4] at h4
  exact ⟨(mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ denNZ),
    (mul_eq_zero.mp h4).resolve_left (pow_ne_zero _ denNZ)⟩

theorem real_paid_scalar {x f d v : ℝ}
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hex : realX x=0) (hef : realF x f=0)
    (hs : d+v = S (moments x f)) (hp : d*v=P (moments x f))
    (sites : Fin 10 → ℝ) (distinct : Function.Injective sites)
    (hull_eq : Lagrange.nodal Finset.univ sites = supportHull x f d v)
    (q : ℝ[X]) (hq : q.natDegree<12) :
    PaidNodalQuadrature.quadr Finset.univ sites integral q=integral q := by
  obtain ⟨h3,h4⟩ := real_relations hex hef
  exact scalar_quadrature_of_two_relations x f d v hx hf hs hp h3 h4 sites distinct hull_eq q hq

end RKResearch.Certified.DIRK12Q36Moments

#print axioms RKResearch.Certified.DIRK12Q36Moments.real_relations
#print axioms RKResearch.Certified.DIRK12Q36Moments.real_paid_scalar
