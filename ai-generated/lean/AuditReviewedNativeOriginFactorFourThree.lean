import RKCert.ReviewedNative.OriginFactorFourThree
import RKCert.ReviewedNative.PositiveIntervalGrid19
import RKCert.ReviewedNative.OrderedNodalGain

open Polynomial RKResearch.Certified.Graded
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.Quintic

noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The no-origin scalar leaf in the exact integral notation of the
order-17 actual-block draft. The typed input does not assert its extraction. -/
theorem audit_erk17_no_origin_scalar {P : K[X]} (pn : P≠0) (dp : P.natDegree≤5)
    (p0 : P.eval 0=0) {u v : K} (hu : u≠0) (hv : v≠0) (hvu : v≠u)
    (first : ∀ R : K[X], R.natDegree≤3 → integral 0 u (R*P)=0)
    (second : ∀ R : K[X], R.natDegree≤2 →
      integral 0 v ((R*(X-C u))*P)=0) : False := by
  apply pn
  refine rooted_four_three P (by omega) p0 hu hv hvu ?_ ?_
  · intro R hR
    simpa only [integral_zero_left,formalPrimitive_eq_native] using first R hR
  · intro R hR
    simpa only [integral_zero_left,formalPrimitive_eq_native] using second R hR

#print axioms RKCert.ReviewedNative.Quintic.rooted_four_three
#print axioms audit_erk17_no_origin_scalar
