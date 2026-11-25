import RKCert.ReviewedNative.CubicAnchoredCutoff

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.AnchorMean RKCert.ReviewedNative.CubicEnd

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {u v b : K} (u1 : u ≠ 1) (overlap : 1 < u+v) (orient : 0 ≤ u-v)
    (linear : (10-6*(u+v))*b = (6*(u+v)-9)*(u-v))
    (paired : endF u+endF v+b*(endG u-endG v) = 0) :
    (5 : K)/4 ≤ u+v ∧ -((3 : K)/5)*(u-v) ≤ b ∧ u < (11 : K)/12 ∧ v < (11 : K)/12 := by
  have H := end_bounds_of_reflected_coefficients u1 overlap orient linear paired
  exact ⟨H.sumLower, H.centerLower, H.leftUpper, H.rightUpper⟩

example {q : K[X]} {u v x : K} (qm : q.Monic) (qd : q.natDegree = 3)
    (u0 : 0 < u) (v0 : 0 < v) (u1 : u ≠ 1) (overlap : 1 < u+v) (orient : 0 ≤ u-v)
    (lu1 : (formalPrimitive (X*q)).eval u = 0)
    (lu2 : (formalPrimitive (X^2*q)).eval u = 0)
    (rv1 : (formalPrimitive (X*(-(q.comp (1-X))))).eval v = 0)
    (rv2 : (formalPrimitive (X^2*(-(q.comp (1-X))))).eval v = 0)
    (hx : (14 : K)/15 ≤ x) :
    u < (11 : K)/12 ∧ v < (11 : K)/12 ∧ 0 < q.eval x ∧
      0 < (formalPrimitive (X*(X-C u)*q)).eval x := by
  obtain ⟨up, vp, positive⟩ := positive_of_monic_cubic_end_moments qm qd u0 v0 u1 overlap orient
    lu1 lu2 (by simpa only [reflectCubic] using rv1) (by simpa only [reflectCubic] using rv2)
  exact ⟨up, vp, (positive x hx).1, by simpa only [anchorPair] using (positive x hx).2⟩

#print axioms RKCert.ReviewedNative.CubicEnd.end_bounds_of_reflected_coefficients
#print axioms RKCert.ReviewedNative.CubicEnd.quadratic_positive_of_anchor_cap
#print axioms RKCert.ReviewedNative.CubicEnd.end_bounds_of_monic_cubic_moments
#print axioms RKCert.ReviewedNative.CubicEnd.positive_of_monic_cubic_end_moments
