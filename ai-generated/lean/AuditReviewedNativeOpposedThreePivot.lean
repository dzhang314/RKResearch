import RKCert.ReviewedNative.OpposedThreePivot

open Polynomial RKCert.ReviewedNative.FiniteOrderedSigns

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem audit_opposed_three_pivot_X_one {P : K[X]} {a b c : K}
    (h : OpposedThreePivotMoments P X 1 a b c) (pn : P≠0) (pd : P.natDegree≤5)
    (ha : a∈Set.Ioo (0:K) 1) (hb : b∈Set.Ioo (0:K) 1) (hc : c∈Set.Ioo (0:K) 1)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) : False := by
  have up (x : K) (hx : x∈Set.Ioo (0:K) 1) : 0 < (X : K[X]).eval x := by
    simpa only [eval_X] using hx.1
  have vp (x : K) (_ : x∈Set.Ioo (0:K) 1) : 0 < (1 : K[X]).eval x := by simp
  have ub : (X : K[X]).natDegree+P.natDegree+2≤19 := by rw [natDegree_X]; omega
  have vb : (1 : K[X]).natDegree+P.natDegree+2≤19 := by rw [natDegree_one]; omega
  have d := h.six_le_natDegree pn ha hb hc ab ac bc up vp ub vb
  omega

#print axioms RKCert.ReviewedNative.FiniteOrderedSigns.OpposedThreePivotMoments.six_le_natDegree
#print axioms audit_opposed_three_pivot_X_one
