import Mathlib.Tactic.Ring

/-! Scalar certificates for the pivot-free dormant-site Gram equations.
The four entries u, v, w, z are literal pairings in the two anchored
models. The hypotheses express the paid row orthogonalities; the
conclusions deliberately retain the zero-pivot cases. -/

namespace RKResearch.Certified.ERK11DormantInverseGramPort

variable {R : Type*} [CommRing R]

theorem central (u v w z b A B C D h k : R)
    (hL : B + h*A = 0) (hR : D + k*C = 0)
    (hdiag : b*(u+k*v+h*w+h*k*z) = 1) :
    b*(A*C*u-A*D*v-B*C*w+B*D*z) = A*C := by
  have hB : B = -(h*A) := eq_neg_of_add_eq_zero_left hL
  have hD : D = -(k*C) := eq_neg_of_add_eq_zero_left hR
  rw [hB, hD]
  calc
    _ = (A*C)*(b*(u+k*v+h*w+h*k*z)) := by ring
    _ = A*C := by rw [hdiag, mul_one]

theorem one_sided (u v b a C D k : R)
    (hR : D + k*C = 0)
    (hdiag : b*(u+k*v) = a) :
    b*(C*u-D*v) = a*C := by
  have hD : D = -(k*C) := eq_neg_of_add_eq_zero_left hR
  rw [hD]
  calc
    _ = (b*(u+k*v))*C := by ring
    _ = a*C := by rw [hdiag]

theorem denominator_clearing (q b I L v : R)
    (hL : b*L = v) (hb : q*b = I) : q*v = I*L := by
  rw [← hL, ← mul_assoc, hb]

#print axioms central
#print axioms one_sided
#print axioms denominator_clearing
end RKResearch.Certified.ERK11DormantInverseGramPort
