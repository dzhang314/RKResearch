import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneQuadraticBoundary

variable {K : Type*} [Field K]

/-- The third coefficient of the actual quadratic carrier kills the free
cubic-hull parameter; this point does not require a nonzero lower coefficient. -/
theorem cubic_parameter_zero {u m t r : K}
    (hu : u = 0) (hm : m = 0) (hr : r = 1) (h : u = m + t*r) : t = 0 := by
  rw [hu, hm, hr, mul_one, zero_add] at h
  exact h.symm

/-- Scalar end of the three-late commutator calculation. The first three
rows are the genuine old reads of the cancelled polynomial identity.
The fourth row pays the scalar multiplier; the last is the literal
commutator diagonal. No diagonal or lower coefficient is inverted. -/
theorem zero_fifth_of_cancelled_old_reads
    {e0 e1 e2 j0 j1 j2 y0 y1 y2 e y mu eta l0 l1 r u d jB uB : K}
    (h0 : eta*j0+l0*e0+l1*y0*e0 = 0)
    (h1 : eta*j1+l0*e1+l1*y1*e1 = 0)
    (h2 : eta*j2+l0*e2+l1*y2*e2 = 0)
    (hd : j0*(e1*y2*e2-e2*y1*e1)-j1*(e0*y2*e2-e2*y0*e0)
          +j2*(e0*y1*e1-e1*y0*e0) ≠ 0)
    (hread : mu*r = eta*u+(l0+l1*y)*e)
    (hr : r ≠ 0) (hdiag : mu*jB = -d^2*uB) (huB : uB ≠ 0) :
    d = 0 := by
  let D := j0*(e1*y2*e2-e2*y1*e1)-j1*(e0*y2*e2-e2*y0*e0)
           +j2*(e0*y1*e1-e1*y0*e0)
  have hD : D ≠ 0 := hd
  have hc : D * eta = 0 := by
    dsimp [D]
    linear_combination (e1*y2*e2-e2*y1*e1)*h0
      -(e0*y2*e2-e2*y0*e0)*h1 +(e0*y1*e1-e1*y0*e0)*h2
  have hcl : D * l0 = 0 := by
    dsimp [D]
    linear_combination -(j1*y2*e2-j2*y1*e1)*h0
      +(j0*y2*e2-j2*y0*e0)*h1 -(j0*y1*e1-j1*y0*e0)*h2
  have hcr : D * l1 = 0 := by
    dsimp [D]
    linear_combination (j1*e2-j2*e1)*h0
      -(j0*e2-j2*e0)*h1 +(j0*e1-j1*e0)*h2
  have he : eta = 0 := (mul_eq_zero.mp hc).resolve_left hD
  have hl : l0 = 0 := (mul_eq_zero.mp hcl).resolve_left hD
  have hl' : l1 = 0 := (mul_eq_zero.mp hcr).resolve_left hD
  have hmr : mu*r = 0 := by simpa [he, hl, hl'] using hread
  have hm : mu = 0 := (mul_eq_zero.mp hmr).resolve_right hr
  have hz : d*d*uB = 0 := by
    rw [hm] at hdiag
    linear_combination hdiag
  exact ((mul_eq_zero.mp hz).resolve_right huB |> mul_eq_zero.mp).elim id id

/-- The divided difference is safe at a lower leader and uses only
the actual distinct marked roots.  The convention is the exact scaled
two-clock polynomial evaluated at the next root. -/
theorem second_distinct_homogeneous_read
    {a0 a1 a2 a3 p q x : K}
    (hd : q*x-p ≠ 0)
    (h0 : a0*q^3+a1*p*q^2+a2*p^2*q+a3*p^3=0)
    (hx : a0+a1*x+a2*x^2+a3*x^3=0) :
    q^2*a1+p*q*a2+p^2*a3+(q^2*a2+p*q*a3)*x+q^2*a3*x^2=0 := by
  apply (mul_eq_zero.mp ?_).resolve_left hd
  linear_combination q^3*hx-h0

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneQuadraticBoundary

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneQuadraticBoundary
#print axioms cubic_parameter_zero
#print axioms zero_fifth_of_cancelled_old_reads
#print axioms second_distinct_homogeneous_read
