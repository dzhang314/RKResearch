module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKResearch.Certified.ERK10TwoDirtyProjection

variable {K : Type*} [Field K]

/-- Projecting onto two live donor clocks without ever inverting a dirty
response. This uses true marks of degree at most two and independent
scalar responses at the two donor coordinates. -/
theorem pointwise_four_clock
    (p q x y dp dq dx dy fp fq fx fy gp gq gx gy : K)
    (hpx : p ≠ x) (hpy : p ≠ y) (hqx : q ≠ x) (hqy : q ≠ y) (hxy : x ≠ y)
    (hdet : fp * gq - gp * fq ≠ 0)
    (hx : fx ≠ 0 ∨ gx ≠ 0) (hy : fy ≠ 0 ∨ gy ≠ 0)
    (f0 : dp * fp + dq * fq + dx * fx + dy * fy = 0)
    (f1 : p * (dp * fp) + q * (dq * fq) + x * (dx * fx) + y * (dy * fy) = 0)
    (f2 : p^2 * (dp * fp) + q^2 * (dq * fq) + x^2 * (dx * fx) + y^2 * (dy * fy) = 0)
    (g0 : dp * gp + dq * gq + dx * gx + dy * gy = 0)
    (g1 : p * (dp * gp) + q * (dq * gq) + x * (dx * gx) + y * (dy * gy) = 0)
    (g2 : p^2 * (dp * gp) + q^2 * (dq * gq) + x^2 * (dx * gx) + y^2 * (dy * gy) = 0) :
    dp = 0 ∧ dq = 0 ∧ dx = 0 ∧ dy = 0 := by
  have f : fp * (dp * (p-x) * (p-y)) + fq * (dq * (q-x) * (q-y)) = 0 := by
    linear_combination f2 - (x+y)*f1 + (x*y)*f0
  have g : gp * (dp * (p-x) * (p-y)) + gq * (dq * (q-x) * (q-y)) = 0 := by
    linear_combination g2 - (x+y)*g1 + (x*y)*g0
  have hp0 : dp * ((p-x) * ((p-y) * (fp*gq-gp*fq))) = 0 := by
    linear_combination gq*f - fq*g
  have hq0 : dq * ((q-x) * ((q-y) * (fp*gq-gp*fq))) = 0 := by
    linear_combination fp*g - gp*f
  have hp' : dp = 0 := (mul_eq_zero.mp hp0).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hpx) (mul_ne_zero (sub_ne_zero.mpr hpy) hdet))
  have hq' : dq = 0 := (mul_eq_zero.mp hq0).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hqx) (mul_ne_zero (sub_ne_zero.mpr hqy) hdet))
  have hxf : dx * ((x-y)*fx) = 0 := by
    linear_combination f1 - y*f0 - ((p-y)*fp)*hp' - ((q-y)*fq)*hq'
  have hxg : dx * ((x-y)*gx) = 0 := by
    linear_combination g1 - y*g0 - ((p-y)*gp)*hp' - ((q-y)*gq)*hq'
  have hyf : dy * ((x-y)*fy) = 0 := by
    linear_combination x*f0 - f1 - ((x-p)*fp)*hp' - ((x-q)*fq)*hq'
  have hyg : dy * ((x-y)*gy) = 0 := by
    linear_combination x*g0 - g1 - ((x-p)*gp)*hp' - ((x-q)*gq)*hq'
  refine ⟨hp', hq', ?_, ?_⟩
  · exact hx.elim
      (fun hf => (mul_eq_zero.mp hxf).resolve_right (mul_ne_zero (sub_ne_zero.mpr hxy) hf))
      (fun hg => (mul_eq_zero.mp hxg).resolve_right (mul_ne_zero (sub_ne_zero.mpr hxy) hg))
  · exact hy.elim
      (fun hf => (mul_eq_zero.mp hyf).resolve_right (mul_ne_zero (sub_ne_zero.mpr hxy) hf))
      (fun hg => (mul_eq_zero.mp hyg).resolve_right (mul_ne_zero (sub_ne_zero.mpr hxy) hg))

/-- Compare one *actual* clock mark with multiplication by the nominal
clock at each donor. Checking the first two model monomials isolates
the discrepancies by a two-clock determinant. -/
theorem marked_axes (p q u v : K) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h1 : p*u + q*v = 0) (h2 : p^2*u + q^2*v = 0) : u = 0 ∧ v = 0 := by
  have hpu : u * (p * (p-q)) = 0 := by linear_combination h2 - q*h1
  have hqv : v * (q * (p-q)) = 0 := by linear_combination p*h1 - h2
  exact ⟨(mul_eq_zero.mp hpu).resolve_right (mul_ne_zero hp (sub_ne_zero.mpr hpq)),
    (mul_eq_zero.mp hqv).resolve_right (mul_ne_zero hq (sub_ne_zero.mpr hpq))⟩

/-- If two distinct dirty clocks share the same live donor direction,
the extra marked equation and the hull equation force that donor to be
on the supported high mesh. No positivity is used. -/
theorem aligned_hull (a b p u v T : K) (hab : a ≠ b) (hu : u ≠ 0)
    (hm : (a-p)*u + (b-p)*v = 0) (hT : (u+v)*T = 0) : T = 0 := by
  apply (mul_eq_zero.mp hT).resolve_left
  intro huv
  have hz : u * (a-b) = 0 := by linear_combination hm - (b-p)*huv
  exact (mul_ne_zero hu (sub_ne_zero.mpr hab)) hz


/-- The quadratic/affine elimination used after both low donor
clocks have been identified with actual high sites. -/
theorem quad_affine_resultant_zero
    (f0 f1 f2 g0 g1 z : K)
    (hf : f0 + f1*z + f2*z^2 = 0) (hg : g0 + g1*z = 0) :
    f0*g1^2 - f1*g0*g1 + f2*g0^2 = 0 := by
  linear_combination g1^2*hf - (f1*g1 + f2*(g1*z-g0))*hg

end RKResearch.Certified.ERK10TwoDirtyProjection
