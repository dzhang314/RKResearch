import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSquare

/-- The grouped square at a two-member h-fiber. No sign or weight
division enters the comparison with its ordinary mass. -/
theorem pair_square_masses {K : Type*} [CommRing K] {b0 b1 h0 h1 : K}
    (h : b0*h0+b1*h1=0) :
    (b0*h0^2+b1*h1^2 = -(h0*h1)*(b0+b1)) ∧
    (b0*h0^2+b1*h1^2 = b0*h0*(h0-h1)) := by
  constructor
  · linear_combination (h0+h1)*h
  · linear_combination h1*h

variable {K : Type*} [Field K]

/-- With at most two physical g-carriers, the three genuine
Gg, Gg² and Ggh reads kill both unmarked and h-marked dirty G sums.
The cubic values may agree or differ. -/
theorem two_ghost_grouped_reverse_zero
    {g0 g1 h0 h1 G0 G1 : K} (nz0 : g0≠0) (nz1 : g1≠0)
    (a : G0*g0+G1*g1=0) (b : G0*g0^2+G1*g1^2=0)
    (c : G0*g0*h0+G1*g1*h1=0) :
    G0+G1=0 ∧ G0*h0+G1*h1=0 := by
  by_cases eq : g0=g1
  · rw [← eq] at a c
    constructor
    · apply (mul_eq_zero.mp ?_).resolve_left nz0
      linear_combination a
    · apply (mul_eq_zero.mp ?_).resolve_left nz0
      linear_combination c
  · have e0 : G0*g0*(g0-g1)=0 := by linear_combination b-g1*a
    have e1 : G1*g1*(g0-g1)=0 := by linear_combination g0*a-b
    have c0 : G0=0 := (mul_eq_zero.mp
      ((mul_eq_zero.mp e0).resolve_right (sub_ne_zero.mpr eq))).resolve_right nz0
    have c1 : G1=0 := (mul_eq_zero.mp
      ((mul_eq_zero.mp e1).resolve_right (sub_ne_zero.mpr eq))).resolve_right nz1
    simp [c0,c1]

/-- Select the first of four different numerical label masses using
only the paid scalar degrees zero through three. -/
theorem four_marked_moments_kill_first
    {a b c d G0 G1 G2 G3 : K} (ab : a≠b) (ac : a≠c) (ad : a≠d)
    (m0 : G0+G1+G2+G3=0)
    (m1 : G0*a+G1*b+G2*c+G3*d=0)
    (m2 : G0*a^2+G1*b^2+G2*c^2+G3*d^2=0)
    (m3 : G0*a^3+G1*b^3+G2*c^3+G3*d^3=0) :
    G0=0 := by
  have hz : G0*(a-b)*(a-c)*(a-d)=0 := by
    linear_combination m3-(b+c+d)*m2+(b*c+b*d+c*d)*m1-b*c*d*m0
  exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
      (sub_ne_zero.mpr ad))).resolve_right (sub_ne_zero.mpr ac))).resolve_right
      (sub_ne_zero.mpr ab)

theorem two_clean_contrast_zero {h0 h1 G0 G1 : K} (hd : h0≠h1)
    (u : G0+G1=0) (v : G0*h0+G1*h1=0) : G0=0 ∧ G1=0 := by
  have h : G0*(h0-h1)=0 := by linear_combination v-h1*u
  have e : G0=0 := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hd)
  exact ⟨e,by simpa [e] using u⟩

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSquare

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSquare
#print axioms pair_square_masses
#print axioms two_ghost_grouped_reverse_zero
#print axioms four_marked_moments_kill_first
#print axioms two_clean_contrast_zero
