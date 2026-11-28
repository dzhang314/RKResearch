import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Scalar gates for the normalized live cubic DIRK11/13 chart.
The ingress from actual rooted order and the finite-algebra arithmetic
are documented separately. -/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixCubicLiveCompactProjection

section Scalar
variable {K : Type*} [CommRing K]

def f0 (V c0 : K) : K := -3*V^2*c0^2

def f1 (V c0 c1 c2 : K) : K :=
  -6*V^2*c0*c2 + 2*V^2*c1^2 - 3*V*c0*c1 + c0^2

def f2 (V c0 c1 c2 : K) : K :=
  8*V^2*c1 - 3*V^2*c2^2 - 6*V*c0 + V*c1*c2 - c0*c2

def f3 (V c2 : K) : K := 2*V*(4*V+c2)

def F (V c0 c1 c2 s : K) : K :=
  f0 V c0 + f1 V c0 c1 c2*s + f2 V c0 c1 c2*s^2 + f3 V c2*s^3

def F' (V c0 c1 c2 s : K) : K :=
  f1 V c0 c1 c2 + 2*f2 V c0 c1 c2*s + 3*f3 V c2*s^2

def A0 (V c0 c1 c2 s : K) : K :=
  15*V*c0^3 + (10*V*c0*c1^2 - 5*c0^2*c1)*s +
    (-22*V*c0*c1 - 15*V*c0*c2^2 + 21*c0^2 + 5*c0*c1*c2)*s^2 +
    (-36*V*c0 - 21*c0*c2)*s^3 + 48*V*c2*s^4

def A1 (V c0 c1 c2 s : K) : K :=
  -10*V*c0^2*c1 + 5*c0^3 + (11*V*c0^2 - 5*c0^2*c2)*s +
    31*V*c0*c2*s^2 + (-16*V*c1 + 16*c0)*s^3 - 32*V*s^4

def UNum (V c0 c1 c2 s : K) : K := s*((c2+4*V)*s+2*V*c1-c0)
def UDen (V c0 c2 s : K) : K := V*(c0+c2*s)
def H (V c0 c1 c2 : K) : K := 2*V*c0-V*c1*c2+c0*c2

theorem reduced_affine_identity (V c0 c1 c2 s : K) :
    A1 V c0 c1 c2 s * UNum V c0 c1 c2 s +
       A0 V c0 c1 c2 s * UDen V c0 c2 s =
       (-5*c0^2+5*c0*c2*s-16*s^3) * F V c0 c1 c2 s := by
  unfold A1 A0 UNum UDen F f0 f1 f2 f3
  ring

theorem contact_value (V c0 c1 c2 : K) :
    c2^3*f0 V c0 + (-c0)*c2^2*f1 V c0 c1 c2 +
      (-c0)^2*c2*f2 V c0 c1 c2 + (-c0)^3*f3 V c2 =
    -2*c0*(H V c0 c1 c2)^2 := by
  unfold H f0 f1 f2 f3
  ring

theorem contact_derivative (V c0 c1 c2 : K) :
    c2^2*f1 V c0 c1 c2 + 2*(-c0)*c2*f2 V c0 c1 c2 +
      3*(-c0)^2*f3 V c2 =
    H V c0 c1 c2 * (12*V*c0-2*V*c1*c2+3*c0*c2) := by
  unfold H f1 f2 f3
  ring

theorem contact_forces_double [IsDomain K] {V c0 c1 c2 s : K}
    (h2 : (2 : K) ≠ 0) (hc0 : c0 ≠ 0) (hF : F V c0 c1 c2 s = 0)
    (hs : c0+c2*s=0) :
    F' V c0 c1 c2 s = 0 := by
  have hc2 : c2 ≠ 0 := by
    intro hz
    simp [hz, hc0] at hs
  have hs' : c2*s = -c0 := by linear_combination hs
  have hv : c2^3*F V c0 c1 c2 s = -2*c0*(H V c0 c1 c2)^2 := by
    calc
      c2^3*F V c0 c1 c2 s =
        c2^3*f0 V c0 + (c2*s)*c2^2*f1 V c0 c1 c2 +
          (c2*s)^2*c2*f2 V c0 c1 c2 + (c2*s)^3*f3 V c2 := by
        unfold F
        ring
      _ = _ := by rw [hs', contact_value]
  have hH : H V c0 c1 c2 = 0 := by
    by_contra hn
    rw [hF, mul_zero] at hv
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hc0) (pow_ne_zero 2 hn)) hv.symm
  have hd : c2^2*F' V c0 c1 c2 s = 0 := by
    calc
      c2^2*F' V c0 c1 c2 s =
        c2^2*f1 V c0 c1 c2 + 2*(c2*s)*c2*f2 V c0 c1 c2 +
          3*(c2*s)^2*f3 V c2 := by
        unfold F'
        ring
      _ = _ := by rw [hs', contact_derivative, hH, zero_mul]
  exact (mul_eq_zero.mp hd).resolve_left (pow_ne_zero 2 hc2)

theorem reduced_affine_actual [IsDomain K] {V c0 c1 c2 s r : K}
    (hF : F V c0 c1 c2 s = 0)
    (ha : A1 V c0 c1 c2 s*r+A0 V c0 c1 c2 s=0)
    (ha1 : A1 V c0 c1 c2 s≠0) :
    UDen V c0 c2 s*r=UNum V c0 c1 c2 s := by
  have hb := reduced_affine_identity V c0 c1 c2 s
  rw [hF, mul_zero] at hb
  have hh : A1 V c0 c1 c2 s * (UDen V c0 c2 s*r-UNum V c0 c1 c2 s)=0 := by
    linear_combination UDen V c0 c2 s * ha - hb
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ha1)

def cubic (a b c d x : K) : K := a+b*x+c*x^2+d*x^3
def dd (b c d z w : K) : K := b+c*(z+w)+d*(z^2+z*w+w^2)
def wedge (a b u v : K) : K := a*v-b*u

theorem pair_wedge_sym (u0 u1 u2 u3 q0 q1 q2 q3 z w : K) :
    cubic u0 u1 u2 u3 z * dd q1 q2 q3 z w -
      cubic q0 q1 q2 q3 z * dd u1 u2 u3 z w =
    wedge u0 u1 q0 q1 + (z+w)*wedge u0 u2 q0 q2 +
      ((z+w)^2-z*w)*wedge u0 u3 q0 q3 + z*w*wedge u1 u2 q1 q2 +
      (z+w)*(z*w)*wedge u1 u3 q1 q3 + (z*w)^2*wedge u2 u3 q2 q3 := by
  unfold cubic dd wedge
  ring

theorem pair_vieta_actual [IsDomain K] {a b c z w : K}
    (hz : a+b*z+c*z^2=0) (hw : a+b*w+c*w^2=0) (hzw : z≠w) :
    c*(z+w)= -b ∧ c*(z*w)=a := by
  have hh : (z-w)*(b+c*(z+w))=0 := by linear_combination hz-hw
  have hh' := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hzw)
  constructor
  · linear_combination hh'
  · linear_combination z*hh'-hz

theorem pair_wedge_compact (u0 u1 u2 u3 q0 q1 q2 q3 : K)
    {a b c z w : K} (hsum : c*(z+w)= -b) (hprod : c*(z*w)=a) :
    c^2*(cubic u0 u1 u2 u3 z * dd q1 q2 q3 z w -
      cubic q0 q1 q2 q3 z * dd u1 u2 u3 z w) =
    c^2*wedge u0 u1 q0 q1 - b*c*wedge u0 u2 q0 q2 +
      (b^2-a*c)*wedge u0 u3 q0 q3 + a*c*wedge u1 u2 q1 q2 -
      a*b*wedge u1 u3 q1 q3 + a^2*wedge u2 u3 q2 q3 := by
  rw [pair_wedge_sym]
  calc
    _ = c^2*wedge u0 u1 q0 q1 +
      (c*(z+w))*c*wedge u0 u2 q0 q2 +
      ((c*(z+w))^2-(c*(z*w))*c)*wedge u0 u3 q0 q3 +
      (c*(z*w))*c*wedge u1 u2 q1 q2 +
      (c*(z+w))*(c*(z*w))*wedge u1 u3 q1 q3 +
      (c*(z*w))^2*wedge u2 u3 q2 q3 := by ring
    _ = _ := by rw [hsum,hprod]; ring

theorem four_prefix_linear (j0 j1 j2 : K) {a b c z w : K}
    (hsum : c*(z+w)= -b) (hprod : c*(z*w)=a) :
    c*(j2-(z+w)*j1+z*w*j0) = c*j2+b*j1+a*j0 := by
  linear_combination -j1*hsum+j0*hprod

theorem linear_ghost_substitute {a b c d g0 g1 z : K}
    (h : g0+g1*z=0) :
    a*g1^3+b*(-g0)*g1^2+c*(-g0)^2*g1+d*(-g0)^3 = g1^3*cubic a b c d z := by
  have h' : -g0=g1*z := by linear_combination -h
  rw [h']
  unfold cubic
  ring

end Scalar
end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixCubicLiveCompactProjection
