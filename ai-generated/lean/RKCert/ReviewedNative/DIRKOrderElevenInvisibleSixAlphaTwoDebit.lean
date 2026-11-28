import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Polynomial and scalar receipts for the actual alpha-two fourth
ordinary zero-diagonal gate and its two-ghost quintic crossing. -/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoDebit
variable {K : Type*} [CommRing K]

def det3 (a b c : K × K × K) : K :=
  a.1*(b.2.1*c.2.2-b.2.2*c.2.1)-b.1*(a.2.1*c.2.2-a.2.2*c.2.1)
     +c.1*(a.2.1*b.2.2-a.2.2*b.2.1)

def primitive4 (c0 c1 c2 : K) : K × K × K :=
  (-3*c0*c2, 3*(6*c0-c1*c2), 8*c1-3*c2^2)

def primitive5 (c0 c1 c2 : K) : K × K × K :=
  (-c0*(5*c1-2*c2^2), -2*c0*c2-5*c1^2+2*c1*c2^2,
   10*c0-7*c1*c2+2*c2^3)

def jacobiRem (c0 c1 c2 : K) : K × K × K :=
  (42*c0*c2+84*c0+1, -14*(3*c0-3*c1*c2-6*c1+1),
   -14*(3*c1-3*c2^2-6*c2-4))

def oldDet (c0 c1 c2 : K) : K :=
  630*c0^3*c2+1512*c0^3-210*c0^2*c1^2-168*c0^2*c1*c2+
  504*c0^2*c1-168*c0^2*c2^2-42*c0^2*c2+18*c0^2+56*c0*c1^2-
  14*c0*c1*c2^2-14*c0*c1*c2+3*c0*c2^3+4*c1^3-c1^2*c2^2

theorem primitive_determinant (c0 c1 c2 : K) :
    det3 (primitive4 c0 c1 c2) (primitive5 c0 c1 c2) (jacobiRem c0 c1 c2) =
      10*oldDet c0 c1 c2 := by
  unfold det3 primitive4 primitive5 jacobiRem oldDet
  ring

def j4 (v : K) : K := 42*v^4-84*v^3+56*v^2-14*v+1
def j5 (v : K) : K := (2*v-1)*(66*v^4-132*v^3+84*v^2-18*v+1)
def dj4 (v : K) : K := 168*v^3-252*v^2+112*v-14
def dj5 (v : K) : K := 660*v^4-1320*v^3+900*v^2-240*v+20
def repeatedClockFactor (v : K) : K :=
  2772*v^8-11088*v^7+18648*v^6-17136*v^5+9360*v^4-3096*v^3+604*v^2-64*v+3
def endpointFactor (v : K) : K := 66*v^4-120*v^3+72*v^2-16*v+1

theorem repeated_clock_identity (v : K) :
    dj5 v*j4 v-j5 v*dj4 v=2*repeatedClockFactor v := by
  unfold dj5 dj4 j5 j4 repeatedClockFactor
  ring

theorem endpoint_identity (v : K) :
    j5 v-j4 v=2*(v-1)*endpointFactor v := by
  unfold j5 j4 endpointFactor
  ring

theorem zero_diagonal_from_quintic [IsDomain K]
    {d C E μ : K} (hC : d^2*C=0) (hE : E+μ*C=0) (h : E≠0) : d=0 := by
  have hc : C≠0 := by
    intro he
    simpa [he, h] using hE
  by_contra hd
  exact mul_ne_zero (pow_ne_zero 2 hd) hc hC

/-- Coefficient remainder of a quadratic without dividing the quadratic leader. -/
theorem quad_remainder (w0 w1 w2 a0 a1 a2 y : K) :
    w2*(a0+a1*y+a2*y^2) - a2*(w0+w1*y+w2*y^2) =
      (w2*a0-a2*w0)+(w2*a1-a2*w1)*y := by ring

/-- Coefficient remainder of a cubic against the actual two-ghost quadratic. -/
theorem cubic_remainder (w0 w1 w2 c0 c1 c2 y : K) :
    w2^2*(y^3+c2*y^2+c1*y+c0) -
       (w2*y+c2*w2-w1)*(w0+w1*y+w2*y^2) =
      (c0*w2^2-c2*w0*w2+w0*w1)+(c1*w2^2-c2*w1*w2-w0*w2+w1^2)*y := by ring

theorem linear_pair_wedge (a0 a1 b0 b1 z w : K) :
    (a0+a1*z)*(b0+b1*w)-(a0+a1*w)*(b0+b1*z)=
       (w-z)*(a0*b1-a1*b0) := by ring

theorem other_d_root [IsDomain K] {a b c r r0 : K}
    (hr : a*r^2+b*r+c=0) (h0 : a*r0^2+b*r0+c=0)
    (hd : r≠r0) : a*(r+r0)=-b := by
  have hh : (r-r0)*(a*(r+r0)+b)=0 := by
    linear_combination hr-h0
  have hh' := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hd)
  linear_combination hh'

theorem basis_replacement [IsDomain K] {m0 m1 r0 r1 q0 q1 l t : K}
    (hq0 : q0=l*m0+t*r0) (hq1 : q1=l*m1+t*r1)
    (h : m0*q1-m1*q0≠0) :
    m0*r1-m1*r0≠0 := by
  intro e
  have hzero : m0*q1-m1*q0=0 := by
    linear_combination m0*hq1-m1*hq0+t*e
  exact h hzero

theorem commutator_multipliers_zero [IsDomain K] {m0 m1 r0 r1 t u : K}
    (h : m0*r1-m1*r0≠0) (h0 : t*m0=u*r0) (h1 : t*m1=u*r1) :
    t=0 ∧ u=0 := by
  have hT : t*(m0*r1-m1*r0)=0 := by
    linear_combination r1*h0-r0*h1
  have hU : u*(m0*r1-m1*r0)=0 := by
    linear_combination m1*h0-m0*h1
  exact ⟨(mul_eq_zero.mp hT).resolve_right h, (mul_eq_zero.mp hU).resolve_right h⟩

theorem next_ghost_diagonal [IsDomain K] {y V d tap : K}
    (ht : tap≠0) (hc : (y-V-d)*tap=0) :
    d=y-V := by
  have h := (mul_eq_zero.mp hc).resolve_right ht
  linear_combination -h

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoDebit
