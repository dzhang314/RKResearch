import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Scalar receipts for the two paid alpha-one zero-multiplier crossings.
The rooted ingress and finite profile exclusions are provided separately. -/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroCubic

variable {K : Type*} [CommRing K]

/-- The adjacent fourth-clean read with no division by its diagonal or
the difference of ghost and ordinary clocks. -/
theorem adjacent_mark
    {d t z v r l m j p q : K}
    (hd : d*r=l) (ht : t=d*m-j)
    (hm : (d+z-v)*t=d^2*m) (hz : q*z=p) :
    (p-v*q)*(l*m-r*j)-q*l*j=0 := by
  have h : (z-v)*t=d*j := by
    linear_combination hm-d*ht
  have hh : (z-v)*(l*m-r*j)-l*j=0 := by
    linear_combination r*h-(z-v)*r*ht-((z-v)*m-j)*hd
  linear_combination q*hh-(l*m-r*j)*hz

def poly3 (a b c d x : K) : K := a+b*x+c*x^2+d*x^3

/-- Cubic divided difference at the first early ghost, homogenized in its
clock. There is no division by a mixed profile denominator. -/
theorem homogenized_difference
    {p q z : K} (h : p=q*z) (a b c d x : K) :
    (x-z)*((q^2*b+p*q*c+p^2*d)+(q^2*c+p*q*d)*x+q^2*d*x^2) =
      q^2*(poly3 a b c d x-poly3 a b c d z) := by
  rw [h]
  unfold poly3
  ring

theorem divided_difference_zero [IsDomain K]
    {p q z x a b c d : K} (hp : p=q*z) (hx : x≠z)
    (h : poly3 a b c d x=poly3 a b c d z) :
    (q^2*b+p*q*c+p^2*d)+(q^2*c+p*q*d)*x+q^2*d*x^2=0 := by
  have hh := homogenized_difference hp a b c d x
  rw [h,sub_self,mul_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hx)

/-- The forward rank-one read eliminates the middle ghost without assuming
its linear coefficient is live. -/
theorem eliminate_middle {g0 g1 x d0 d1 d2 : K}
    (hl : g0=x*g1) (hq : d0+d1*x+d2*x^2=0) :
    d0*g1^2+d1*g0*g1+d2*g0^2=0 := by
  rw [hl]
  linear_combination g1^2*hq

def det3 (u v w : K × K × K) : K :=
  u.1*(v.2.1*w.2.2-v.2.2*w.2.1)-u.2.1*(v.1*w.2.2-v.2.2*w.1)+
  u.2.2*(v.1*w.2.1-v.2.1*w.1)

/-- Linear dependence can be used before removing a possibly zero
commutator coefficient. -/
theorem scaled_affine_determinant (u v w : K × K × K) (k a b : K)
    (h0 : k*w.1=a*u.1+b*v.1)
    (h1 : k*w.2.1=a*u.2.1+b*v.2.1)
    (h2 : k*w.2.2=a*u.2.2+b*v.2.2) :
    k*det3 u v w=0 := by
  unfold det3
  linear_combination
    (u.2.1*v.2.2-u.2.2*v.2.1)*h0 +
    (u.2.2*v.1-u.1*v.2.2)*h1 + (u.1*v.2.1-u.2.1*v.1)*h2

theorem squared_first_diagonal [IsDomain K] {e j d r D J B : K}
    (hr : r≠0) (he : e*j= -(d^2*r)) (hg : e*D=0) (hJ : B*d=J) :
    J^2*D=0 := by
  by_cases hd : d=0
  · have h : J=0 := by simpa [hd] using hJ.symm
    simp [h]
  · have hh : e≠0 := by
      intro he0
      apply mul_ne_zero (pow_ne_zero 2 hd) hr
      simpa [he0] using he.symm
    have hD : D=0 := (mul_eq_zero.mp hg).resolve_left hh
    simp [hD]

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroCubic
