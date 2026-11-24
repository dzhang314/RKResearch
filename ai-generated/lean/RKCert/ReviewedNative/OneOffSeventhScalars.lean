module

public import RKCert.ReviewedNative.OneOffAnchoredRadau

@[expose] public section

/-! # Seventh-row residuals: small polynomial identities

These are the existing seventh-row formulas, in the normalized variable
H=Ag/a. A linear combination of the three paid power actions is used
instead of explicitly solving for each of three aggregate taps. No root
search or numerical interpolation is involved. All coefficient identities
below are checked by ordinary field/ring normalization.
-/
namespace RKResearch.Certified.Graded.OneOff.Seven
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

def hzero (d x : K) : K := x^2*(x-2*d)/(4*d)
def m1 (x H : K) : K := x^2/2+2*H
def m2 (d x H : K) : K := x^3/3+(4*d/3)*H
def m3 (d x H : K) : K := x^4/4+(2*d^2-d*x)*H

def jValue (d z x H : K) : K :=
  2*d*(d-x)*H + ((z-d)*m3 d x H-d*(3*z-2*d)*m2 d x H+2*d^2*z*m1 x H)/(4*d)

def vValue (d z x H : K) : K :=
  (3*d+z)*m3 d x H-(2*d^2+3*d*z)*m2 d x H+2*d^2*z*m1 x H-x^5/5

def paramT (d : K) : K := 2016*d^4-2240*d^3+840*d^2-120*d+5
def paramB (d : K) : K := 1008*d^3-896*d^2+252*d-24

def radauVal (x : K) : K := x*(x^4-20*x^3/9+5*x^2/3-10*x/21+5/126)
def jRadau (d : K) : K := 21*d^3/paramT d

theorem radauVal_eq (x : K) : radauVal x=(anchorRadau : K[X]).eval x := by
  simp only [radauVal,anchorRadau,radauQuartic,eval_mul,eval_X,eval_add,eval_monomial]
  ring

theorem radauVal_doubled (d : K) : radauVal (2*d)=d*paramT d/63 := by
  unfold radauVal paramT
  ring

/-- Numerators of the three coefficients of Q_J, all with the same
denominator. The subsequent three evaluation checks certify their
interpolation conditions, so the coefficient list has no trusted part. -/
def qJ0 (d z : K) : K :=
  8*d^2*(-13104*d^5*z+4032*d^4*z^2+14560*d^4*z-5040*d^3*z^2-5460*d^3*z+
    2100*d^2*z^2+840*d^2*z-5*d^2-360*d*z^2-40*d*z+20*z^2)
def qJ1 (d z : K) : K :=
  -20*d*(-6048*d^5*z+1512*d^4*z^2+6496*d^4*z-1904*d^3*z^2-2268*d^3*z+
    756*d^2*z^2+312*d^2*z-3*d^2-120*d*z^2-12*d*z+6*z^2)
def qJ2 (d z : K) : K :=
  -4*d^2*(4536*d^3*z+252*d^2*z^2-4480*d^2*z+1260*d*z-120*z+5)

def qJ (d z x : K) : K :=
  (qJ0 d z+qJ1 d z*x+qJ2 d z*x^2)/(12*z*(z-2*d)*paramT d)

def qV (d z x : K) : K := (4*d/5)*qJ d z x-(4*d/5)*(x^2-2*d^2)

def jResidual (d z x H : K) : K :=
  jValue d z x H-jRadau d*radauVal x-qJ d z x*H

def vResidual (d z x H : K) : K :=
  vValue d z x H-((4*d/5)*jRadau d)*radauVal x-qV d z x*H

theorem j_value_doubled (d z H : K) (dn : d≠0) :
    jValue d z (2*d) H=d^4/3-(4*d^2/3)*H := by
  unfold jValue m1 m2 m3
  field_simp [dn]
  ring

theorem j_coefficient_doubled (d : K) (tn : paramT d≠0) :
    jRadau d*radauVal (2*d)=d^4/3 := by
  rw [radauVal_doubled,jRadau]
  field_simp [tn]
  ring

set_option maxHeartbeats 2800000 in
theorem qJ_doubled (d z : K) (zn : z≠0) (zt : z≠2*d) (tn : paramT d≠0) :
    qJ d z (2*d)= -(4*d^2/3) := by
  unfold qJ
  field_simp [zn,sub_ne_zero.mpr zt,tn]
  unfold qJ0 qJ1 qJ2 paramT
  ring

set_option maxHeartbeats 2800000 in
theorem j_at_d (d z : K) (_dn : d≠0) (zn : z≠0) (zt : z≠2*d) (tn : paramT d≠0) :
    jResidual d z d (hzero d d)=0 := by
  unfold jResidual jValue hzero m1 m2 m3 jRadau radauVal qJ
  field_simp [_dn,zn,sub_ne_zero.mpr zt,tn]
  unfold qJ0 qJ1 qJ2 paramT
  ring

set_option maxHeartbeats 2800000 in
theorem j_at_z (d z : K) (dn : d≠0) (_zn : z≠0) (zt : z≠2*d) (tn : paramT d≠0) :
    jResidual d z z (hzero d z)=0 := by
  unfold jResidual jValue hzero m1 m2 m3 jRadau radauVal qJ
  field_simp [dn,_zn,sub_ne_zero.mpr zt,tn]
  unfold qJ0 qJ1 qJ2 paramT
  ring

theorem j_at_t (d z H : K) (dn : d≠0) (zn : z≠0) (zt : z≠2*d) (tn : paramT d≠0) :
    jResidual d z (2*d) H=0 := by
  rw [jResidual,j_value_doubled _ _ _ dn,j_coefficient_doubled _ tn,qJ_doubled _ _ zn zt tn]
  ring

set_option maxHeartbeats 1700000 in
theorem master_residual (d z x H : K) (dn : d≠0) :
    vResidual d z x H-(4*d/5)*jResidual d z x H =
      (x-2*d)*(x-z)*(4*d*H-x^2*(x-2*d))/5 := by
  unfold vResidual jResidual qV jValue vValue m1 m2 m3
  field_simp [dn]
  ring

end RKResearch.Certified.Graded.OneOff.Seven
