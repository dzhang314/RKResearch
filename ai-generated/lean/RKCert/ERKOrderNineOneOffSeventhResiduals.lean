module

public import RKCert.ERKOrderNineOneOffSeventhScalars
public import RKCert.ERKOrderNineOneOffTerminalShape

@[expose] public section

/-! # The exact seventh-row cubic substitution, endpoint residual and slope
Only the fixed printed identities are checked. No resultant search or
isolated root computation is used for this step. -/
namespace RKCert.Paired.OneOff.Seven
open Polynomial RKCert.GoodPrimeDense

variable {K : Type*} [Field K] [CharZero K]

def paramU (d : K) : K := 168*d^3-112*d^2+21*d-1
def theta (d : K) : K := d*(336*d^3-280*d^2+70*d-5)
def mixedK (d z x : K) : K := paramB d*x*z+x+z-2*d

def endP (d x : K) : K := x*(x-2*d)*endpointF d x/(2*(1-2*d)*paramU d)

def endL (d z x : K) : K :=
  ((4*endpointF d d)/d)*(x-z)/((d-z)*(2*(1-2*d)*paramU d)) -
  ((4*d*endpointF d z)/(z*(z-2*d)))*(x-d)/((z-d)*(2*(1-2*d)*paramU d))

theorem endpointF_formula (d x : K) :
    endpointF d x=5-70*d+280*d^2-336*d^3+
      (-35+560*d-2408*d^2+3024*d^3)*x+
      (70-1204*d+5432*d^2-7056*d^3)*x^2+
      (-42+756*d-3528*d^2+4704*d^3)*x^3 := by
  simp [endpointF,readGrid,endpointFData,GoodPrimeDense.read]
  ring

set_option maxHeartbeats 4600000 in
theorem cubic_j_residual (d z x : K)
    (dn : d≠0) (zn : z≠0) (zt : z≠2*d) (tn : paramT d≠0) :
    jResidual d z x (hzero d x)=
      5*d*x*(x-2*d)*(x-d)*(x-z)*mixedK d z x/(12*z*(z-2*d)*paramT d) := by
  unfold jResidual jValue hzero m1 m2 m3 jRadau radauVal qJ
  field_simp [dn,zn,sub_ne_zero.mpr zt,tn]
  unfold qJ0 qJ1 qJ2 paramT mixedK paramB
  ring

set_option maxHeartbeats 3600000 in
theorem j_slope_at_z (d z H₁ H₂ : K)
    (dn : d≠0) (zn : z≠0) (zt : z≠2*d) (tn : paramT d≠0) :
    jResidual d z z H₂-jResidual d z z H₁ =
      (-5*endpointG d z/(12*z*paramT d))*(H₂-H₁) := by
  unfold jResidual jValue m1 m2 m3 qJ
  rw [endpointG_formula]
  field_simp [dn,zn,sub_ne_zero.mpr zt,tn]
  unfold qJ0 qJ1 qJ2 paramT
  ring

set_option maxHeartbeats 5200000 in
theorem cubic_endpoint_residual (d z x : K)
    (dn : d≠0) (zn : z≠0) (zd : z≠d) (zt : z≠2*d)
    (t1 : 2*d≠1) (un : paramU d≠0) :
    endP d x+(x-2*d)*endL d z x*hzero d x =
      x*(x-2*d)*(x-d)*(x-z)*
        (theta d*mixedK d z x-paramU d*paramT d*x*z)/
        (2*d^2*z*(z-2*d)*(2*d-1)*paramU d) := by
  unfold endP endL hzero
  rw [show 2*d-1= -(1-2*d) by ring]
  field_simp [dn,zn,sub_ne_zero.mpr (Ne.symm zd),sub_ne_zero.mpr zd,
    sub_ne_zero.mpr zt,sub_ne_zero.mpr (Ne.symm t1),un]
  simp only [endpointF_formula]
  unfold theta mixedK paramB paramU paramT
  ring

end RKCert.Paired.OneOff.Seven
