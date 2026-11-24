module

public import RKCert.ERKOrderNineOneOffResiduals
public import RKCert.ERKOrderNineOneOffCaseTwoCalibration

@[expose] public section

namespace RKCert.Paired.OneOff

variable {K : Type*} [Field K] [CharZero K]

def Ltwo (a d x : K) : K := (2*a-d)*x-3*a*d

theorem two_q_off (a d v G : K) (an : a≠0) (dn : d≠0) (vn : v≠0) :
    Qres a d (twoLam a d) (twoMu a d) (twoNu a d v)
      a G ((twoGam a d/v)*(G*(G-baseAmp a))) (G*(G-baseAmp a)) =
       -a*(a-2*d)*((G-baseAmp a)*(G-v))/(6*v) := by
  unfold Qres
  dsimp only [rowM1,rowM2,rowM3,twoLam,twoMu,twoNu,twoGam,baseAmp]
  field_simp [an,dn,vn] <;> ring

theorem two_q_clean_d (a d v H : K) (an : a≠0) :
    Qres a d (twoLam a d) (twoMu a d) (twoNu a d v) d 0 H 0 =
      -d*(2*a-d)*(H-twoHd a d)/(3*a) := by
  unfold Qres
  dsimp only [rowM1,rowM2,rowM3,twoLam,twoMu,twoNu,twoHd]
  field_simp [an] <;> ring

theorem two_h_clean_d (a d v H : K) (an : a≠0) (dn : d≠0) (da : d≠a) :
    Hres a d (twoHd a d) (twoGam a d) (twoLam a d) (twoKap a d v) d 0 H 0 =
      -(a+d)*(H-twoHd a d)/3 := by
  unfold Hres
  dsimp only [rowM1,rowM2,twoHd,twoGam,twoLam,twoKap,baseAmp]
  simp only [mul_zero,zero_add,add_zero,sub_zero]
  field_simp [an,dn,sub_ne_zero.mpr da] <;> ring

theorem two_h_clean (a d v x : K) (an : a≠0) (dn : d≠0) (da : d≠a) :
    Hres a d (twoHd a d) (twoGam a d) (twoLam a d) (twoKap a d v) x 0 0 0 =
      a*x^2*Ltwo a d x/(12*d) := by
  unfold Hres Ltwo
  dsimp only [rowM1,rowM2,twoHd,twoGam,twoLam,twoKap,baseAmp]
  simp only [mul_zero,zero_add,add_zero,sub_zero]
  field_simp [an,dn,sub_ne_zero.mpr da] <;> ring

/-- Cleared resultant at the only actual on-first pair, with no
division by the leading coefficient of the linear polynomial. -/
theorem two_linear_quadratic_exclusion (a d x : K) (an : a≠0) (dn : d≠0)
    (ae : a≠2*d) (b : Btwo a d x=0) (l : Ltwo a d x=0) : False := by
  unfold Btwo at b
  unfold Ltwo at l
  have e : 9*a*d^2*(2*d-a)=0 := by
    linear_combination ((2*a-d)^2)*b-((6*a-3*d)*x-8*a^2+5*a*d+4*d^2)*l
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) an) (pow_ne_zero _ dn))
    (sub_ne_zero.mpr (Ne.symm ae)) e

end RKCert.Paired.OneOff
