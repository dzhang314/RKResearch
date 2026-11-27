module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffResiduals
public import RKCert.ReviewedNative.ERK8PaidOneOffCaseTwoCalibration

@[expose] public section

namespace RKResearch.Certified.Graded.OneOff.PaidProof

variable {K : Type*} [Field K] [EightUnits K]

def Ltwo (a d x : K) : K := (2*a-d)*x-3*a*d

theorem two_q_off (a d v G : K) (an : a≠0) (dn : d≠0) (vn : v≠0) :
    Qres a d (twoLam a d) (twoMu a d) (twoNu a d v)
      a G ((twoGam a d/v)*(G*(G-baseAmp a))) (G*(G-baseAmp a)) =
       -a*(a-2*d)*((G-baseAmp a)*(G-v))/(6*v) := by
  unfold Qres
  dsimp only [rowM1,rowM2,rowM3,twoLam,twoMu,twoNu,twoGam,baseAmp]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn,vn]; eight_ring K

theorem two_q_clean_d (a d v H : K) (an : a≠0) :
    Qres a d (twoLam a d) (twoMu a d) (twoNu a d v) d 0 H 0 =
      -d*(2*a-d)*(H-twoHd a d)/(3*a) := by
  unfold Qres
  dsimp only [rowM1,rowM2,rowM3,twoLam,twoMu,twoNu,twoHd]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]; eight_ring K

theorem two_h_clean_d (a d v H : K) (an : a≠0) (dn : d≠0) (da : d≠a) :
    Hres a d (twoHd a d) (twoGam a d) (twoLam a d) (twoKap a d v) d 0 H 0 =
      -(a+d)*(H-twoHd a d)/3 := by
  unfold Hres
  dsimp only [rowM1,rowM2,twoHd,twoGam,twoLam,twoKap,baseAmp]
  simp only [mul_zero,add_zero,sub_zero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn,sub_ne_zero.mpr da]; eight_ring K

theorem two_h_clean (a d v x : K) (an : a≠0) (dn : d≠0) (da : d≠a) :
    Hres a d (twoHd a d) (twoGam a d) (twoLam a d) (twoKap a d v) x 0 0 0 =
      a*x^2*Ltwo a d x/(12*d) := by
  unfold Hres Ltwo
  dsimp only [rowM1,rowM2,twoHd,twoGam,twoLam,twoKap,baseAmp]
  simp only [mul_zero,add_zero,sub_zero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn,sub_ne_zero.mpr da]; eight_ring K

/-- Cleared resultant at the only actual on-first pair, with no
division by the leading coefficient of the linear polynomial. -/
theorem two_linear_quadratic_exclusion (a d x : K) (an : a≠0) (dn : d≠0)
    (ae : a≠2*d) (b : Btwo a d x=0) (l : Ltwo a d x=0) : False := by
  unfold Btwo at b
  unfold Ltwo at l
  have e : 9*a*d^2*(2*d-a)=0 := by
    linear_combination (norm := eight_ring K) ((2*a-d)^2)*b-((6*a-3*d)*x-8*a^2+5*a*d+4*d^2)*l
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by eight_num) an) (pow_ne_zero _ dn))
    (sub_ne_zero.mpr (Ne.symm ae)) e

end RKResearch.Certified.Graded.OneOff.PaidProof
