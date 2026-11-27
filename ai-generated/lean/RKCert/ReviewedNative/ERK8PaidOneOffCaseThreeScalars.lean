module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffResiduals
public import RKCert.ReviewedNative.ERK8PaidOneOffCaseThreeCalibration

@[expose] public section

namespace RKResearch.Certified.Graded.OneOff.PaidProof

variable {K : Type*} [Field K] [EightUnits K]

def Lthree (a d x : K) : K := (a-2*d)*x+3*a*d

theorem three_q_off (a d v G : K) (vn : v≠0) :
    Qres a d (-2/3) (-a) (threeNu a d v)
      a G ((threeGam a/v)*(G*(G-baseAmp a))) 0 =
       -a*(a-2*d)*((G-baseAmp a)*(G-v))/(6*v) := by
  unfold Qres
  dsimp only [rowM1,rowM2,rowM3,threeNu,threeGam,baseAmp]
  simp only [mul_zero,add_zero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,vn]
  eight_ring K

theorem three_h_off (a d v G : K) (_dn : d≠0) (da : d≠a) (vn : v≠0) :
    Hres a d (threeHd a d) (threeGam a) (-2/3) (threeKap a d v)
      a G ((threeGam a/v)*(G*(G-baseAmp a))) 0 =
       a*(a+d)*((G-baseAmp a)*(G-v))/(6*v) := by
  unfold Hres
  dsimp only [rowM1,rowM2,threeHd,threeGam,threeKap,baseAmp]
  simp only [mul_zero,sub_zero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,_dn,sub_ne_zero.mpr da,vn]
  eight_ring K

theorem three_q_clean_d (a d v H : K) (an : a≠0) (vn : v≠0) (dm : 2*d-3*a≠0) :
    Qres a d (-2/3) (-a) (threeNu a d v) d 0 H ((2*v/a)*H) =
      d*(2*a-d)*(H-threeHd a d)/(3*(2*d-3*a)) := by
  unfold Qres
  dsimp only [rowM1,rowM2,rowM3,threeNu,threeHd]
  simp only [mul_zero,add_zero]
  generalize dEq : 2*d-3*a = Delta at dm ⊢
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,vn,dm]
  rw [←dEq]
  eight_ring K

theorem three_h_clean (a d v x : K) (_dn : d≠0) (da : d≠a) :
    Hres a d (threeHd a d) (threeGam a) (-2/3) (threeKap a d v) x 0 0 0 =
      -x^2*Lthree a d x/12 := by
  unfold Hres Lthree
  dsimp only [rowM1,rowM2,threeHd,threeGam,threeKap,baseAmp]
  simp only [mul_zero,add_zero,sub_zero]
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,_dn,sub_ne_zero.mpr da]
  eight_ring K

/-- The exact off-first linear/quadratic compatibility gate. -/
theorem three_linear_quadratic_exclusion (a d x : K) (an : a≠0) (dn : d≠0)
    (de : d≠2*a) (b : Btwo a d x=0) (l : Lthree a d x=0) : False := by
  unfold Btwo at b
  unfold Lthree at l
  have e : 9*a^2*d*(2*a-d)=0 := by
    linear_combination (norm := eight_ring K) ((a-2*d)^2)*b-((3*a-6*d)*x-4*a^2-5*a*d+8*d^2)*l
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by eight_num) (pow_ne_zero _ an)) dn)
    (sub_ne_zero.mpr (Ne.symm de)) e

end RKResearch.Certified.Graded.OneOff.PaidProof
