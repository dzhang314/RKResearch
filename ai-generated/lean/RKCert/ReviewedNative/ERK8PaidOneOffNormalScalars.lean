module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffNormalCalibration

@[expose] public section

/-! # Two denominator-cleared residuals for the exact normal-form chart -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open scoped Matrix
variable {K : Type*} [Field K] [EightUnits K]

def normAH (d e x : K) : K := -4*d*(d*e+3*d*x-2*e^2)
def normQH (d e x : K) : K := 4*d*(-5*d*e+3*d*x+4*e^2-3*e*x)

def normAPoly (a d e x G H : K) : K :=
  normAH d e x*H-a*x^2*(3*d-2*e)*((d-2*e)*x+3*d*e)
    -2*a*(3*d-2*e)*G*(a*(d-2*e)+3*d*e)

def normQPoly (a d e x G H : K) : K :=
  normQH d e x*H-a*x^2*(3*d-2*e)*Btwo d e x-2*a*(3*d-2*e)*G*Btwo d e a

set_option maxHeartbeats 850000 in
theorem normal_a_scale (a d e x G H : K)
    (an : a≠0) (dn : d≠0) (_en : e≠0) (ed : e≠d) (dnorm : 3*d-2*e≠0) :
    12*d*(3*d-2*e)*
      (normalHSource a d e (twoHd a d) (normHe a d e)
        (rowM1 x G) (rowM2 a (twoLam a d) x G H) H - normKap d e*((x-d)*H))
      = normAPoly a d e x G H := by
  unfold normAPoly normAH
  dsimp only [normalHSource,twoHd,normHe,rowM1,rowM2,twoLam,normKap,baseAmp]
  generalize hD : 3*d-2*e=DD at dnorm ⊢
  generalize hE : e-d=EE
  have ee : EE≠0 := hE ▸ sub_ne_zero.mpr ed
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn,_en,dnorm,ee]
  rw [←hD,←hE]
  eight_ring K

set_option maxHeartbeats 750000 in
theorem normal_q_scale (a d e x G H : K) (an : a≠0) (dnorm : 3*d-2*e≠0) :
    12*a*(3*d-2*e)*
      (normalCubSource a d e (rowM1 x G) (rowM2 a (twoLam a d) x G H) H -
          rowM3 a (twoMu a d) (normNu a d e) x G H ((x-d)*H))
      = normQPoly a d e x G H := by
  unfold normQPoly normQH Btwo
  dsimp only [normalCubSource,rowM1,rowM2,rowM3,twoLam,twoMu,normNu,baseAmp]
  generalize hD : 3*d-2*e=DD at dnorm ⊢
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dnorm]
  rw [←hD]
  eight_ring K

/-- The clean-clock resultant is a direct combination of the two
checked residuals, with no division by their coefficients of H. -/
theorem normal_clean_clocks (a d e x H : K)
    (an : a≠0) (dn : d≠0) (dm : 3*d-2*e≠0)
    (A : normAPoly a d e x 0 H=0) (Q : normQPoly a d e x 0 H=0) :
    x=0 ∨ x=d ∨ x=e := by
  have z : 36*a*d^2*x^2*(x-d)*(3*d-2*e)*(x-e)^2=0 := by
    simp only [normAPoly,normQPoly,normAH,normQH,Btwo] at A Q
    linear_combination (norm := eight_ring K) (-4*d*(d*e+3*d*x-2*e^2))*Q-(4*d*(-5*d*e+3*d*x+4*e^2-3*e*x))*A
  by_contra! ne
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by eight_num) an) (pow_ne_zero 2 dn)) (pow_ne_zero 2 ne.1))
    (sub_ne_zero.mpr ne.2.1)) dm) (pow_ne_zero 2 (sub_ne_zero.mpr ne.2.2)) z

theorem normal_clean_at_zero (a d e H : K) (dn : d≠0) (en : e≠0)
    (A : normAPoly a d e 0 0 H=0) (Q : normQPoly a d e 0 0 H=0) : H=0 := by
  simp only [normAPoly,normQPoly,normAH,normQH,Btwo] at A Q
  have z : (12*d^2*e)*H=0 := by linear_combination (norm := eight_ring K) 2*A-Q
  exact (mul_eq_zero.mp z).resolve_left
    (mul_ne_zero (mul_ne_zero (by eight_num) (pow_ne_zero 2 dn)) en)

theorem normal_clean_at_d (a d e H : K) (dn : d≠0) (dm : 3*d-2*e≠0)
    (A : normAPoly a d e d 0 H=0) (Q : normQPoly a d e d 0 H=0) : H=twoHd a d := by
  simp only [normAPoly,normQPoly,normAH,normQH,Btwo] at A Q
  have z : (3*d^2*(3*d-2*e))*(4*H+a*d^2)=0 := by linear_combination (norm := eight_ring K) -2*A+Q
  have h := (mul_eq_zero.mp z).resolve_left
    (mul_ne_zero (mul_ne_zero (by eight_num) (pow_ne_zero 2 dn)) dm)
  linear_combination (norm := eight_ring K) (1/4:K)*h

theorem normal_clean_at_e (a d e H : K) (dn : d≠0) (en : e≠0) (ex : e≠2*d)
    (Q : normQPoly a d e e 0 H=0) : H=normHe a d e := by
  unfold normQPoly normQH Btwo at Q
  have z : (-e*(2*d-e))*(4*d*H+a*e^2*(3*d-2*e))=0 := by linear_combination (norm := eight_ring K) Q
  have h := (mul_eq_zero.mp z).resolve_left
    (mul_ne_zero (neg_ne_zero.mpr en) (sub_ne_zero.mpr (Ne.symm ex)))
  have den : (4:K)*d≠0 := mul_ne_zero (by eight_num) dn
  apply (eq_div_iff den).mpr
  linear_combination (norm := eight_ring K) h

theorem normal_off_at_a (a d e H : K) (dn : d≠0) (en : e≠0)
    (dm : 3*d-2*e≠0) (ex : e≠2*d)
    (A : normAPoly a d e a (baseAmp a) H=0)
    (Q : normQPoly a d e a (baseAmp a) H=0) : H=0 := by
  simp only [normAPoly,normQPoly,normAH,normQH,Btwo,baseAmp] at A Q
  have z : (4*d*e*(3*d-2*e)*(e-2*d))*H=0 := by linear_combination (norm := eight_ring K) d*Q+(d-e)*A
  exact (mul_eq_zero.mp z).resolve_left (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by eight_num) dn) en) dm) (sub_ne_zero.mpr ex))

end RKResearch.Certified.Graded.OneOff.PaidProof
