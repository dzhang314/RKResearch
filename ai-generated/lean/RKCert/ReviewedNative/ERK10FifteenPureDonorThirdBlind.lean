import Mathlib.Tactic.Ring

namespace RKResearch.Certified.ERK10FifteenPureDonorThirdBlind

variable {R : Type*} [CommRing R]

variable (a d e : R)

def da : R := -4*a*(a-d)*(a-e)
def dt : R := a*(3*a-2*d)*(3*a-2*e)
def dd : R := 4*(d-a)*(2*d-3*a)*(d-e)

-- The x argument is twice a reverse ordinate.
def r96 (x : R) : R := x*(3*x^2-20*a*x+36*a^2)
def H960 (x : R) : R :=
  12*x^4-15*(5*a+2*d)*x^3+40*(3*a^2+5*a*d)*x^2-360*a^2*d*x
def K960 (x : R) : R := -3*x^4+25*a*x^3-60*a^2*x^2

def ca : R := (2*d-3*a)*r96 a (2*a)*da a d e
def ct : R := 2*(a-d)*r96 a (3*a)*dt a d e
def cd : R := a*r96 a (2*d)*dd a d e

def za : R :=
  9*d*e*(3*a-2*d)*(3*a-2*e)*(d-e)*(42*a^2-27*a*d-27*a*e+16*d*e)
def zt : R :=
  -16*d*e*(a-d)*(a-e)*(d-e)*(117*a^2-63*a*d-63*a*e+31*d*e)
def zd : R := -9*a^3*e*(a-e)*(3*a-2*e)*(15*a-11*e)
def ze : R := 9*a^3*d*(a-d)*(3*a-2*d)*(15*a-11*d)

def colCommon : R := 3840*a^5*(a-d)*(3*a-2*d)*(d-e)

def det3 (x0 x1 x2 y0 y1 y2 z0 z1 z2 : R) : R :=
  x0*(y1*z2-y2*z1)-x1*(y0*z2-y2*z0)+x2*(y0*z1-y1*z0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chronologicalCofactors :
  det3 (ct a d e) (cd a d e) 0
    (H960 a d (3*a)) (H960 a d (2*d)) (H960 a d (2*e))
    (K960 a (3*a)) (K960 a (2*d)) (K960 a (2*e))
     = colCommon a d e * za a d e ∧
  -(det3 (ca a d e) (cd a d e) 0
    (H960 a d (2*a)) (H960 a d (2*d)) (H960 a d (2*e))
    (K960 a (2*a)) (K960 a (2*d)) (K960 a (2*e)))
     = colCommon a d e * zt a d e ∧
  det3 (ca a d e) (ct a d e) 0
    (H960 a d (2*a)) (H960 a d (3*a)) (H960 a d (2*e))
    (K960 a (2*a)) (K960 a (3*a)) (K960 a (2*e))
     = colCommon a d e * zd a e ∧
  -(det3 (ca a d e) (ct a d e) (cd a d e)
    (H960 a d (2*a)) (H960 a d (3*a)) (H960 a d (2*d))
    (K960 a (2*a)) (K960 a (3*a)) (K960 a (2*d)))
     = colCommon a d e * ze a d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [det3, ca, ct, cd, r96, H960, K960, da, dt, dd,
                         colCommon, za, zt, zd, ze]
  all_goals ring

def gden : R := a*zd a e*dd a d e
def gnum : R :=
  -a^3*d*(5*(3*a-2*d)*za a d e*da a d e + 9*(d-a)*zt a d e*dt a d e)

def j0 : R :=
  za a d e * (-16*a^4) + zt a d e * (-27*a^4) +
  zd a e*(8*a*d^2*(d-3*a)) + ze a d*(8*a*e^2*(e-3*a))

def j1 : R :=
  za a d e*r96 a (2*a) + zt a d e*r96 a (3*a) +
  zd a e*r96 a (2*d) + ze a d*r96 a (2*e)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdBlindNumerator :
    6*d*(d-a)*(2*d-3*a)*gden a d e*j0 a d e +
        (gnum a d e-gden a d e*d^2*(4*a*d-9*a^2))*j1 a d e =
    -139968*a^8*d^2*e^2*(a-d)^3*(a-e)^2*(3*a-2*d)^3*(3*a-2*e)^2*
        (15*a-11*e)*(d-e)^2 := by
  simp only [gden, gnum, j0, j1, r96, da, dt, dd, za, zt, zd, ze]
  ring


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kRowNull : ca a d e*za a d e + ct a d e*zt a d e + cd a d e*zd a e = 0 := by
  simp only [ca, ct, cd, r96, za, zt, zd, da, dt, dd]
  ring

section Field

variable {K : Type*} [Field K]

theorem thirdGateScalarPairZero (a d e gammaD : K)
    (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (had : a-d ≠ 0) (hae : a-e ≠ 0)
    (htd : 3*a-2*d ≠ 0) (hte : 3*a-2*e ≠ 0) (hde : d-e ≠ 0)
    (hp : gden a d e * gammaD = gnum a d e)
    (hgate : 6*d*(d-a)*(2*d-3*a)*gden a d e*j0 a d e +
      (gnum a d e-gden a d e*d^2*(4*a*d-9*a^2))*j1 a d e = 0) :
    za a d e = 0 ∧ zt a d e = 0 := by
  have hcnum : (-(139968:K)) ≠ 0 := by
    rw [show (-(139968:K)) = -((2:K)^6*(3:K)^7) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))
  rw [thirdBlindNumerator] at hgate
  have hpref : (-(139968:K))*a^8*d^2*e^2*(a-d)^3*(a-e)^2*
      (3*a-2*d)^3*(3*a-2*e)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero hcnum (pow_ne_zero _ ha)) (pow_ne_zero _ hd)) (pow_ne_zero _ he))
      (pow_ne_zero _ had)) (pow_ne_zero _ hae)) (pow_ne_zero _ htd)) (pow_ne_zero _ hte)
  have htail := (mul_eq_zero.mp hgate).resolve_right (pow_ne_zero _ hde)
  have hh := (mul_eq_zero.mp htail).resolve_left hpref
  have hz : zd a e = 0 := by simp [zd,hh]
  let qa := (3*a-2*d)*za a d e*da a d e
  let qt := (d-a)*zt a d e*dt a d e
  have hca : -(a^3)*(16*qa+18*qt) = 0 := by
    have h0 := kRowNull a d e
    rw [hz, mul_zero, add_zero] at h0
    calc
      _ = ca a d e*za a d e + ct a d e*zt a d e := by
        simp only [qa, qt, ca, ct, r96]
        ring
      _ = 0 := h0
  have hpa : -(a^3)*d*(5*qa+9*qt) = 0 := by
    calc
      _ = gnum a d e := by
        simp only [qa, qt, gnum]
        ring
      _ = gden a d e*gammaD := hp.symm
      _ = 0 := by simp [gden,hz]
  have hna : -(a^3) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ha)
  have hc1 := (mul_eq_zero.mp hca).resolve_left hna
  have hp1 := (mul_eq_zero.mp hpa).resolve_left (mul_ne_zero hna hd)
  have h6 : (6:K) ≠ 0 := by
    rw [show (6:K) = (2:K)*(3:K) by ring]
    exact mul_ne_zero h2 h3
  have h9 : (9:K) ≠ 0 := by
    rw [show (9:K) = (3:K)*(3:K) by ring]
    exact mul_ne_zero h3 h3
  have ha6 : (6:K)*qa = 0 := by
    calc
      _ = (16*qa+18*qt)-2*(5*qa+9*qt) := by ring
      _ = 0 := by rw [hc1,hp1,mul_zero,sub_self]
  have hqa := (mul_eq_zero.mp ha6).resolve_left h6
  have hqt : qt = 0 := by
    have ht9 : (9:K)*qt = 0 := by simpa [hqa] using hp1
    exact (mul_eq_zero.mp ht9).resolve_left h9
  have h4 : (-4:K) ≠ 0 := by
    rw [show (-4:K) = -((2:K)*2) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero h2 h2)
  have hda : da a d e ≠ 0 := by
    unfold da
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h4 ha) had) hae
  have hdt : dt a d e ≠ 0 := by
    unfold dt
    exact mul_ne_zero (mul_ne_zero ha htd) hte
  have hda' : d-a ≠ 0 := by
    rw [show d-a = -(a-d) by ring]
    exact neg_ne_zero.mpr had
  exact ⟨(mul_eq_zero.mp ((mul_eq_zero.mp hqa).resolve_right hda)).resolve_left htd,
    (mul_eq_zero.mp ((mul_eq_zero.mp hqt).resolve_right hdt)).resolve_left hda'⟩

theorem thirdGateNoTwoMasses (a d e gammaD rr muA muT nuA nuT : K)
    (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (had : a-d ≠ 0) (hae : a-e ≠ 0)
    (htd : 3*a-2*d ≠ 0) (hte : 3*a-2*e ≠ 0) (hde : d-e ≠ 0)
    (hp : gden a d e * gammaD = gnum a d e)
    (hgate : 6*d*(d-a)*(2*d-3*a)*gden a d e*j0 a d e +
      (gnum a d e-gden a d e*d^2*(4*a*d-9*a^2))*j1 a d e = 0)
    (hmuA : muA ≠ 0) (hmuT : muT ≠ 0)
    (hactualA : (a-rr)*muA = nuA*za a d e)
    (hactualT : (3*a-2*rr)*muT = nuT*zt a d e) : False := by
  obtain ⟨hza,hzt⟩ := thirdGateScalarPairZero a d e gammaD h2 h3 ha hd he had hae
    htd hte hde hp hgate
  rw [hza,mul_zero] at hactualA
  rw [hzt,mul_zero] at hactualT
  have hA := (mul_eq_zero.mp hactualA).resolve_right hmuA
  have hT := (mul_eq_zero.mp hactualT).resolve_right hmuT
  apply ha
  calc
    a = (3*a-2*rr)-2*(a-rr) := by ring
    _ = 0 := by rw [hA,hT,mul_zero,sub_self]

end Field

end RKResearch.Certified.ERK10FifteenPureDonorThirdBlind

#print axioms RKResearch.Certified.ERK10FifteenPureDonorThirdBlind.chronologicalCofactors
#print axioms RKResearch.Certified.ERK10FifteenPureDonorThirdBlind.thirdBlindNumerator

#print axioms RKResearch.Certified.ERK10FifteenPureDonorThirdBlind.thirdGateNoTwoMasses
