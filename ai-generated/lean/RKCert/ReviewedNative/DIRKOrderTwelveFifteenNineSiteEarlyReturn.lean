import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact normalized scalar elimination gates for the single live pair in
    the nine-site weighted reverse DIRK12 equality frame. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteEarlyReturn

variable {K : Type*} [Field K] [CharZero K]

/-- Two genuine moment reads at a return to a pair of uniform normalized
    cubic amplitudes. -/
theorem uniformReturn (d v td tv : K) (hd : d ≠ 0) (hv : v ≠ 0) (hvd : v-d ≠ 0)
    (h₁ : d*td+v*tv=d^2/2) (h₂ : d^2*td+v^2*tv=d^3/2) :
    tv=0 ∧ td=d/2 := by
  have h : (v*(v-d))*tv=0 := by linear_combination h₂ - d*h₁
  have ht : tv=0 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hv hvd)
  have hp : d*(td-d/2)=0 := by linear_combination h₁ - v*ht
  exact ⟨ht, sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hd)⟩

omit [CharZero K] in
/-- If a new live numerical zero row has only the nonzero live source labels
    d and v, its first two scalar moments kill their aggregate taps. -/
theorem zeroReceiver (d v td tv : K) (hd : d ≠ 0) (hv : v ≠ 0) (hvd : v-d ≠ 0)
    (h₁ : d*td+v*tv=0) (h₂ : d^2*td+v^2*tv=0) :
    tv=0 ∧ td=0 := by
  have h : (v*(v-d))*tv=0 := by linear_combination h₂ - d*h₁
  have ht : tv=0 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hv hvd)
  have hp : d*td=0 := by linear_combination h₁ - v*ht
  exact ⟨ht, (mul_eq_zero.mp hp).resolve_left hd⟩

def aCoef (r t : K) : K :=
  -3*(r-1)*(4*r^2*t+r^2-13*r*t+r+4*t)/(5*(2*r-1))
def bCoef (r t : K) : K :=
  t^3*(5*r*t-10*r-3*t^2+5*t)/60
def q₂ (r t : K) : K :=
  -3*(r-2)*(r-1)/(t*(r-t)*(t-1))
def q₁ (r t : K) : K :=
  (4*r^3*t^2-15*r^3*t+3*r^3+6*r^2*t^2+15*r^2*t+3*r^2
    -9*r*t^3+6*r*t^2-15*r*t+4*t^2)/(12*(r-2)*(r-t)*(2*r-1)*(t-1))
def q₀ (r t : K) : K :=
  -t^3*(r^2*t^2-3*r^2*t+6*r^2-r*t^2-3*r*t+t^2)/
    (432*(r-2)*(r-1)*(r-t)*(t-1))
def ratio (r t : K) : K :=
  (r^2-4*r+1)*t+r*(r+1)

/-- Exact linear-quadratic resultant over its literal guarded field. -/
theorem resultantIdentity (r t : K) (hr₁ : r-1 ≠ 0) (hr₂ : r-2 ≠ 0)
    (hrh : 2*r-1 ≠ 0) (ht₀ : t ≠ 0) (ht₁ : t-1 ≠ 0) (hrt : r-t ≠ 0) :
    q₂ r t*(bCoef r t)^2 - q₁ r t*aCoef r t*bCoef r t + q₀ r t*(aCoef r t)^2 =
      -3*t^3*(r-1)*(r-t)*(t-1)*(ratio r t)^2/(100*(r-2)*(2*r-1)^2) := by
  unfold q₂ q₁ q₀ aCoef bCoef ratio
  generalize hz : 2*r-1 = z at hrh ⊢
  field_simp [hr₁, hr₂, hrh, ht₀, ht₁, hrt]
  rw [← hz]
  ring

/-- The actual scalar resultant conclusion does not divide by the leading
    coefficient of the linear equation. -/
theorem thirdRatio (r t h : K) (hr₁ : r-1 ≠ 0) (hr₂ : r-2 ≠ 0)
    (hrh : 2*r-1 ≠ 0) (ht₀ : t ≠ 0) (ht₁ : t-1 ≠ 0) (hrt : r-t ≠ 0)
    (e : aCoef r t*h+bCoef r t=0)
    (f : q₂ r t*h^2+q₁ r t*h+q₀ r t=0) :
    ratio r t = 0 := by
  have hb : bCoef r t = -aCoef r t*h := by linear_combination e
  have he : q₂ r t*(bCoef r t)^2 - q₁ r t*aCoef r t*bCoef r t +
      q₀ r t*(aCoef r t)^2 = 0 := by
    rw [hb]
    linear_combination (aCoef r t)^2*f
  rw [resultantIdentity r t hr₁ hr₂ hrh ht₀ ht₁ hrt] at he
  have hn : (100:K)*(r-2)*(2*r-1)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hr₂) (pow_ne_zero 2 hrh)
  have hn' := (div_eq_iff hn).mp he
  rw [zero_mul] at hn'
  have hc : (-3:K)*t^3*(r-1)*(r-t)*(t-1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 3 ht₀)) hr₁) hrt) ht₁
  have hh := (mul_eq_zero.mp hn').resolve_left hc
  by_contra hno
  exact pow_ne_zero 2 hno hh

#print axioms uniformReturn
#print axioms zeroReceiver
#print axioms resultantIdentity
#print axioms thirdRatio

end RKResearch.Certified.Graded.OrderTwelveFifteen.NineSiteEarlyReturn
