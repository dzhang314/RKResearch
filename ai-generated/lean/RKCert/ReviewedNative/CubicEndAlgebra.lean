module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.CubicEnd

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def endF (x : K) := (x-1)^2 * (8*x-5)
def endG (x : K) := 5-12*x+6*x^2

structure EndBounds (u v b : K) : Prop where
  sumLower : (5 : K)/4 ≤ u+v
  centerLower : -((3 : K)/5)*(u-v) ≤ b
  leftUpper : u < (11 : K)/12
  rightUpper : v < (11 : K)/12

/-- A rational sum of nonnegative terms removes all subinterval cases. -/
private theorem square_gap {s : K} (lo : (5 : K)/4 < s) (hi : s < (5 : K)/3) :
    0 < 3*(s-1)*((11 : K)/6-s)^2 - (5-3*s)*(s-2)^2*(4*s-5) := by
  let t : K := (12*s-15)/5
  have tpos : 0 < t := by dsimp [t]; linarith only [lo]
  have tlt : t < 1 := by dsimp [t]; linarith only [hi]
  have sep : 0 ≤ 1-t := sub_nonneg.mpr tlt.le
  have identity :
      3*(s-1)*((11 : K)/6-s)^2 - (5-3*s)*(s-2)^2*(4*s-5) =
        ((1-t)^2*(78*(1-2*t)^2 + 363*(1-t)^2 + 258*t^2) +
          404*t^3*(1-t) + 96*t^4)/1728 := by
    dsimp [t]
    ring
  rw [identity]
  have p0 : 0 ≤ (1-t)^2*(78*(1-2*t)^2 + 363*(1-t)^2 + 258*t^2) :=
    mul_nonneg (sq_nonneg _) (add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (by norm_num) (sq_nonneg _)))
      (mul_nonneg (by norm_num) (sq_nonneg _)))
  have p1 : 0 ≤ 404*t^3*(1-t) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg tpos.le _)) sep
  have p2 : 0 < 96*t^4 := mul_pos (by norm_num) (pow_pos tpos _)
  exact div_pos (add_pos_of_nonneg_of_pos (add_nonneg p0 p1) p2) (by norm_num)

/-- Only two reflected scalar identities are needed for the numerical
length and centered-coefficient bounds. -/
theorem end_bounds_of_reflected_coefficients {u v b : K}
    (u1 : u ≠ 1) (overlap : 1 < u+v) (orientation : 0 ≤ u-v)
    (linear : (10-6*(u+v))*b = (6*(u+v)-9)*(u-v))
    (paired : endF u + endF v + b*(endG u-endG v) = 0) :
    EndBounds u v b := by
  by_cases equal : u = v
  · have pe := paired
    rw [← equal, sub_self, mul_zero, add_zero] at pe
    have ez : endF u = 0 := by linarith only [pe]
    have ez' : (u-1)^2*(8*u-5) = 0 := ez
    have ueq : u = 5/8 := by
      have cut := (mul_eq_zero.mp ez').resolve_left (pow_ne_zero _ (sub_ne_zero.mpr u1))
      linarith only [cut]
    have veq : v = 5/8 := equal.symm.trans ueq
    have bz : b = 0 := by
      rw [ueq, veq] at linear
      norm_num at linear
      linarith only [linear]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [ueq, veq, bz]
  · let s := u+v
    let d := u-v
    let r := 5-3*s
    have hs : 1 < s := overlap
    have hd : 0 < d := lt_of_le_of_ne orientation (sub_ne_zero.mpr equal).symm
    have e1 : 2*r*b = (1-2*r)*d := by
      dsimp [r, s, d]
      linear_combination linear
    have e2 : (s-2)^2*(4*s-5) + (12*s-21)*d^2 + 12*(s-2)*d*b = 0 := by
      unfold endF endG at paired
      dsimp [s, d]
      linear_combination 2*paired
    have dCleared : 3*(s-1)*d^2 = r*(s-2)^2*(4*s-5) := by
      have ee :
        r*((s-2)^2*(4*s-5) + (12*s-21)*d^2 + 12*(s-2)*d*b) -
          6*(s-2)*d*(2*r*b-(1-2*r)*d) =
            r*(s-2)^2*(4*s-5)-3*(s-1)*d^2 := by
        dsimp [r]
        ring
      have zero : 0 = r*(s-2)^2*(4*s-5)-3*(s-1)*d^2 := by
        simpa only [e1, e2, sub_self, mul_zero] using ee
      exact (sub_eq_zero.mp zero.symm).symm
    have den : 0 < 3*(s-1) := mul_pos (by norm_num) (sub_pos.mpr hs)
    have prod : 0 < r*(4*s-5) := by
      by_contra! nonpos
      have no := mul_nonpos_of_nonpos_of_nonneg nonpos (sq_nonneg (s-2))
      have swap : (r*(4*s-5))*(s-2)^2 = 3*(s-1)*d^2 := by
        rw [dCleared]
        ring
      rw [swap] at no
      exact (not_lt_of_ge no) (mul_pos den (sq_pos_of_pos hd))
    have slo : (5 : K)/4 < s := by
      by_contra! no
      have rn : 0 ≤ r := by dsimp [r]; linarith only [no]
      have fn : 4*s-5 ≤ 0 := by linarith only [no]
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos rn fn)) prod
    have shi : s < (5 : K)/3 := by
      by_contra! no
      have rn : r ≤ 0 := by dsimp [r]; linarith only [no]
      have fn : 0 ≤ 4*s-5 := by linarith only [no]
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg rn fn)) prod
    have rp : 0 < r := by dsimp [r]; linarith only [shi]
    have rhi : r < (5 : K)/4 := by dsimp [r]; linarith only [slo]
    have bfit : 2*r*(b+((3 : K)/5)*d) = (1-((4 : K)/5)*r)*d := by
      calc
        _ = (2*r*b) + ((6 : K)/5)*r*d := by ring
        _ = (1-2*r)*d + ((6 : K)/5)*r*d := by rw [e1]
        _ = _ := by ring
    have bn : -((3 : K)/5)*d ≤ b := by
      have z : 0 ≤ 2*r*(b+((3 : K)/5)*d) := by
        rw [bfit]
        exact mul_nonneg (by linarith only [rhi]) hd.le
      have z' := (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0:K)<2) rp)).mp z
      linarith only [z']
    have dsq : d^2 < ((11 : K)/6 - s)^2 := by
      apply (mul_lt_mul_iff_right₀ den).mp
      rw [dCleared]
      exact sub_pos.mp (square_gap slo shi)
    have gap : 0 < (11 : K)/6 - s := by linarith only [shi]
    have dc : d < (11 : K)/6 - s := by
      by_contra! no
      exact (not_lt_of_ge (pow_le_pow_left₀ gap.le no 2)) dsq
    have up : u < (11 : K)/12 := by
      dsimp [s, d] at dc
      linarith only [dc]
    exact ⟨slo.le, bn, up, (sub_nonneg.mp orientation).trans_lt up⟩

/-- Coefficient-only form of the anchored quadratic bound and its
derivative. There are no polynomial, grid, or moment inputs here. -/
theorem quadratic_positive_of_anchor_cap {u S P x : K}
    (u0 : 0 < u) (up : u < (11 : K)/12)
    (mean : P = ((3 : K)/4)*u*S - ((3 : K)/5)*u^2)
    (cap : S-((3 : K)/4)*u ≤ (9 : K)/10 - ((11 : K)/100)*u)
    (hx : (14 : K)/15 ≤ x) :
    0 < x^2-S*x+P ∧ 0 < 2*x-S := by
  let B : K := 14/15
  let mu : K := ((3 : K)/4)*u
  let r : K := S-mu
  have mb : mu < B := by dsimp [mu, B]; linarith only [up]
  have rb : r < B := by dsimp [r, mu, B]; linarith only [cap, u0]
  have low :
      0 < (B-mu)*(B-(9 : K)/10+((11 : K)/100)*u) - ((3 : K)/80)*u^2 := by
    have chord :
        (B-mu)*(B-(9 : K)/10+((11 : K)/100)*u)-((3 : K)/80)*u^2 =
        (1-((12 : K)/11)*u)*(7/225) +
          (((12 : K)/11)*u)*(53/36000) + ((3 : K)/25)*u*((11 : K)/12-u) := by
      dsimp [B, mu]
      ring
    rw [chord]
    have pos : 0 < (((12 : K)/11)*u)*(53/36000) :=
      mul_pos (mul_pos (by norm_num) u0) (by norm_num)
    have non0 : 0 ≤ (1-((12 : K)/11)*u)*(7/225) :=
      mul_nonneg (by linarith only [up]) (by norm_num)
    have non1 : 0 ≤ ((3 : K)/25)*u*((11 : K)/12-u) :=
      mul_nonneg (mul_nonneg (by norm_num) u0.le) (sub_nonneg.mpr up.le)
    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos non0 pos) non1
  have HB : 0 < B^2-S*B+P := by
    have rel : B^2-S*B+P = (B-mu)*(B-r)-((3 : K)/80)*u^2 := by
      rw [mean]
      dsimp [r, mu]
      ring
    have cap' : r ≤ (9 : K)/10 - ((11 : K)/100)*u := cap
    have prod := mul_le_mul_of_nonneg_left
      (show B-(9 : K)/10+((11 : K)/100)*u ≤ B-r by linarith only [cap'])
      (sub_nonneg.mpr mb.le)
    rw [rel]
    exact low.trans_le (sub_le_sub_right prod _)
  have s2 : S < 2*B := by
    change S-mu < B at rb
    linarith only [mb, rb]
  have xB : B ≤ x := hx
  have gain : 0 ≤ (x-B)*(x+B-S) :=
    mul_nonneg (sub_nonneg.mpr xB) (by linarith only [xB, s2])
  have rel : x^2-S*x+P = (B^2-S*B+P)+(x-B)*(x+B-S) := by ring
  constructor
  · rw [rel]
    exact add_pos_of_pos_of_nonneg HB gain
  · linarith only [xB, s2]

end RKCert.ReviewedNative.CubicEnd
