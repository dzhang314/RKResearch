module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

public section

namespace RKResearch.Certified.ERK10RankThreePortTwoLabels

theorem singleton_pair
    (p q y v : ℚ) (q0 : q ≠ 0) (pq : p ≠ q)
    (h1 : y+p*v=q^2/2)
    (h2 : (2*p/3)*y+p^2*v=q^3/3)
    (h3 : (p^2/2)*y+p^3*v=q^4/4) : False := by
  have h : q^2*(p-q)^2/4=0 := by
    linear_combination -(p^2/2)*h1+(3*p/2)*h2-h3
  exact (div_ne_zero (mul_ne_zero (pow_ne_zero _ q0) (pow_ne_zero _ (sub_ne_zero.mpr pq)))
    (by decide : (4:ℚ) ≠ 0)) h

theorem repeat_first_clock
    (s a b : ℚ) (hs : s ≠ 0) (h1 : s ≠ 1) (h32 : 3*s-2 ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : -(3*s-2)/(6*a*(s-1))=s*(2*s-3)/(6*b*(s-1)))
    (hG : -(2*s-1)/(6*a)=s^2*(s-2)/(6*b*(3*s-2))) : False := by
  have hd : (-(3*s-2)/(6*a*(s-1)))*(s^2*(s-2)/(6*b*(3*s-2))) -
      (-(2*s-1)/(6*a))*(s*(2*s-3)/(6*b*(s-1))) =
      s*(s-1)/(12*a*b) := by
    field_simp [ha,hb,sub_ne_zero.mpr h1,h32]
    <;> ring
  rw [hA,hG,mul_comm (s*(2*s-3)/(6*b*(s-1))),sub_self] at hd
  exact (div_ne_zero (mul_ne_zero hs (sub_ne_zero.mpr h1))
    (mul_ne_zero (mul_ne_zero (by decide) ha) hb)) hd.symm

theorem repeat_second_clock
    (s a b : ℚ) (hs : s ≠ 0) (h1 : s ≠ 1) (h23 : 2*s-3 ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : s*(2*s-3)/(6*a*(s-1))=-(3*s-2)/(6*b*(s-1)))
    (hG : -s*(s-2)*(2*s-3)/(6*a)=-(2*s-1)/(6*b)) : False := by
  have hd : (s*(2*s-3)/(6*a*(s-1)))*(-(2*s-1)/(6*b)) -
      (-s*(s-2)*(2*s-3)/(6*a))*(-(3*s-2)/(6*b*(s-1))) =
      -(s*(s-1)*(2*s-3))/(12*a*b) := by
    field_simp [ha,hb,sub_ne_zero.mpr h1]
    <;> ring
  rw [hA,hG,mul_comm (-(3*s-2)/(6*b*(s-1))),sub_self] at hd
  exact (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hs (sub_ne_zero.mpr h1)) h23))
    (mul_ne_zero (mul_ne_zero (by decide) ha) hb)) hd.symm

end RKResearch.Certified.ERK10RankThreePortTwoLabels

#print axioms RKResearch.Certified.ERK10RankThreePortTwoLabels.singleton_pair
#print axioms RKResearch.Certified.ERK10RankThreePortTwoLabels.repeat_first_clock
#print axioms RKResearch.Certified.ERK10RankThreePortTwoLabels.repeat_second_clock
