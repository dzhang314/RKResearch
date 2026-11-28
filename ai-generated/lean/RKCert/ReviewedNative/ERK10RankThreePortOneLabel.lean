module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

public section

namespace RKResearch.Certified.ERK10RankThreePortOneLabel

/-- The sole regular nonduplicate equal-defect row can occur at the
doubled clean clock. This is the homogeneous stage-five gate. -/
theorem equal_defect_fifth_clock
    (r e T U J : ℚ) (r0 : r ≠ 0) (r1 : r ≠ 1)
    (r32 : 2*r ≠ 3) (j0 : J ≠ 0)
    (h1 : T+U+r*J=0)
    (h2 : (2/3)*T+U+r^2*J=0)
    (h3 : (3-2*r)*(U+r^2*(3-2*r)*J)=2*(e-1)*T)
    (h4 : (3-2*r)*(U+r^3*J)+(3-2*r+(r-1)*(e-1))*T/2=0) :
    r=2 ∧ e=2 := by
  have ht : T=3*r*(r-1)*J := by linear_combination 3*h1-3*h2
  have hu : U=-r*(3*r-2)*J := by linear_combination h1-ht
  have h3' : (2*J*r*(r-1))*(-3*e+2*r^2-r)=0 := by
    linear_combination h3-(3-2*r)*hu+2*(e-1)*ht
  have hE := (mul_eq_zero.mp h3').resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) j0) r0) (sub_ne_zero.mpr r1))
  have es : e=(2*r^2-r)/3 := by linarith only [hE]
  rw [ht,hu,es] at h4
  have hR : (J*r^2*(r-1)*(2*r-3))*(r-2)=0 := by linear_combination 2*h4
  have hr := sub_eq_zero.mp ((mul_eq_zero.mp hR).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero j0 (pow_ne_zero _ r0)) (sub_ne_zero.mpr r1))
      (sub_ne_zero.mpr r32)))
  subst r
  constructor
  · rfl
  · norm_num at es ⊢
    exact es

/-- When the third dirty row follows a zero-V first clean row, the
last independently charged size-five defect forces an old defect. -/
theorem third_dirty_value
    (x y S H a v : ℚ)
    (h1 : S+(3/2)*H=1/2+x)
    (h2 : S+(9/4)*H=1/3+(2/3)*x-(2/3)*v)
    (hV : -S/2+(y+1/2)*a=v)
    (hG : S+(27/8)*H-1/4-x/2+v+((2*y+1)/8)*a=0)
    (hD : 4*y*v= -x*(2*x+1)) :
    x=y ∨ x= -1/2 := by
  have hh : (x-y)*(2*x+1)=0 := by
    linear_combination (16*y)*hG+(18*y)*h1-(36*y)*h2-(4*y)*hV+hD
  rcases mul_eq_zero.mp hh with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linarith only [h]

end RKResearch.Certified.ERK10RankThreePortOneLabel

#print axioms RKResearch.Certified.ERK10RankThreePortOneLabel.equal_defect_fifth_clock
#print axioms RKResearch.Certified.ERK10RankThreePortOneLabel.third_dirty_value
