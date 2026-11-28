module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

public section

namespace RKResearch.Certified.ERK10RankThreePortFourLabels

theorem clean_polynomial_coefficients
    (t c d : ℚ)
    (hE : t^2/4+c*t/3+d/2=0)
    (hF : (1/5-t/4)+c*(1/4-t/3)+d*(1/3-t/2)=0) :
    (5*(12*t^2-20*t+9))*c = -3*(15*t^3-10*t^2-15*t+12) ∧
      (10*(12*t^2-20*t+9))*d = 3*t*(20*t^2-35*t+16) := by
  constructor
  · linear_combination (-360*(1/3-t/2))*hE+180*hF
  · linear_combination (720*(1/4-t/3))*hE-(240*t)*hF

theorem clean_hull_pressure_nonzero
    (t c d w : ℚ)
    (hE : t^2/4+c*t/3+d/2=0)
    (hF : (1/5-t/4)+c*(1/4-t/3)+d*(1/3-t/2)=0)
    (hW : w*t*(t^2+c*t+d)=1/4+c/3+d/2) :
    (4*t-3)/36-w*(t-1)*t^2/3 ≠ 0 := by
  obtain ⟨hc,hd⟩ := clean_polynomial_coefficients t c d hE hF
  have hw : 2*w*t^2*(30*t^3-80*t^2+75*t-24)=-(t-1)*(5*t-3) := by
    linear_combination (20*(12*t^2-20*t+9))*hW-
      (4*(w*t^2-1/3))*hc-(2*(w*t-1/2))*hd
  have hdet :
      ((4*t-3)/36-w*(t-1)*t^2/3)*(36*(30*t^3-80*t^2+75*t-24)) =
        (10*t^2-15*t+6)*(12*t^2-20*t+9) := by
    linear_combination (-6*(t-1))*hw
  intro hZ
  rw [hZ,zero_mul] at hdet
  have p : 10*t^2-15*t+6 ≠ 0 := by
    intro h
    nlinarith [sq_nonneg (t-3/4)]
  have q : 12*t^2-20*t+9 ≠ 0 := by
    intro h
    nlinarith [sq_nonneg (t-5/6)]
  exact (mul_ne_zero p q) hdet.symm

end RKResearch.Certified.ERK10RankThreePortFourLabels

#print axioms RKResearch.Certified.ERK10RankThreePortFourLabels.clean_polynomial_coefficients
#print axioms RKResearch.Certified.ERK10RankThreePortFourLabels.clean_hull_pressure_nonzero
