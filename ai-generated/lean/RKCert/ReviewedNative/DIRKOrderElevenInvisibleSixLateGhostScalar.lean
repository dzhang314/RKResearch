module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Exact cleared primitive ratio for the six-ghost late chart -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixLateGhost

variable {K : Type*} [Field K] [CharZero K]

noncomputable def IP (u v x : K) : K := x^4/4-(u+v)*x^3/3+u*v*x^2/2
noncomputable def IXP (u v x : K) : K := x^5/5-(u+v)*x^4/4+u*v*x^3/3
noncomputable def gate (u v w : K) : K := w*(u^2-4*u*v+v^2)+u*v*(u+v)

/-- The three primitive comparisons force the same cubic macro
relation as the signed one-active chart, without a division by IP. -/
theorem cleared_ratio_determinant (u v w : K) :
    (v-w)*IXP u v u*IP u v v*IP u v w
    +(w-u)*IXP u v v*IP u v u*IP u v w
    +(u-v)*IXP u v w*IP u v u*IP u v v =
      -u^3*v^3*w^2*(u-v)*(u-w)*(v-w)*gate u v w/1440 := by
  unfold IP IXP gate
  ring

/-- Nodal primitive degeneration still satisfies the cubic clock gate;
the two hypotheses are the corresponding nonzero-power-cleared rows. -/
theorem radau_gate (u v w : K) (hw : w≠0)
    (h0 : 3*w^2-4*(u+v)*w+6*u*v=0)
    (h1 : 12*w^2-15*(u+v)*w+20*u*v=0) : gate u v w=0 := by
  have hh : w*(5*(u+v)-6*w)=0 := by linear_combination 10*h0-3*h1
  have S : u+v=6*w/5 := by
    have z := (mul_eq_zero.mp hh).resolve_left hw
    linear_combination (1/5:K)*z
  have p : u*v=3*w^2/10 := by
    rw [S] at h0
    linear_combination (1/6:K)*h0
  unfold gate
  have e : u^2-4*u*v+v^2=(u+v)^2-6*(u*v) := by ring
  rw [e,S,p]
  ring

end RKResearch.Certified.Graded.OrderElevenInvisibleSixLateGhost
