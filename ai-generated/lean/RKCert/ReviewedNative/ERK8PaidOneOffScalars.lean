module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERKOrderEightLobattoScalar

public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Paid scalar helpers. Their proofs use no
order-nine tableau hypotheses, and none is the numerical width-ten theorem. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open Polynomial
open scoped BigOperators Classical

variable {K : Type*} [Field K] [EightUnits K]

/-- Same explicit cubic, from the reviewed p8 scalar object. -/
noncomputable abbrev lobattoCubic : K[X] := LobattoEight.lobattoCubic

/-! The seven order-independent scalar definitions/identities are
public donor slices in this new, independent namespace. -/
def hzero (d x : K) : K := x^2*(x-2*d)/(4*d)
def m1 (x H : K) : K := x^2/2+2*H
def m2 (d x H : K) : K := x^3/3+(4*d/3)*H
def m3 (d x H : K) : K := x^4/4+(2*d^2-d*x)*H

def jValue (d z x H : K) : K :=
  2*d*(d-x)*H + ((z-d)*m3 d x H-d*(3*z-2*d)*m2 d x H+2*d^2*z*m1 x H)/(4*d)

def vValue (d z x H : K) : K :=
  (3*d+z)*m3 d x H-(2*d^2+3*d*z)*m2 d x H+2*d^2*z*m1 x H-x^5/5

theorem j_value_doubled (d z H : K) (dn : d≠0) :
    jValue d z (2*d) H=d^4/3-(4*d^2/3)*H := by
  unfold jValue m1 m2 m3
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,dn]
  eight_ring K

omit [EightUnits K] in
theorem common_clock_affine_parameters {u v J slope P Q : K}
    (diff : v≠u) (a0 : J+u*slope=P+u*Q) (a1 : J+v*slope=P+v*Q) :
    P=J ∧ Q=slope := by
  have sq : Q=slope := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr diff)
    linear_combination (norm := eight_ring K) a0-a1
  rw [sq] at a0
  exact ⟨(add_right_cancel a0).symm,sq⟩

theorem lobatto_eval_factor (x : K) :
    (lobattoCubic : K[X]).eval x = (x-1/2)*(x^2-x+1/7) := by
  simp only [lobattoCubic,LobattoEight.lobattoCubic,eval_add,eval_monomial]
  eight_ring K

/-- The exact scalar discriminant for the seventh physical receiver;
no Radau value, no wide p9 coefficient formula, and no extra knot. -/
theorem masterCombination (d z x U : K) (dn : d≠0) :
    vValue d z x U-(4*d/5)*jValue d z x U + (4*d/5)*(x^2-2*d^2)*U =
      (x-2*d)*(x-z)*(4*d*U-x^2*(x-2*d))/5 := by
  unfold jValue vValue m1 m2 m3
  field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,dn] <;> eight_ring K

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight
