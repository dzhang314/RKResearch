module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Rational recovery of a free helper tap
A rational clock core needs no further algebraic extension to meet the
monic-quadratic helper and first chronological-tail identities if their
scalar pivots are nonzero. This is not a new clock-core existence claim. -/
namespace RKResearch.Certified.SDIRKSevenDirtyRationalHelper

variable {K : Type*} [Field K] [CharZero K]

def q (w η x : K) : K := (x-w)*(x-η)
def J (w η x : K) : K := x^3/3-(w+η)*x^2/2+w*η*x
def E (w η : K) : K := (1-w)*(1-η)
def hNum (w η : K) : K := 2*E w η-2+w+η
def hDen (w η : K) : K := 1+E w η

omit [CharZero K] in
theorem helper_factor (w η t : K) :
    q w η (1+t)-(1+2*t-t^2)*q w η 1=t*(hDen w η*t-hNum w η) := by
  simp only [q,hDen,hNum,E]
  ring

omit [CharZero K] in
theorem tap_eq {w η t : K} (ht : t≠0)
    (h : q w η (1+t)=(1+2*t-t^2)*q w η 1) : hDen w η*t=hNum w η := by
  have e := helper_factor w η t
  rw [h,sub_self] at e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e.symm).resolve_left ht)

/-- At rational normalized helper data, a compatible nonzero tap can
never sit at a pole of the finite-quadratic recovery formula. -/
theorem rational_tap_den_ne {w η t : ℚ} (ht : t≠0)
    (h : q w η (1+t)=(1+2*t-t^2)*q w η 1) : hDen w η≠0 := by
  intro n
  have q := tap_eq ht h
  rw [n,zero_mul] at q
  have e₄ : w+η=4 := by
    simp only [hDen,hNum] at n q
    linear_combination -q-2*n
  have e₂ : (w-2)^2=2 := by
    simp only [hDen,E] at n
    linear_combination (w-1)*e₄-n
  have nat_no : ¬ IsSquare (2:ℕ) := by
    rintro ⟨m,e⟩
    by_cases b : 2≤m
    · have ge : 4≤m*m := Nat.mul_le_mul b b
      omega
    · have e' : m=0 ∨ m=1 := by omega
      rcases e' with rfl | rfl <;> norm_num at e
  exact ((Rat.isSquare_natCast_iff (n:=2)).not.mpr nat_no)
    ⟨w-2,by linear_combination -e₂⟩

omit [CharZero K] in
theorem solve_tap {w η : K} (h : hDen w η≠0) :
    let t := hNum w η / hDen w η
    q w η (1+t)=(1+2*t-t^2)*q w η 1 := by
  dsimp only
  apply sub_eq_zero.mp
  rw [helper_factor]
  have e : (hNum w η / hDen w η) * hDen w η=hNum w η := div_mul_cancel₀ _ h
  rw [mul_comm (hDen w η), e, sub_self, mul_zero]

def constTerm (w x aff : K) : K :=
  x*(x-w)-(x^3/3-w*x^2/2)+(w^3/3-w*w^2/2)*aff

def etaTerm (w x aff : K) : K :=
  -(x-w)-(w*x-x^2/2)+(w*w-w^2/2)*aff

theorem first_read_linear (w x aff η : K) :
    q w η x-J w η x+J w η w*aff=constTerm w x aff+η*etaTerm w x aff := by
  simp only [q,J,constTerm,etaTerm]
  ring

/-- Under the nonzero first-read pivot, the clock core fixes the
quadratic's second coefficient by one division. -/
theorem solve_first_read {w x aff : K} (h : etaTerm w x aff≠0) :
    let η := -constTerm w x aff / etaTerm w x aff
    q w η x-J w η x+J w η w*aff=0 := by
  dsimp only
  rw [first_read_linear,div_mul_cancel₀ _ h,add_neg_cancel]

end RKResearch.Certified.SDIRKSevenDirtyRationalHelper
