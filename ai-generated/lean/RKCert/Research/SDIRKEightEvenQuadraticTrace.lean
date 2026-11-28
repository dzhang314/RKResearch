module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Protected prefix and symmetric supported-trace scalar receipts -/

namespace RKResearch.Certified.SDIRKEightEvenQuadraticTrace

open scoped BigOperators

theorem symmetric_diagonal_form {R : Type*} [CommRing R] (x y z a b c : R) :
    (-a-b)*(x-y)*(x-z)+(-a-c)*(y-x)*(y-z)+(-b-c)*(z-x)*(z-y) =
      -a*(x-y)^2-b*(x-z)^2-c*(y-z)^2 := by ring

theorem protected_diagonal_read {R I : Type*} [CommRing R]
    {s : Finset I} {a v w : I → R} {d x y : R}
    (h : ∀ j ∈ s, v j=w j) :
    (∑ j ∈ s,a j*v j)+d*x = (∑ j ∈ s,a j*w j)+d*y+d*(x-y) := by
  have eq : (∑ j ∈ s,a j*v j) = ∑ j ∈ s,a j*w j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [h j hj]
  rw [eq]
  ring

theorem protected_defects :
    (327053 : ZMod 965179) ≠ 0 ∧ (372905 : ZMod 965179) ≠ 0 ∧
    (274684677964 : ZMod 3535032504307) ≠ 0 ∧
    (2883704798279 : ZMod 3535032504307) ≠ 0 ∧
    (3184654386934665632 : ZMod 3489226706289835873) ≠ 0 ∧
    (559218082341581846 : ZMod 3489226706289835873) ≠ 0 ∧
    (825 : ZMod 1439) ≠ 0 ∧ (1318 : ZMod 1439) ≠ 0 ∧
    (204773 : ZMod 420941) ≠ 0 ∧ (83426 : ZMod 420941) ≠ 0 ∧
    (45959 : ZMod 48029) ≠ 0 ∧ (7256 : ZMod 48029) ≠ 0 ∧
    (80272079603567541 : ZMod 434112360658085729) ≠ 0 ∧
    (238261968342116336 : ZMod 434112360658085729) ≠ 0 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightEvenQuadraticTrace
