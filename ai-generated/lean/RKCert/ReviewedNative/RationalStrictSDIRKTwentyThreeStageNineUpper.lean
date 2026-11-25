module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineTall
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.Grade00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade03
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade04
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade05
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade06
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade07
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineGrades.Grade08

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open scoped Matrix

private theorem paidGroup (n : Fin 9) :
    (treesOfOrderSucc n.val).all paidTree = true := by
  fin_cases n
  · exact paidGrade0
  · exact paidGrade1
  · exact paidGrade2
  · exact paidGrade3
  · exact paidGrade4
  · exact paidGrade5
  · exact paidGrade6
  · exact paidGrade7
  · exact paidGrade8

private theorem checked : checkScaledOrder actInt outInt stageScale weightScale 9 = true := by
  change (List.range 9).all (fun n => (treesOfOrderSucc n).all paidTree) = true
  apply List.all_eq_true.mpr
  intro n hn
  exact paidGroup ⟨n, List.mem_range.mp hn⟩

theorem order_nine : HasOrder 9 A b :=
  hasOrder_of_scaled_check (A := AInt) (b := bInt) (d := stageScale) (e := weightScale) (p := 9)
    (Int.castRingHom ℚ) actInt_eq outInt_eq cast_AInt cast_bInt
    (isUnit_iff_ne_zero.mpr stageScale_ne_zero)
    (isUnit_iff_ne_zero.mpr weightScale_ne_zero) checked

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

namespace RKResearch.Certified

/-- Twenty-three rational stages suffice for exact order nine. -/
theorem exists_twenty_three_stage_rational_strictSDIRK_exact_nine :
    ∃ (A : Matrix (Fin 23) (Fin 23) ℚ) (b : Fin 23 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/9) ∧ (1/9 : ℚ) ≠ 0 ∧
        HasOrder 9 A b ∧ ¬ HasOrder 10 A b :=
  ⟨RationalStrictSDIRKTwentyThreeStageNineUpper.A, RationalStrictSDIRKTwentyThreeStageNineUpper.b,
    RationalStrictSDIRKTwentyThreeStageNineUpper.lowerTriangular, RationalStrictSDIRKTwentyThreeStageNineUpper.common_diagonal, by decide +kernel,
    RationalStrictSDIRKTwentyThreeStageNineUpper.order_nine, RationalStrictSDIRKTwentyThreeStageNineUpper.not_order_ten⟩

end RKResearch.Certified
