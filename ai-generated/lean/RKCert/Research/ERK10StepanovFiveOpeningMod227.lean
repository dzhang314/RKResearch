import Lean

namespace RKResearch.ERK10StepanovFiveOpeningMod227

/-! Arithmetic receipts only: the mathematical high-row support argument
    and recovery of the matrices from the official radicals are separate. -/

private def removeAt : Nat → List Int → List Int
  | _, [] => []
  | 0, _ :: x => x
  | n+1, a :: x => a :: removeAt n x

private def det : Nat → List (List Int) → Int
  | 0, _ => 1
  | Nat.succ _, [] => 0
  | n+1, r :: rs =>
    (r.zipIdx.map (fun (a,j) =>
      (if j % 2 == 0 then a else -a) * det n (rs.map (removeAt j)))).sum

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem canonicalColumns : det 7 [[106, 224, 43, 142, 185, 103, 53], [185, 74, 124, 3, 58, 71, 53], [128, 142, 25, 72, 28, 82, 53], [172, 205, 146, 139, 37, 213, 53], [37, 190, 223, 4, 186, 135, 0], [71, 156, 131, 96, 35, 60, 0], [109, 50, 191, 66, 32, 205, 53]] % 227 = 159 := by decide

theorem relaxedColumns : det 6 [[224, 43, 142, 185, 103, 53], [74, 124, 3, 58, 71, 53], [142, 25, 72, 28, 82, 53], [205, 146, 139, 37, 213, 53], [190, 223, 4, 186, 135, 0], [156, 131, 96, 35, 60, 0]] % 227 = 199 := by decide

theorem canonicalMoment : det 2 [[154, 11], [131, 201]] % 227 = 3 := by decide

theorem relaxedMoment : det 3 [[154, 204, 177], [131, 75, 3], [120, 177, 9]] % 227 = 178 := by decide

end RKResearch.ERK10StepanovFiveOpeningMod227
