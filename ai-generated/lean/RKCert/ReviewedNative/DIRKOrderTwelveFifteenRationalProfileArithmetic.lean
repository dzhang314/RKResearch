import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFourDirtyArithmetic

/-! Fixed singular-profile diagonal and reversed anomaly primitive receipts. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.RationalProfileArithmetic

open FourDirtyArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def quotient (b : Nat) : List Nat := hull (interiors.filter (· != b))

def diagonalNum (b : Nat) : Nat := integral (0::quotient b) 0 b

def reverseRow (b : Nat) : List Nat :=
  let f := mulPoly [1,42] (quotient b)
  (interiors.filter (· != b)).map fun a => integral f a 1

theorem diagonalNumerators :
    interiors.map diagonalNum = [11,8,20,12,16] := by decide_cbv

theorem anomalyReversePrimitives :
    interiors.map reverseRow =
      [[29,10,15,39],[16,2,3,15],[6,8,9,2],[20,14,41,5],[14,26,26,11]] := by decide_cbv

theorem allDiagonalNonzero : (interiors.map diagonalNum).all (· != 0) = true := by
  rw [diagonalNumerators]
  decide

theorem allReverseNonzero :
    (interiors.flatMap reverseRow).length = 20 ∧
    (interiors.flatMap reverseRow).all (· != 0) = true := by decide_cbv

#print axioms allDiagonalNonzero
#print axioms allReverseNonzero

end RKResearch.Certified.Graded.OrderTwelveFifteen.RationalProfileArithmetic
