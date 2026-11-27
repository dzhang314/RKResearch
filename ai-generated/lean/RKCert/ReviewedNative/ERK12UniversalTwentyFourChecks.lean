module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft0
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight0
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep0
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft1
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight1
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep1
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft2
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight2
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep2
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft3
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight3
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep3
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft4
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight4
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep4
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft5
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight5
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep5
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft6
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight6
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep6
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft7
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight7
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep7
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft8
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight8
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep8
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft9
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight9
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep9
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckLeft10
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckRight10
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckStep10
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCheckEnergy
import Mathlib.Tactic.FinCases

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

theorem matrixLeft0 : branch M D 1 * cov 0 = leftScale 0 • left 0 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left0At0
  · exact left0At1
  · exact left0At2
  · exact left0At3
  · exact left0At4

theorem matrixRight0 : left 0 * (branch M D 1)ᵀ = rightScale 0 • right 0 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right0At0
  · exact right0At1
  · exact right0At2
  · exact right0At3
  · exact right0At4

theorem matrixStep0 : lhs 0 • cov (0+1) = factoredStep 0 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step0At0
  · exact step0At1
  · exact step0At2
  · exact step0At3
  · exact step0At4

theorem matrixLeft1 : branch M D 1 * cov 1 = leftScale 1 • left 1 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left1At0
  · exact left1At1
  · exact left1At2
  · exact left1At3
  · exact left1At4

theorem matrixRight1 : left 1 * (branch M D 1)ᵀ = rightScale 1 • right 1 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right1At0
  · exact right1At1
  · exact right1At2
  · exact right1At3
  · exact right1At4

theorem matrixStep1 : lhs 1 • cov (1+1) = factoredStep 1 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step1At0
  · exact step1At1
  · exact step1At2
  · exact step1At3
  · exact step1At4

theorem matrixLeft2 : branch M D 1 * cov 2 = leftScale 2 • left 2 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left2At0
  · exact left2At1
  · exact left2At2
  · exact left2At3
  · exact left2At4

theorem matrixRight2 : left 2 * (branch M D 1)ᵀ = rightScale 2 • right 2 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right2At0
  · exact right2At1
  · exact right2At2
  · exact right2At3
  · exact right2At4

theorem matrixStep2 : lhs 2 • cov (2+1) = factoredStep 2 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step2At0
  · exact step2At1
  · exact step2At2
  · exact step2At3
  · exact step2At4

theorem matrixLeft3 : branch M D 1 * cov 3 = leftScale 3 • left 3 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left3At0
  · exact left3At1
  · exact left3At2
  · exact left3At3
  · exact left3At4

theorem matrixRight3 : left 3 * (branch M D 1)ᵀ = rightScale 3 • right 3 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right3At0
  · exact right3At1
  · exact right3At2
  · exact right3At3
  · exact right3At4

theorem matrixStep3 : lhs 3 • cov (3+1) = factoredStep 3 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step3At0
  · exact step3At1
  · exact step3At2
  · exact step3At3
  · exact step3At4

theorem matrixLeft4 : branch M D 1 * cov 4 = leftScale 4 • left 4 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left4At0
  · exact left4At1
  · exact left4At2
  · exact left4At3
  · exact left4At4

theorem matrixRight4 : left 4 * (branch M D 1)ᵀ = rightScale 4 • right 4 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right4At0
  · exact right4At1
  · exact right4At2
  · exact right4At3
  · exact right4At4

theorem matrixStep4 : lhs 4 • cov (4+1) = factoredStep 4 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step4At0
  · exact step4At1
  · exact step4At2
  · exact step4At3
  · exact step4At4

theorem matrixLeft5 : branch M D 1 * cov 5 = leftScale 5 • left 5 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left5At0
  · exact left5At1
  · exact left5At2
  · exact left5At3
  · exact left5At4

theorem matrixRight5 : left 5 * (branch M D 1)ᵀ = rightScale 5 • right 5 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right5At0
  · exact right5At1
  · exact right5At2
  · exact right5At3
  · exact right5At4

theorem matrixStep5 : lhs 5 • cov (5+1) = factoredStep 5 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step5At0
  · exact step5At1
  · exact step5At2
  · exact step5At3
  · exact step5At4

theorem matrixLeft6 : branch M D 1 * cov 6 = leftScale 6 • left 6 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left6At0
  · exact left6At1
  · exact left6At2
  · exact left6At3
  · exact left6At4

theorem matrixRight6 : left 6 * (branch M D 1)ᵀ = rightScale 6 • right 6 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right6At0
  · exact right6At1
  · exact right6At2
  · exact right6At3
  · exact right6At4

theorem matrixStep6 : lhs 6 • cov (6+1) = factoredStep 6 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step6At0
  · exact step6At1
  · exact step6At2
  · exact step6At3
  · exact step6At4

theorem matrixLeft7 : branch M D 1 * cov 7 = leftScale 7 • left 7 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left7At0
  · exact left7At1
  · exact left7At2
  · exact left7At3
  · exact left7At4

theorem matrixRight7 : left 7 * (branch M D 1)ᵀ = rightScale 7 • right 7 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right7At0
  · exact right7At1
  · exact right7At2
  · exact right7At3
  · exact right7At4

theorem matrixStep7 : lhs 7 • cov (7+1) = factoredStep 7 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step7At0
  · exact step7At1
  · exact step7At2
  · exact step7At3
  · exact step7At4

theorem matrixLeft8 : branch M D 1 * cov 8 = leftScale 8 • left 8 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left8At0
  · exact left8At1
  · exact left8At2
  · exact left8At3
  · exact left8At4

theorem matrixRight8 : left 8 * (branch M D 1)ᵀ = rightScale 8 • right 8 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right8At0
  · exact right8At1
  · exact right8At2
  · exact right8At3
  · exact right8At4

theorem matrixStep8 : lhs 8 • cov (8+1) = factoredStep 8 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step8At0
  · exact step8At1
  · exact step8At2
  · exact step8At3
  · exact step8At4

theorem matrixLeft9 : branch M D 1 * cov 9 = leftScale 9 • left 9 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left9At0
  · exact left9At1
  · exact left9At2
  · exact left9At3
  · exact left9At4

theorem matrixRight9 : left 9 * (branch M D 1)ᵀ = rightScale 9 • right 9 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right9At0
  · exact right9At1
  · exact right9At2
  · exact right9At3
  · exact right9At4

theorem matrixStep9 : lhs 9 • cov (9+1) = factoredStep 9 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step9At0
  · exact step9At1
  · exact step9At2
  · exact step9At3
  · exact step9At4

theorem matrixLeft10 : branch M D 1 * cov 10 = leftScale 10 • left 10 := by
  rw [← leftEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact left10At0
  · exact left10At1
  · exact left10At2
  · exact left10At3
  · exact left10At4

theorem matrixRight10 : left 10 * (branch M D 1)ᵀ = rightScale 10 • right 10 := by
  rw [← rightEntry_matrix]
  apply extOfBlocks
  intro k
  fin_cases k
  · exact right10At0
  · exact right10At1
  · exact right10At2
  · exact right10At3
  · exact right10At4

theorem matrixStep10 : lhs 10 • cov (10+1) = factoredStep 10 := by
  apply extOfBlocks
  intro k
  fin_cases k
  · exact step10At0
  · exact step10At1
  · exact step10At2
  · exact step10At3
  · exact step10At4

theorem all_left (n : Fin 11) : branch M D 1 * cov n.val = leftScale n.val • left n.val := by
  fin_cases n
  · exact matrixLeft0
  · exact matrixLeft1
  · exact matrixLeft2
  · exact matrixLeft3
  · exact matrixLeft4
  · exact matrixLeft5
  · exact matrixLeft6
  · exact matrixLeft7
  · exact matrixLeft8
  · exact matrixLeft9
  · exact matrixLeft10

theorem all_right (n : Fin 11) : left n.val * (branch M D 1)ᵀ = rightScale n.val • right n.val := by
  fin_cases n
  · exact matrixRight0
  · exact matrixRight1
  · exact matrixRight2
  · exact matrixRight3
  · exact matrixRight4
  · exact matrixRight5
  · exact matrixRight6
  · exact matrixRight7
  · exact matrixRight8
  · exact matrixRight9
  · exact matrixRight10

theorem all_step (n : Fin 11) : lhs n.val • cov (n.val+1) = factoredStep n.val := by
  fin_cases n
  · exact matrixStep0
  · exact matrixStep1
  · exact matrixStep2
  · exact matrixStep3
  · exact matrixStep4
  · exact matrixStep5
  · exact matrixStep6
  · exact matrixStep7
  · exact matrixStep8
  · exact matrixStep9
  · exact matrixStep10

theorem all_energy (n : Fin 12) : energy (cov n.val) (output w D (n.val+1)) = 0 := by
  fin_cases n
  · exact energy0
  · exact energy1
  · exact energy2
  · exact energy3
  · exact energy4
  · exact energy5
  · exact energy6
  · exact energy7
  · exact energy8
  · exact energy9
  · exact energy10
  · exact energy11

theorem all_lhs (n : Fin 11) : covScale (n.val+1) = common n.val * lhs n.val := by
  revert n
  decide +kernel

theorem all_coeff (n : Fin 11) : ∀ i : Fin (n.val+1),
    covScale i.val * (covScale (n.val-i.val) * leftScale (n.val-i.val) * rightScale (n.val-i.val)) =
      common n.val * coeff n.val i.val := by
  revert n
  decide +kernel

def trace : FactoredTrace M D 12 where
  cov := cov
  left := left
  right := right
  covScale := covScale
  leftScale := leftScale
  rightScale := rightScale
  common := common
  lhs := lhs
  coeff := coeff
  base := checkedBase
  hleft n hn := all_left ⟨n, by omega⟩
  hright n hn := all_right ⟨n, by omega⟩
  hlhs n hn := all_lhs ⟨n, by omega⟩
  hcoeff n hn := all_coeff ⟨n, by omega⟩
  next n hn := all_step ⟨n, by omega⟩

end RKResearch.Certified.ERK12UniversalTwentyFour
