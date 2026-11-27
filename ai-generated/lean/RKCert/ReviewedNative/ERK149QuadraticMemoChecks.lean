module

public import RKCert.ReviewedNative.ERK149QuadraticMemoSoundness
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKResearch.Certified.ERK149QuadraticMemo

open CanonicalStageMemo ERKQuadraticIntegerReplay ERK149QuadraticMemoData
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem gradeOKBlock0 : checkBlock gradeOK 486 0 16 = true := by decide +kernel
private theorem gradeOKBlock1 : checkBlock gradeOK 486 1 16 = true := by decide +kernel
private theorem gradeOKBlock2 : checkBlock gradeOK 486 2 16 = true := by decide +kernel
private theorem gradeOKBlock3 : checkBlock gradeOK 486 3 16 = true := by decide +kernel
private theorem gradeOKBlock4 : checkBlock gradeOK 486 4 16 = true := by decide +kernel
private theorem gradeOKBlock5 : checkBlock gradeOK 486 5 16 = true := by decide +kernel
private theorem gradeOKBlock6 : checkBlock gradeOK 486 6 16 = true := by decide +kernel
private theorem gradeOKBlock7 : checkBlock gradeOK 486 7 16 = true := by decide +kernel
private theorem gradeOKBlock8 : checkBlock gradeOK 486 8 16 = true := by decide +kernel
private theorem gradeOKBlock9 : checkBlock gradeOK 486 9 16 = true := by decide +kernel
private theorem gradeOKBlock10 : checkBlock gradeOK 486 10 16 = true := by decide +kernel
private theorem gradeOKBlock11 : checkBlock gradeOK 486 11 16 = true := by decide +kernel
private theorem gradeOKBlock12 : checkBlock gradeOK 486 12 16 = true := by decide +kernel
private theorem gradeOKBlock13 : checkBlock gradeOK 486 13 16 = true := by decide +kernel
private theorem gradeOKBlock14 : checkBlock gradeOK 486 14 16 = true := by decide +kernel
private theorem gradeOKBlock15 : checkBlock gradeOK 486 15 16 = true := by decide +kernel
private theorem gradeOKBlock16 : checkBlock gradeOK 486 16 16 = true := by decide +kernel
private theorem gradeOKBlock17 : checkBlock gradeOK 486 17 16 = true := by decide +kernel
private theorem gradeOKBlock18 : checkBlock gradeOK 486 18 16 = true := by decide +kernel
private theorem gradeOKBlock19 : checkBlock gradeOK 486 19 16 = true := by decide +kernel
private theorem gradeOKBlock20 : checkBlock gradeOK 486 20 16 = true := by decide +kernel
private theorem gradeOKBlock21 : checkBlock gradeOK 486 21 16 = true := by decide +kernel
private theorem gradeOKBlock22 : checkBlock gradeOK 486 22 16 = true := by decide +kernel
private theorem gradeOKBlock23 : checkBlock gradeOK 486 23 16 = true := by decide +kernel
private theorem gradeOKBlock24 : checkBlock gradeOK 486 24 16 = true := by decide +kernel
private theorem gradeOKBlock25 : checkBlock gradeOK 486 25 16 = true := by decide +kernel
private theorem gradeOKBlock26 : checkBlock gradeOK 486 26 16 = true := by decide +kernel
private theorem gradeOKBlock27 : checkBlock gradeOK 486 27 16 = true := by decide +kernel
private theorem gradeOKBlock28 : checkBlock gradeOK 486 28 16 = true := by decide +kernel
private theorem gradeOKBlock29 : checkBlock gradeOK 486 29 16 = true := by decide +kernel
private theorem gradeOKBlock30 : checkBlock gradeOK 486 30 16 = true := by decide +kernel

private theorem gradeOKBlocks (i : ℕ) (h : i < 31) : checkBlock gradeOK 486 i 16 = true := by
  interval_cases i
  · exact gradeOKBlock0
  · exact gradeOKBlock1
  · exact gradeOKBlock2
  · exact gradeOKBlock3
  · exact gradeOKBlock4
  · exact gradeOKBlock5
  · exact gradeOKBlock6
  · exact gradeOKBlock7
  · exact gradeOKBlock8
  · exact gradeOKBlock9
  · exact gradeOKBlock10
  · exact gradeOKBlock11
  · exact gradeOKBlock12
  · exact gradeOKBlock13
  · exact gradeOKBlock14
  · exact gradeOKBlock15
  · exact gradeOKBlock16
  · exact gradeOKBlock17
  · exact gradeOKBlock18
  · exact gradeOKBlock19
  · exact gradeOKBlock20
  · exact gradeOKBlock21
  · exact gradeOKBlock22
  · exact gradeOKBlock23
  · exact gradeOKBlock24
  · exact gradeOKBlock25
  · exact gradeOKBlock26
  · exact gradeOKBlock27
  · exact gradeOKBlock28
  · exact gradeOKBlock29
  · exact gradeOKBlock30

private theorem joinOKBlock0 : checkBlock joinOK 200 0 8 = true := by decide +kernel
private theorem joinOKBlock1 : checkBlock joinOK 200 1 8 = true := by decide +kernel
private theorem joinOKBlock2 : checkBlock joinOK 200 2 8 = true := by decide +kernel
private theorem joinOKBlock3 : checkBlock joinOK 200 3 8 = true := by decide +kernel
private theorem joinOKBlock4 : checkBlock joinOK 200 4 8 = true := by decide +kernel
private theorem joinOKBlock5 : checkBlock joinOK 200 5 8 = true := by decide +kernel
private theorem joinOKBlock6 : checkBlock joinOK 200 6 8 = true := by decide +kernel
private theorem joinOKBlock7 : checkBlock joinOK 200 7 8 = true := by decide +kernel
private theorem joinOKBlock8 : checkBlock joinOK 200 8 8 = true := by decide +kernel
private theorem joinOKBlock9 : checkBlock joinOK 200 9 8 = true := by decide +kernel
private theorem joinOKBlock10 : checkBlock joinOK 200 10 8 = true := by decide +kernel
private theorem joinOKBlock11 : checkBlock joinOK 200 11 8 = true := by decide +kernel
private theorem joinOKBlock12 : checkBlock joinOK 200 12 8 = true := by decide +kernel
private theorem joinOKBlock13 : checkBlock joinOK 200 13 8 = true := by decide +kernel
private theorem joinOKBlock14 : checkBlock joinOK 200 14 8 = true := by decide +kernel
private theorem joinOKBlock15 : checkBlock joinOK 200 15 8 = true := by decide +kernel
private theorem joinOKBlock16 : checkBlock joinOK 200 16 8 = true := by decide +kernel
private theorem joinOKBlock17 : checkBlock joinOK 200 17 8 = true := by decide +kernel
private theorem joinOKBlock18 : checkBlock joinOK 200 18 8 = true := by decide +kernel
private theorem joinOKBlock19 : checkBlock joinOK 200 19 8 = true := by decide +kernel
private theorem joinOKBlock20 : checkBlock joinOK 200 20 8 = true := by decide +kernel
private theorem joinOKBlock21 : checkBlock joinOK 200 21 8 = true := by decide +kernel
private theorem joinOKBlock22 : checkBlock joinOK 200 22 8 = true := by decide +kernel
private theorem joinOKBlock23 : checkBlock joinOK 200 23 8 = true := by decide +kernel
private theorem joinOKBlock24 : checkBlock joinOK 200 24 8 = true := by decide +kernel

private theorem joinOKBlocks (i : ℕ) (h : i < 25) : checkBlock joinOK 200 i 8 = true := by
  interval_cases i
  · exact joinOKBlock0
  · exact joinOKBlock1
  · exact joinOKBlock2
  · exact joinOKBlock3
  · exact joinOKBlock4
  · exact joinOKBlock5
  · exact joinOKBlock6
  · exact joinOKBlock7
  · exact joinOKBlock8
  · exact joinOKBlock9
  · exact joinOKBlock10
  · exact joinOKBlock11
  · exact joinOKBlock12
  · exact joinOKBlock13
  · exact joinOKBlock14
  · exact joinOKBlock15
  · exact joinOKBlock16
  · exact joinOKBlock17
  · exact joinOKBlock18
  · exact joinOKBlock19
  · exact joinOKBlock20
  · exact joinOKBlock21
  · exact joinOKBlock22
  · exact joinOKBlock23
  · exact joinOKBlock24

private theorem derivOKBlock0 : checkBlock derivOK 200 0 8 = true := by decide +kernel
private theorem derivOKBlock1 : checkBlock derivOK 200 1 8 = true := by decide +kernel
private theorem derivOKBlock2 : checkBlock derivOK 200 2 8 = true := by decide +kernel
private theorem derivOKBlock3 : checkBlock derivOK 200 3 8 = true := by decide +kernel
private theorem derivOKBlock4 : checkBlock derivOK 200 4 8 = true := by decide +kernel
private theorem derivOKBlock5 : checkBlock derivOK 200 5 8 = true := by decide +kernel
private theorem derivOKBlock6 : checkBlock derivOK 200 6 8 = true := by decide +kernel
private theorem derivOKBlock7 : checkBlock derivOK 200 7 8 = true := by decide +kernel
private theorem derivOKBlock8 : checkBlock derivOK 200 8 8 = true := by decide +kernel
private theorem derivOKBlock9 : checkBlock derivOK 200 9 8 = true := by decide +kernel
private theorem derivOKBlock10 : checkBlock derivOK 200 10 8 = true := by decide +kernel
private theorem derivOKBlock11 : checkBlock derivOK 200 11 8 = true := by decide +kernel
private theorem derivOKBlock12 : checkBlock derivOK 200 12 8 = true := by decide +kernel
private theorem derivOKBlock13 : checkBlock derivOK 200 13 8 = true := by decide +kernel
private theorem derivOKBlock14 : checkBlock derivOK 200 14 8 = true := by decide +kernel
private theorem derivOKBlock15 : checkBlock derivOK 200 15 8 = true := by decide +kernel
private theorem derivOKBlock16 : checkBlock derivOK 200 16 8 = true := by decide +kernel
private theorem derivOKBlock17 : checkBlock derivOK 200 17 8 = true := by decide +kernel
private theorem derivOKBlock18 : checkBlock derivOK 200 18 8 = true := by decide +kernel
private theorem derivOKBlock19 : checkBlock derivOK 200 19 8 = true := by decide +kernel
private theorem derivOKBlock20 : checkBlock derivOK 200 20 8 = true := by decide +kernel
private theorem derivOKBlock21 : checkBlock derivOK 200 21 8 = true := by decide +kernel
private theorem derivOKBlock22 : checkBlock derivOK 200 22 8 = true := by decide +kernel
private theorem derivOKBlock23 : checkBlock derivOK 200 23 8 = true := by decide +kernel
private theorem derivOKBlock24 : checkBlock derivOK 200 24 8 = true := by decide +kernel

private theorem derivOKBlocks (i : ℕ) (h : i < 25) : checkBlock derivOK 200 i 8 = true := by
  interval_cases i
  · exact derivOKBlock0
  · exact derivOKBlock1
  · exact derivOKBlock2
  · exact derivOKBlock3
  · exact derivOKBlock4
  · exact derivOKBlock5
  · exact derivOKBlock6
  · exact derivOKBlock7
  · exact derivOKBlock8
  · exact derivOKBlock9
  · exact derivOKBlock10
  · exact derivOKBlock11
  · exact derivOKBlock12
  · exact derivOKBlock13
  · exact derivOKBlock14
  · exact derivOKBlock15
  · exact derivOKBlock16
  · exact derivOKBlock17
  · exact derivOKBlock18
  · exact derivOKBlock19
  · exact derivOKBlock20
  · exact derivOKBlock21
  · exact derivOKBlock22
  · exact derivOKBlock23
  · exact derivOKBlock24

private theorem payOKBlock0 : checkBlock payOK 486 0 16 = true := by decide +kernel
private theorem payOKBlock1 : checkBlock payOK 486 1 16 = true := by decide +kernel
private theorem payOKBlock2 : checkBlock payOK 486 2 16 = true := by decide +kernel
private theorem payOKBlock3 : checkBlock payOK 486 3 16 = true := by decide +kernel
private theorem payOKBlock4 : checkBlock payOK 486 4 16 = true := by decide +kernel
private theorem payOKBlock5 : checkBlock payOK 486 5 16 = true := by decide +kernel
private theorem payOKBlock6 : checkBlock payOK 486 6 16 = true := by decide +kernel
private theorem payOKBlock7 : checkBlock payOK 486 7 16 = true := by decide +kernel
private theorem payOKBlock8 : checkBlock payOK 486 8 16 = true := by decide +kernel
private theorem payOKBlock9 : checkBlock payOK 486 9 16 = true := by decide +kernel
private theorem payOKBlock10 : checkBlock payOK 486 10 16 = true := by decide +kernel
private theorem payOKBlock11 : checkBlock payOK 486 11 16 = true := by decide +kernel
private theorem payOKBlock12 : checkBlock payOK 486 12 16 = true := by decide +kernel
private theorem payOKBlock13 : checkBlock payOK 486 13 16 = true := by decide +kernel
private theorem payOKBlock14 : checkBlock payOK 486 14 16 = true := by decide +kernel
private theorem payOKBlock15 : checkBlock payOK 486 15 16 = true := by decide +kernel
private theorem payOKBlock16 : checkBlock payOK 486 16 16 = true := by decide +kernel
private theorem payOKBlock17 : checkBlock payOK 486 17 16 = true := by decide +kernel
private theorem payOKBlock18 : checkBlock payOK 486 18 16 = true := by decide +kernel
private theorem payOKBlock19 : checkBlock payOK 486 19 16 = true := by decide +kernel
private theorem payOKBlock20 : checkBlock payOK 486 20 16 = true := by decide +kernel
private theorem payOKBlock21 : checkBlock payOK 486 21 16 = true := by decide +kernel
private theorem payOKBlock22 : checkBlock payOK 486 22 16 = true := by decide +kernel
private theorem payOKBlock23 : checkBlock payOK 486 23 16 = true := by decide +kernel
private theorem payOKBlock24 : checkBlock payOK 486 24 16 = true := by decide +kernel
private theorem payOKBlock25 : checkBlock payOK 486 25 16 = true := by decide +kernel
private theorem payOKBlock26 : checkBlock payOK 486 26 16 = true := by decide +kernel
private theorem payOKBlock27 : checkBlock payOK 486 27 16 = true := by decide +kernel
private theorem payOKBlock28 : checkBlock payOK 486 28 16 = true := by decide +kernel
private theorem payOKBlock29 : checkBlock payOK 486 29 16 = true := by decide +kernel
private theorem payOKBlock30 : checkBlock payOK 486 30 16 = true := by decide +kernel

private theorem payOKBlocks (i : ℕ) (h : i < 31) : checkBlock payOK 486 i 16 = true := by
  interval_cases i
  · exact payOKBlock0
  · exact payOKBlock1
  · exact payOKBlock2
  · exact payOKBlock3
  · exact payOKBlock4
  · exact payOKBlock5
  · exact payOKBlock6
  · exact payOKBlock7
  · exact payOKBlock8
  · exact payOKBlock9
  · exact payOKBlock10
  · exact payOKBlock11
  · exact payOKBlock12
  · exact payOKBlock13
  · exact payOKBlock14
  · exact payOKBlock15
  · exact payOKBlock16
  · exact payOKBlock17
  · exact payOKBlock18
  · exact payOKBlock19
  · exact payOKBlock20
  · exact payOKBlock21
  · exact payOKBlock22
  · exact payOKBlock23
  · exact payOKBlock24
  · exact payOKBlock25
  · exact payOKBlock26
  · exact payOKBlock27
  · exact payOKBlock28
  · exact payOKBlock29
  · exact payOKBlock30

theorem receipts : Receipts where
  root := by decide +kernel
  grade i := checkBlock_covers (by decide) (by decide) gradeOKBlocks i i.isLt
  join i hi := checkBlock_covers (by decide) (by decide) joinOKBlocks i hi
  deriv i hi := checkBlock_covers (by decide) (by decide) derivOKBlocks i hi
  payment i := checkBlock_covers (by decide) (by decide) payOKBlocks i i.isLt

variable {R : Type*} [CommRing R]

theorem orderNine {s d : R} (hs : s*s = ((15:ℤ):R)) (hd : (den:R)*d = 1) :
    HasOrder 9 (A s d) (b s d) :=
  order_from_receipts receipts hs hd

def failed : FiniteRootedTree := bushyTree 5 ◂ bushyTree 5

private theorem failedNum :
    mul 15 (pack 3456) (numer 15 aNum bNum failed) =
      pack ((3456+1)*(den*scale den failed)) := by decide +kernel

theorem failedDefect {s d : R} (hs : s*s = ((15:ℤ):R)) (hd : (den:R)*d = 1) :
    ((3456:ℤ):R) * ((failed.factorial : R) * (b s d ⬝ᵥ Φ failed (A s d)) - 1) = 1 := by
  have he := ERKQuadraticIntegerReplay.exact_defect den 3456 (δ := 15) hs d hd
    aNum bNum failed failedNum
  have eA : tableau s d aNum = A s d := by
    ext i j
    simp [tableau,A,rawA,mul_comm]
  have eb : weights s d bNum = b s d := by
    funext i
    simp [weights,b,rawB,mul_comm]
  rwa [eA,eb] at he

theorem exactOverReal : ∃ (U : Matrix (Fin 14) (Fin 14) ℝ) (v : Fin 14 → ℝ),
    ERK U ∧ HasOrder 9 U v ∧ ¬ HasOrder 10 U v := by
  let s : ℝ := Real.sqrt 15
  let d : ℝ := (den : ℝ)⁻¹
  have hs : s*s = ((15:ℤ):ℝ) := by
    simp [s, ← pow_two]
  have hd : (den:ℝ)*d = 1 := by
    exact mul_inv_cancel₀ (by norm_num [den])
  refine ⟨A s d, b s d, explicit s d, orderNine hs hd, ?_⟩
  intro hu
  have he := failedDefect hs hd
  rw [hu failed (by decide +kernel),sub_self,mul_zero] at he
  exact zero_ne_one he

end RKResearch.Certified.ERK149QuadraticMemo
