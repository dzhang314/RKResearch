module

public import Certificate11
import all Certificate11
public import RKCert.ReviewedNative.GramLocalPurity
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.Seed11Donors

open RootedTreeGram TwoDonorDense
open StrictSDIRKGram26Order11

theorem clockVec : TwoDonorDense.clocks A = StrictSDIRKGram26Order11.clocks := clocksEq

theorem clock18 : TwoDonorDense.clocks A (18 : Fin 26) = (-9 : ℚ) := by
  unfold TwoDonorDense.clocks
  rw [clocksEq]
  decide +kernel

theorem clock19 : TwoDonorDense.clocks A (19 : Fin 26) = (-11 : ℚ) := by
  unfold TwoDonorDense.clocks
  rw [clocksEq]
  decide +kernel

theorem clock20 : TwoDonorDense.clocks A (20 : Fin 26) = (251647454237400205 / 337389807870474227 : ℚ) := by
  unfold TwoDonorDense.clocks
  rw [clocksEq]
  decide +kernel

set_option maxHeartbeats 7000000
set_option maxRecDepth 16000
set_option Elab.async false

private theorem local18 (g : Fin 7) :
    energy (cov g.val) (localForm (18 : Fin 26) (-9) 1 g.val) = 0 := by
  fin_cases g <;> decide +kernel
private theorem local19 (g : Fin 7) :
    energy (cov g.val) (localForm (19 : Fin 26) (-11) 1 g.val) = 0 := by
  fin_cases g <;> decide +kernel
private theorem local20 (g : Fin 7) :
    energy (cov g.val) (localForm (20 : Fin 26) 251647454237400205 337389807870474227 g.val) = 0 := by
  fin_cases g <;> decide +kernel

theorem pure18 : PureAt A (18 : Fin 26) 7 :=
  trace.pureAt_of_local castA (by decide +kernel) 18 (-9) 1 (by decide +kernel)
    (by simpa using clock18) (by decide) (fun g hg => local18 ⟨g,hg⟩)
theorem pure19 : PureAt A (19 : Fin 26) 7 :=
  trace.pureAt_of_local castA (by decide +kernel) 19 (-11) 1 (by decide +kernel)
    (by simpa using clock19) (by decide) (fun g hg => local19 ⟨g,hg⟩)
theorem pure20 : PureAt A (20 : Fin 26) 7 :=
  trace.pureAt_of_local castA (by decide +kernel) 20 251647454237400205 337389807870474227 (by decide +kernel)
    (by simpa using clock20) (by decide) (fun g hg => local20 ⟨g,hg⟩)

#print axioms pure18
#print axioms pure19
#print axioms pure20
end RKResearch.Certified.Seed11Donors
