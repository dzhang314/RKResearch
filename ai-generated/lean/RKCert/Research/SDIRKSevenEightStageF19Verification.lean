module
public import RKCert.Research.SDIRKSevenEightStageF19Receipts
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.SDIRKSeven.F19

def validBlock (z : Fin 19) : Bool :=
  (receipts z).all (fun s => decide (valid s.1 s.2))

set_option maxHeartbeats 0
set_option maxRecDepth 16000
private theorem validBlock0 : validBlock 0 = true := by decide +kernel
private theorem validBlock1 : validBlock 1 = true := by decide +kernel
private theorem validBlock2 : validBlock 2 = true := by decide +kernel
private theorem validBlock3 : validBlock 3 = true := by decide +kernel
private theorem validBlock4 : validBlock 4 = true := by decide +kernel
private theorem validBlock5 : validBlock 5 = true := by decide +kernel
private theorem validBlock6 : validBlock 6 = true := by decide +kernel
private theorem validBlock7 : validBlock 7 = true := by decide +kernel
private theorem validBlock8 : validBlock 8 = true := by decide +kernel
private theorem validBlock9 : validBlock 9 = true := by decide +kernel
private theorem validBlock10 : validBlock 10 = true := by decide +kernel
private theorem validBlock11 : validBlock 11 = true := by decide +kernel
private theorem validBlock12 : validBlock 12 = true := by decide +kernel
private theorem validBlock13 : validBlock 13 = true := by decide +kernel
private theorem validBlock14 : validBlock 14 = true := by decide +kernel
private theorem validBlock15 : validBlock 15 = true := by decide +kernel
private theorem validBlock16 : validBlock 16 = true := by decide +kernel
private theorem validBlock17 : validBlock 17 = true := by decide +kernel
private theorem validBlock18 : validBlock 18 = true := by decide +kernel

theorem finite_validity (z : Fin 19) : validBlock z=true := by
  fin_cases z
  · exact validBlock0
  · exact validBlock1
  · exact validBlock2
  · exact validBlock3
  · exact validBlock4
  · exact validBlock5
  · exact validBlock6
  · exact validBlock7
  · exact validBlock8
  · exact validBlock9
  · exact validBlock10
  · exact validBlock11
  · exact validBlock12
  · exact validBlock13
  · exact validBlock14
  · exact validBlock15
  · exact validBlock16
  · exact validBlock17
  · exact validBlock18

end RKResearch.Certified.SDIRKSeven.F19
