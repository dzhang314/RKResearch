module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceShards
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDataHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

abbrev original : RationalFitCover (Option (Fin 7)) 7 4 := DataHigh.table
abbrev useStop : (Option (Fin 7)) → Bool := exteriorStopAllowed true
abbrev claimTest : FitClaim (Option (Fin 7)) 7 4 → Bool :=
  exteriorClaimTest referenceJList referenceN₁List original.den true
abbrev stripTest : RationalStripFrame 7 → Bool :=
  RationalStripFrame.check true referenceJList referenceN₁List original.den

def fits00 : List (Finset (Option (Fin 7))) :=
  [{some 0,some 1,some 2,some 3},{some 0,some 1,some 2,some 4},{some 0,some 1,some 2,some 5},{some 0,some 1,some 2,some 6},{some 0,some 1,some 3,some 4},{some 0,some 1,some 3,some 5},{some 0,some 1,some 3,some 6},{some 0,some 1,some 4,some 5},{some 0,some 1,some 4,some 6},{some 0,some 1,some 5,some 6},{some 0,some 2,some 3,some 4},{some 0,some 2,some 3,some 5},{some 0,some 2,some 3,some 6},{some 0,some 2,some 4,some 5},{some 0,some 2,some 4,some 6},{some 0,some 2,some 5,some 6},{some 0,some 3,some 4,some 5},{some 0,some 3,some 4,some 6},{some 0,some 3,some 5,some 6},{some 0,some 4,some 5,some 6},{some 1,some 2,some 3,some 4},{some 1,some 2,some 3,some 5},{some 1,some 2,some 3,some 6},{some 1,some 2,some 4,some 5},{some 1,some 2,some 4,some 6},{some 1,some 2,some 5,some 6},{some 1,some 3,some 4,some 5},{some 1,some 3,some 4,some 6},{some 1,some 3,some 5,some 6},{some 1,some 4,some 5,some 6},{some 2,some 3,some 4,some 5},{some 2,some 3,some 4,some 6},{some 2,some 3,some 5,some 6},{some 2,some 4,some 5,some 6},{some 3,some 4,some 5,some 6}]

def batch00 : FitBatch (Option (Fin 7)) := ⟨none,fits00⟩

private theorem batchGood00 : batch00.good 4=true := by
  decide

def fits01 : List (Finset (Option (Fin 7))) :=
  [{none,some 1,some 2,some 3},{none,some 1,some 2,some 4},{none,some 1,some 2,some 5},{none,some 1,some 2,some 6},{none,some 1,some 3,some 4},{none,some 1,some 3,some 5},{none,some 1,some 3,some 6},{none,some 1,some 4,some 5},{none,some 1,some 4,some 6},{none,some 1,some 5,some 6},{none,some 2,some 3,some 4},{none,some 2,some 3,some 5},{none,some 2,some 3,some 6},{none,some 2,some 4,some 5},{none,some 2,some 4,some 6},{none,some 2,some 5,some 6},{none,some 3,some 4,some 5},{none,some 3,some 4,some 6},{none,some 3,some 5,some 6},{none,some 4,some 5,some 6},{some 1,some 2,some 3,some 4},{some 1,some 2,some 3,some 5},{some 1,some 2,some 3,some 6},{some 1,some 2,some 4,some 5},{some 1,some 2,some 4,some 6},{some 1,some 2,some 5,some 6},{some 1,some 3,some 4,some 5},{some 1,some 3,some 4,some 6},{some 1,some 3,some 5,some 6},{some 1,some 4,some 5,some 6},{some 2,some 3,some 4,some 5},{some 2,some 3,some 4,some 6},{some 2,some 3,some 5,some 6},{some 2,some 4,some 5,some 6},{some 3,some 4,some 5,some 6}]

def batch01 : FitBatch (Option (Fin 7)) := ⟨some 0,fits01⟩

private theorem batchGood01 : batch01.good 4=true := by
  decide

def fits02 : List (Finset (Option (Fin 7))) :=
  [{none,some 0,some 2,some 3},{none,some 0,some 2,some 4},{none,some 0,some 2,some 5},{none,some 0,some 2,some 6},{none,some 0,some 3,some 4},{none,some 0,some 3,some 5},{none,some 0,some 3,some 6},{none,some 0,some 4,some 5},{none,some 0,some 4,some 6},{none,some 0,some 5,some 6},{none,some 2,some 3,some 4},{none,some 2,some 3,some 5},{none,some 2,some 3,some 6},{none,some 2,some 4,some 5},{none,some 2,some 4,some 6},{none,some 2,some 5,some 6},{none,some 3,some 4,some 5},{none,some 3,some 4,some 6},{none,some 3,some 5,some 6},{none,some 4,some 5,some 6},{some 0,some 2,some 3,some 4},{some 0,some 2,some 3,some 5},{some 0,some 2,some 3,some 6},{some 0,some 2,some 4,some 5},{some 0,some 2,some 4,some 6},{some 0,some 2,some 5,some 6},{some 0,some 3,some 4,some 5},{some 0,some 3,some 4,some 6},{some 0,some 3,some 5,some 6},{some 0,some 4,some 5,some 6},{some 2,some 3,some 4,some 5},{some 2,some 3,some 4,some 6},{some 2,some 3,some 5,some 6},{some 2,some 4,some 5,some 6},{some 3,some 4,some 5,some 6}]

def batch02 : FitBatch (Option (Fin 7)) := ⟨some 1,fits02⟩

private theorem batchGood02 : batch02.good 4=true := by
  decide

def fits03 : List (Finset (Option (Fin 7))) :=
  [{none,some 0,some 1,some 3},{none,some 0,some 1,some 4},{none,some 0,some 1,some 5},{none,some 0,some 1,some 6},{none,some 0,some 3,some 4},{none,some 0,some 3,some 5},{none,some 0,some 3,some 6},{none,some 0,some 4,some 5},{none,some 0,some 4,some 6},{none,some 0,some 5,some 6},{none,some 1,some 3,some 4},{none,some 1,some 3,some 5},{none,some 1,some 3,some 6},{none,some 1,some 4,some 5},{none,some 1,some 4,some 6},{none,some 1,some 5,some 6},{none,some 3,some 4,some 5},{none,some 3,some 4,some 6},{none,some 3,some 5,some 6},{none,some 4,some 5,some 6},{some 0,some 1,some 3,some 4},{some 0,some 1,some 3,some 5},{some 0,some 1,some 3,some 6},{some 0,some 1,some 4,some 5},{some 0,some 1,some 4,some 6},{some 0,some 1,some 5,some 6},{some 0,some 3,some 4,some 5},{some 0,some 3,some 4,some 6},{some 0,some 3,some 5,some 6},{some 0,some 4,some 5,some 6},{some 1,some 3,some 4,some 5},{some 1,some 3,some 4,some 6},{some 1,some 3,some 5,some 6},{some 1,some 4,some 5,some 6},{some 3,some 4,some 5,some 6}]

def batch03 : FitBatch (Option (Fin 7)) := ⟨some 2,fits03⟩

private theorem batchGood03 : batch03.good 4=true := by
  decide

def fits04 : List (Finset (Option (Fin 7))) :=
  [{none,some 0,some 1,some 2},{none,some 0,some 1,some 4},{none,some 0,some 1,some 5},{none,some 0,some 1,some 6},{none,some 0,some 2,some 4},{none,some 0,some 2,some 5},{none,some 0,some 2,some 6},{none,some 0,some 4,some 5},{none,some 0,some 4,some 6},{none,some 0,some 5,some 6},{none,some 1,some 2,some 4},{none,some 1,some 2,some 5},{none,some 1,some 2,some 6},{none,some 1,some 4,some 5},{none,some 1,some 4,some 6},{none,some 1,some 5,some 6},{none,some 2,some 4,some 5},{none,some 2,some 4,some 6},{none,some 2,some 5,some 6},{none,some 4,some 5,some 6},{some 0,some 1,some 2,some 4},{some 0,some 1,some 2,some 5},{some 0,some 1,some 2,some 6},{some 0,some 1,some 4,some 5},{some 0,some 1,some 4,some 6},{some 0,some 1,some 5,some 6},{some 0,some 2,some 4,some 5},{some 0,some 2,some 4,some 6},{some 0,some 2,some 5,some 6},{some 0,some 4,some 5,some 6},{some 1,some 2,some 4,some 5},{some 1,some 2,some 4,some 6},{some 1,some 2,some 5,some 6},{some 1,some 4,some 5,some 6},{some 2,some 4,some 5,some 6}]

def batch04 : FitBatch (Option (Fin 7)) := ⟨some 3,fits04⟩

private theorem batchGood04 : batch04.good 4=true := by
  decide

def fits05 : List (Finset (Option (Fin 7))) :=
  [{none,some 0,some 1,some 2},{none,some 0,some 1,some 3},{none,some 0,some 1,some 5},{none,some 0,some 1,some 6},{none,some 0,some 2,some 3},{none,some 0,some 2,some 5},{none,some 0,some 2,some 6},{none,some 0,some 3,some 5},{none,some 0,some 3,some 6},{none,some 0,some 5,some 6},{none,some 1,some 2,some 3},{none,some 1,some 2,some 5},{none,some 1,some 2,some 6},{none,some 1,some 3,some 5},{none,some 1,some 3,some 6},{none,some 1,some 5,some 6},{none,some 2,some 3,some 5},{none,some 2,some 3,some 6},{none,some 2,some 5,some 6},{none,some 3,some 5,some 6},{some 0,some 1,some 2,some 3},{some 0,some 1,some 2,some 5},{some 0,some 1,some 2,some 6},{some 0,some 1,some 3,some 5},{some 0,some 1,some 3,some 6},{some 0,some 1,some 5,some 6},{some 0,some 2,some 3,some 5},{some 0,some 2,some 3,some 6},{some 0,some 2,some 5,some 6},{some 0,some 3,some 5,some 6},{some 1,some 2,some 3,some 5},{some 1,some 2,some 3,some 6},{some 1,some 2,some 5,some 6},{some 1,some 3,some 5,some 6},{some 2,some 3,some 5,some 6}]

def batch05 : FitBatch (Option (Fin 7)) := ⟨some 4,fits05⟩

private theorem batchGood05 : batch05.good 4=true := by
  decide

def fits06 : List (Finset (Option (Fin 7))) :=
  [{none,some 0,some 1,some 2},{none,some 0,some 1,some 3},{none,some 0,some 1,some 4},{none,some 0,some 1,some 6},{none,some 0,some 2,some 3},{none,some 0,some 2,some 4},{none,some 0,some 2,some 6},{none,some 0,some 3,some 4},{none,some 0,some 3,some 6},{none,some 0,some 4,some 6},{none,some 1,some 2,some 3},{none,some 1,some 2,some 4},{none,some 1,some 2,some 6},{none,some 1,some 3,some 4},{none,some 1,some 3,some 6},{none,some 1,some 4,some 6},{none,some 2,some 3,some 4},{none,some 2,some 3,some 6},{none,some 2,some 4,some 6},{none,some 3,some 4,some 6},{some 0,some 1,some 2,some 3},{some 0,some 1,some 2,some 4},{some 0,some 1,some 2,some 6},{some 0,some 1,some 3,some 4},{some 0,some 1,some 3,some 6},{some 0,some 1,some 4,some 6},{some 0,some 2,some 3,some 4},{some 0,some 2,some 3,some 6},{some 0,some 2,some 4,some 6},{some 0,some 3,some 4,some 6},{some 1,some 2,some 3,some 4},{some 1,some 2,some 3,some 6},{some 1,some 2,some 4,some 6},{some 1,some 3,some 4,some 6},{some 2,some 3,some 4,some 6}]

def batch06 : FitBatch (Option (Fin 7)) := ⟨some 5,fits06⟩

private theorem batchGood06 : batch06.good 4=true := by
  decide

def fits07 : List (Finset (Option (Fin 7))) :=
  [{none,some 0,some 1,some 2},{none,some 0,some 1,some 3},{none,some 0,some 1,some 4},{none,some 0,some 1,some 5},{none,some 0,some 2,some 3},{none,some 0,some 2,some 4},{none,some 0,some 2,some 5},{none,some 0,some 3,some 4},{none,some 0,some 3,some 5},{none,some 0,some 4,some 5},{none,some 1,some 2,some 3},{none,some 1,some 2,some 4},{none,some 1,some 2,some 5},{none,some 1,some 3,some 4},{none,some 1,some 3,some 5},{none,some 1,some 4,some 5},{none,some 2,some 3,some 4},{none,some 2,some 3,some 5},{none,some 2,some 4,some 5},{none,some 3,some 4,some 5},{some 0,some 1,some 2,some 3},{some 0,some 1,some 2,some 4},{some 0,some 1,some 2,some 5},{some 0,some 1,some 3,some 4},{some 0,some 1,some 3,some 5},{some 0,some 1,some 4,some 5},{some 0,some 2,some 3,some 4},{some 0,some 2,some 3,some 5},{some 0,some 2,some 4,some 5},{some 0,some 3,some 4,some 5},{some 1,some 2,some 3,some 4},{some 1,some 2,some 3,some 5},{some 1,some 2,some 4,some 5},{some 1,some 3,some 4,some 5},{some 2,some 3,some 4,some 5}]

def batch07 : FitBatch (Option (Fin 7)) := ⟨some 6,fits07⟩

private theorem batchGood07 : batch07.good 4=true := by
  decide

def plan : List (FitBatch (Option (Fin 7))) := [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07]

private theorem goodBatches : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.good 4)=true := by
  simp only [List.all_cons,List.all_nil,batchGood00,batchGood01,batchGood02,batchGood03,batchGood04,batchGood05,batchGood06,batchGood07,Bool.and_self]

private theorem enoughStops : decide (∀ j : (Option (Fin 7)),
    useStop j=true → plan.any (fun b => decide (b.stop=j))=true)=true := by
  decide

theorem planChecked : batchPlanCheck 4 useStop plan=true :=
  Bool.and_eq_true_iff.mpr ⟨goodBatches,enoughStops⟩


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
