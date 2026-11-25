module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceShards
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDataCubic

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Cubic
open RKCert.ReviewedNative.WeakFourFirstOnly.DataCubic
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

abbrev original : RationalFitCover (Fin 7) 7 3 := DataCubic.table
abbrev useStop : (Fin 7) → Bool := fun _ => true
abbrev claimTest : FitClaim (Fin 7) 7 3 → Bool :=
  ordinaryClaimTest
abbrev stripTest : RationalStripFrame 7 → Bool :=
  RationalStripFrame.check false referenceJList referenceJList original.den

def fits00 : List (Finset (Fin 7)) :=
  [{1,2,3},{1,2,4},{1,2,5},{1,2,6},{1,3,4},{1,3,5},{1,3,6},{1,4,5},{1,4,6},{1,5,6},{2,3,4},{2,3,5},{2,3,6},{2,4,5},{2,4,6},{2,5,6},{3,4,5},{3,4,6},{3,5,6},{4,5,6}]

def batch00 : FitBatch (Fin 7) := ⟨0,fits00⟩

private theorem batchGood00 : batch00.good 3=true := by
  decide

def fits01 : List (Finset (Fin 7)) :=
  [{0,2,3},{0,2,4},{0,2,5},{0,2,6},{0,3,4},{0,3,5},{0,3,6},{0,4,5},{0,4,6},{0,5,6},{2,3,4},{2,3,5},{2,3,6},{2,4,5},{2,4,6},{2,5,6},{3,4,5},{3,4,6},{3,5,6},{4,5,6}]

def batch01 : FitBatch (Fin 7) := ⟨1,fits01⟩

private theorem batchGood01 : batch01.good 3=true := by
  decide

def fits02 : List (Finset (Fin 7)) :=
  [{0,1,3},{0,1,4},{0,1,5},{0,1,6},{0,3,4},{0,3,5},{0,3,6},{0,4,5},{0,4,6},{0,5,6},{1,3,4},{1,3,5},{1,3,6},{1,4,5},{1,4,6},{1,5,6},{3,4,5},{3,4,6},{3,5,6},{4,5,6}]

def batch02 : FitBatch (Fin 7) := ⟨2,fits02⟩

private theorem batchGood02 : batch02.good 3=true := by
  decide

def fits03 : List (Finset (Fin 7)) :=
  [{0,1,2},{0,1,4},{0,1,5},{0,1,6},{0,2,4},{0,2,5},{0,2,6},{0,4,5},{0,4,6},{0,5,6},{1,2,4},{1,2,5},{1,2,6},{1,4,5},{1,4,6},{1,5,6},{2,4,5},{2,4,6},{2,5,6},{4,5,6}]

def batch03 : FitBatch (Fin 7) := ⟨3,fits03⟩

private theorem batchGood03 : batch03.good 3=true := by
  decide

def fits04 : List (Finset (Fin 7)) :=
  [{0,1,2},{0,1,3},{0,1,5},{0,1,6},{0,2,3},{0,2,5},{0,2,6},{0,3,5},{0,3,6},{0,5,6},{1,2,3},{1,2,5},{1,2,6},{1,3,5},{1,3,6},{1,5,6},{2,3,5},{2,3,6},{2,5,6},{3,5,6}]

def batch04 : FitBatch (Fin 7) := ⟨4,fits04⟩

private theorem batchGood04 : batch04.good 3=true := by
  decide

def fits05 : List (Finset (Fin 7)) :=
  [{0,1,2},{0,1,3},{0,1,4},{0,1,6},{0,2,3},{0,2,4},{0,2,6},{0,3,4},{0,3,6},{0,4,6},{1,2,3},{1,2,4},{1,2,6},{1,3,4},{1,3,6},{1,4,6},{2,3,4},{2,3,6},{2,4,6},{3,4,6}]

def batch05 : FitBatch (Fin 7) := ⟨5,fits05⟩

private theorem batchGood05 : batch05.good 3=true := by
  decide

def fits06 : List (Finset (Fin 7)) :=
  [{0,1,2},{0,1,3},{0,1,4},{0,1,5},{0,2,3},{0,2,4},{0,2,5},{0,3,4},{0,3,5},{0,4,5},{1,2,3},{1,2,4},{1,2,5},{1,3,4},{1,3,5},{1,4,5},{2,3,4},{2,3,5},{2,4,5},{3,4,5}]

def batch06 : FitBatch (Fin 7) := ⟨6,fits06⟩

private theorem batchGood06 : batch06.good 3=true := by
  decide

def plan : List (FitBatch (Fin 7)) := [batch00,batch01,batch02,batch03,batch04,batch05,batch06]

private theorem goodBatches : [batch00,batch01,batch02,batch03,batch04,batch05,batch06].all (FitBatch.good 3)=true := by
  simp only [List.all_cons,List.all_nil,batchGood00,batchGood01,batchGood02,batchGood03,batchGood04,batchGood05,batchGood06,Bool.and_self]

private theorem enoughStops : decide (∀ j : (Fin 7),
    useStop j=true → plan.any (fun b => decide (b.stop=j))=true)=true := by
  decide

theorem planChecked : batchPlanCheck 3 useStop plan=true :=
  Bool.and_eq_true_iff.mpr ⟨goodBatches,enoughStops⟩


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Cubic
