module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK034 : stripTest frame71=true := by decide +kernel

theorem spanOK034 : checkChain 1712 1704 [frame71.span]=true := by decide +kernel

private theorem guideAt034 : List.lookup frame71.span.1 guideTable=some guide034 := by
  decide +kernel

private theorem scoped034 : original.guide frame71.span.1 =
    (fun z => List.lookup (guideCode z) guide034) := by
  funext z
  change (List.lookup frame71.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide034
  simp only [guideAt034,Option.bind_some]

private abbrev frame034test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch00.stop,F)

private theorem frame034scope00_s000 : ((fits00.drop 0).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s004 : ((fits00.drop 4).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s008 : ((fits00.drop 8).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s012 : ((fits00.drop 12).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s016 : ((fits00.drop 16).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s020 : ((fits00.drop 20).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s024 : ((fits00.drop 24).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s028 : ((fits00.drop 28).take 4).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_s032 : ((fits00.drop 32).take 3).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00_end : (fits00.drop 35).all frame034test00=true := by
  decide +kernel

private theorem frame034scope00 : fits00.all frame034test00=true := by
  have h32 := stitchAt 32 3 frame034scope00_s032 frame034scope00_end
  have h28 := stitchAt 28 4 frame034scope00_s028 h32
  have h24 := stitchAt 24 4 frame034scope00_s024 h28
  have h20 := stitchAt 20 4 frame034scope00_s020 h24
  have h16 := stitchAt 16 4 frame034scope00_s016 h20
  have h12 := stitchAt 12 4 frame034scope00_s012 h16
  have h8 := stitchAt 8 4 frame034scope00_s008 h12
  have h4 := stitchAt 4 4 frame034scope00_s004 h8
  have h0 := stitchAt 0 4 frame034scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch00 : batch00.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope00

private abbrev frame034test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch01.stop,F)

private theorem frame034scope01_s000 : ((fits01.drop 0).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s004 : ((fits01.drop 4).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s008 : ((fits01.drop 8).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s012 : ((fits01.drop 12).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s016 : ((fits01.drop 16).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s020 : ((fits01.drop 20).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s024 : ((fits01.drop 24).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s028 : ((fits01.drop 28).take 4).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_s032 : ((fits01.drop 32).take 3).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01_end : (fits01.drop 35).all frame034test01=true := by
  decide +kernel

private theorem frame034scope01 : fits01.all frame034test01=true := by
  have h32 := stitchAt 32 3 frame034scope01_s032 frame034scope01_end
  have h28 := stitchAt 28 4 frame034scope01_s028 h32
  have h24 := stitchAt 24 4 frame034scope01_s024 h28
  have h20 := stitchAt 20 4 frame034scope01_s020 h24
  have h16 := stitchAt 16 4 frame034scope01_s016 h20
  have h12 := stitchAt 12 4 frame034scope01_s012 h16
  have h8 := stitchAt 8 4 frame034scope01_s008 h12
  have h4 := stitchAt 4 4 frame034scope01_s004 h8
  have h0 := stitchAt 0 4 frame034scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch01 : batch01.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope01

private abbrev frame034test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch02.stop,F)

private theorem frame034scope02_s000 : ((fits02.drop 0).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s004 : ((fits02.drop 4).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s008 : ((fits02.drop 8).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s012 : ((fits02.drop 12).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s016 : ((fits02.drop 16).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s020 : ((fits02.drop 20).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s024 : ((fits02.drop 24).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s028 : ((fits02.drop 28).take 4).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_s032 : ((fits02.drop 32).take 3).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02_end : (fits02.drop 35).all frame034test02=true := by
  decide +kernel

private theorem frame034scope02 : fits02.all frame034test02=true := by
  have h32 := stitchAt 32 3 frame034scope02_s032 frame034scope02_end
  have h28 := stitchAt 28 4 frame034scope02_s028 h32
  have h24 := stitchAt 24 4 frame034scope02_s024 h28
  have h20 := stitchAt 20 4 frame034scope02_s020 h24
  have h16 := stitchAt 16 4 frame034scope02_s016 h20
  have h12 := stitchAt 12 4 frame034scope02_s012 h16
  have h8 := stitchAt 8 4 frame034scope02_s008 h12
  have h4 := stitchAt 4 4 frame034scope02_s004 h8
  have h0 := stitchAt 0 4 frame034scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch02 : batch02.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope02

private abbrev frame034test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch03.stop,F)

private theorem frame034scope03_s000 : ((fits03.drop 0).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s004 : ((fits03.drop 4).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s008 : ((fits03.drop 8).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s012 : ((fits03.drop 12).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s016 : ((fits03.drop 16).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s020 : ((fits03.drop 20).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s024 : ((fits03.drop 24).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s028 : ((fits03.drop 28).take 4).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_s032 : ((fits03.drop 32).take 3).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03_end : (fits03.drop 35).all frame034test03=true := by
  decide +kernel

private theorem frame034scope03 : fits03.all frame034test03=true := by
  have h32 := stitchAt 32 3 frame034scope03_s032 frame034scope03_end
  have h28 := stitchAt 28 4 frame034scope03_s028 h32
  have h24 := stitchAt 24 4 frame034scope03_s024 h28
  have h20 := stitchAt 20 4 frame034scope03_s020 h24
  have h16 := stitchAt 16 4 frame034scope03_s016 h20
  have h12 := stitchAt 12 4 frame034scope03_s012 h16
  have h8 := stitchAt 8 4 frame034scope03_s008 h12
  have h4 := stitchAt 4 4 frame034scope03_s004 h8
  have h0 := stitchAt 0 4 frame034scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch03 : batch03.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope03

private abbrev frame034test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch04.stop,F)

private theorem frame034scope04_s000 : ((fits04.drop 0).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s004 : ((fits04.drop 4).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s008 : ((fits04.drop 8).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s012 : ((fits04.drop 12).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s016 : ((fits04.drop 16).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s020 : ((fits04.drop 20).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s024 : ((fits04.drop 24).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s028 : ((fits04.drop 28).take 4).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_s032 : ((fits04.drop 32).take 3).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04_end : (fits04.drop 35).all frame034test04=true := by
  decide +kernel

private theorem frame034scope04 : fits04.all frame034test04=true := by
  have h32 := stitchAt 32 3 frame034scope04_s032 frame034scope04_end
  have h28 := stitchAt 28 4 frame034scope04_s028 h32
  have h24 := stitchAt 24 4 frame034scope04_s024 h28
  have h20 := stitchAt 20 4 frame034scope04_s020 h24
  have h16 := stitchAt 16 4 frame034scope04_s016 h20
  have h12 := stitchAt 12 4 frame034scope04_s012 h16
  have h8 := stitchAt 8 4 frame034scope04_s008 h12
  have h4 := stitchAt 4 4 frame034scope04_s004 h8
  have h0 := stitchAt 0 4 frame034scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch04 : batch04.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope04

private abbrev frame034test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch05.stop,F)

private theorem frame034scope05_s000 : ((fits05.drop 0).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s004 : ((fits05.drop 4).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s008 : ((fits05.drop 8).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s012 : ((fits05.drop 12).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s016 : ((fits05.drop 16).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s020 : ((fits05.drop 20).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s024 : ((fits05.drop 24).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s028 : ((fits05.drop 28).take 4).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_s032 : ((fits05.drop 32).take 3).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05_end : (fits05.drop 35).all frame034test05=true := by
  decide +kernel

private theorem frame034scope05 : fits05.all frame034test05=true := by
  have h32 := stitchAt 32 3 frame034scope05_s032 frame034scope05_end
  have h28 := stitchAt 28 4 frame034scope05_s028 h32
  have h24 := stitchAt 24 4 frame034scope05_s024 h28
  have h20 := stitchAt 20 4 frame034scope05_s020 h24
  have h16 := stitchAt 16 4 frame034scope05_s016 h20
  have h12 := stitchAt 12 4 frame034scope05_s012 h16
  have h8 := stitchAt 8 4 frame034scope05_s008 h12
  have h4 := stitchAt 4 4 frame034scope05_s004 h8
  have h0 := stitchAt 0 4 frame034scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch05 : batch05.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope05

private abbrev frame034test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch06.stop,F)

private theorem frame034scope06_s000 : ((fits06.drop 0).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s004 : ((fits06.drop 4).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s008 : ((fits06.drop 8).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s012 : ((fits06.drop 12).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s016 : ((fits06.drop 16).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s020 : ((fits06.drop 20).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s024 : ((fits06.drop 24).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s028 : ((fits06.drop 28).take 4).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_s032 : ((fits06.drop 32).take 3).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06_end : (fits06.drop 35).all frame034test06=true := by
  decide +kernel

private theorem frame034scope06 : fits06.all frame034test06=true := by
  have h32 := stitchAt 32 3 frame034scope06_s032 frame034scope06_end
  have h28 := stitchAt 28 4 frame034scope06_s028 h32
  have h24 := stitchAt 24 4 frame034scope06_s024 h28
  have h20 := stitchAt 20 4 frame034scope06_s020 h24
  have h16 := stitchAt 16 4 frame034scope06_s016 h20
  have h12 := stitchAt 12 4 frame034scope06_s012 h16
  have h8 := stitchAt 8 4 frame034scope06_s008 h12
  have h4 := stitchAt 4 4 frame034scope06_s004 h8
  have h0 := stitchAt 0 4 frame034scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch06 : batch06.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope06

private abbrev frame034test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame71 (fun z => List.lookup (guideCode z) guide034)
    (batch07.stop,F)

private theorem frame034scope07_s000 : ((fits07.drop 0).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s004 : ((fits07.drop 4).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s008 : ((fits07.drop 8).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s012 : ((fits07.drop 12).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s016 : ((fits07.drop 16).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s020 : ((fits07.drop 20).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s024 : ((fits07.drop 24).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s028 : ((fits07.drop 28).take 4).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_s032 : ((fits07.drop 32).take 3).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07_end : (fits07.drop 35).all frame034test07=true := by
  decide +kernel

private theorem frame034scope07 : fits07.all frame034test07=true := by
  have h32 := stitchAt 32 3 frame034scope07_s032 frame034scope07_end
  have h28 := stitchAt 28 4 frame034scope07_s028 h32
  have h24 := stitchAt 24 4 frame034scope07_s024 h28
  have h20 := stitchAt 20 4 frame034scope07_s020 h24
  have h16 := stitchAt 16 4 frame034scope07_s016 h20
  have h12 := stitchAt 12 4 frame034scope07_s012 h16
  have h8 := stitchAt 8 4 frame034scope07_s008 h12
  have h4 := stitchAt 4 4 frame034scope07_s004 h8
  have h0 := stitchAt 0 4 frame034scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame034batch07 : batch07.pickTest original frame71=true :=
  FitBatch.pickTest_of_scoped scoped034 frame034scope07

private theorem frameBatches034 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame71)=true := by
  simp only [List.all_cons,List.all_nil,frame034batch00,frame034batch01,frame034batch02,frame034batch03,frame034batch04,frame034batch05,frame034batch06,frame034batch07,Bool.and_self]

theorem frameOK034 : frameRankTest original useStop frame71=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches034

theorem stripOK035 : stripTest frame73=true := by decide +kernel

theorem spanOK035 : checkChain 1720 1712 [frame73.span]=true := by decide +kernel

private theorem guideAt035 : List.lookup frame73.span.1 guideTable=some guide035 := by
  decide +kernel

private theorem scoped035 : original.guide frame73.span.1 =
    (fun z => List.lookup (guideCode z) guide035) := by
  funext z
  change (List.lookup frame73.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide035
  simp only [guideAt035,Option.bind_some]

private abbrev frame035test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch00.stop,F)

private theorem frame035scope00_s000 : ((fits00.drop 0).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s004 : ((fits00.drop 4).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s008 : ((fits00.drop 8).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s012 : ((fits00.drop 12).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s016 : ((fits00.drop 16).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s020 : ((fits00.drop 20).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s024 : ((fits00.drop 24).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s028 : ((fits00.drop 28).take 4).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_s032 : ((fits00.drop 32).take 3).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00_end : (fits00.drop 35).all frame035test00=true := by
  decide +kernel

private theorem frame035scope00 : fits00.all frame035test00=true := by
  have h32 := stitchAt 32 3 frame035scope00_s032 frame035scope00_end
  have h28 := stitchAt 28 4 frame035scope00_s028 h32
  have h24 := stitchAt 24 4 frame035scope00_s024 h28
  have h20 := stitchAt 20 4 frame035scope00_s020 h24
  have h16 := stitchAt 16 4 frame035scope00_s016 h20
  have h12 := stitchAt 12 4 frame035scope00_s012 h16
  have h8 := stitchAt 8 4 frame035scope00_s008 h12
  have h4 := stitchAt 4 4 frame035scope00_s004 h8
  have h0 := stitchAt 0 4 frame035scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch00 : batch00.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope00

private abbrev frame035test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch01.stop,F)

private theorem frame035scope01_s000 : ((fits01.drop 0).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s004 : ((fits01.drop 4).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s008 : ((fits01.drop 8).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s012 : ((fits01.drop 12).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s016 : ((fits01.drop 16).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s020 : ((fits01.drop 20).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s024 : ((fits01.drop 24).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s028 : ((fits01.drop 28).take 4).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_s032 : ((fits01.drop 32).take 3).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01_end : (fits01.drop 35).all frame035test01=true := by
  decide +kernel

private theorem frame035scope01 : fits01.all frame035test01=true := by
  have h32 := stitchAt 32 3 frame035scope01_s032 frame035scope01_end
  have h28 := stitchAt 28 4 frame035scope01_s028 h32
  have h24 := stitchAt 24 4 frame035scope01_s024 h28
  have h20 := stitchAt 20 4 frame035scope01_s020 h24
  have h16 := stitchAt 16 4 frame035scope01_s016 h20
  have h12 := stitchAt 12 4 frame035scope01_s012 h16
  have h8 := stitchAt 8 4 frame035scope01_s008 h12
  have h4 := stitchAt 4 4 frame035scope01_s004 h8
  have h0 := stitchAt 0 4 frame035scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch01 : batch01.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope01

private abbrev frame035test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch02.stop,F)

private theorem frame035scope02_s000 : ((fits02.drop 0).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s004 : ((fits02.drop 4).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s008 : ((fits02.drop 8).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s012 : ((fits02.drop 12).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s016 : ((fits02.drop 16).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s020 : ((fits02.drop 20).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s024 : ((fits02.drop 24).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s028 : ((fits02.drop 28).take 4).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_s032 : ((fits02.drop 32).take 3).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02_end : (fits02.drop 35).all frame035test02=true := by
  decide +kernel

private theorem frame035scope02 : fits02.all frame035test02=true := by
  have h32 := stitchAt 32 3 frame035scope02_s032 frame035scope02_end
  have h28 := stitchAt 28 4 frame035scope02_s028 h32
  have h24 := stitchAt 24 4 frame035scope02_s024 h28
  have h20 := stitchAt 20 4 frame035scope02_s020 h24
  have h16 := stitchAt 16 4 frame035scope02_s016 h20
  have h12 := stitchAt 12 4 frame035scope02_s012 h16
  have h8 := stitchAt 8 4 frame035scope02_s008 h12
  have h4 := stitchAt 4 4 frame035scope02_s004 h8
  have h0 := stitchAt 0 4 frame035scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch02 : batch02.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope02

private abbrev frame035test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch03.stop,F)

private theorem frame035scope03_s000 : ((fits03.drop 0).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s004 : ((fits03.drop 4).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s008 : ((fits03.drop 8).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s012 : ((fits03.drop 12).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s016 : ((fits03.drop 16).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s020 : ((fits03.drop 20).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s024 : ((fits03.drop 24).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s028 : ((fits03.drop 28).take 4).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_s032 : ((fits03.drop 32).take 3).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03_end : (fits03.drop 35).all frame035test03=true := by
  decide +kernel

private theorem frame035scope03 : fits03.all frame035test03=true := by
  have h32 := stitchAt 32 3 frame035scope03_s032 frame035scope03_end
  have h28 := stitchAt 28 4 frame035scope03_s028 h32
  have h24 := stitchAt 24 4 frame035scope03_s024 h28
  have h20 := stitchAt 20 4 frame035scope03_s020 h24
  have h16 := stitchAt 16 4 frame035scope03_s016 h20
  have h12 := stitchAt 12 4 frame035scope03_s012 h16
  have h8 := stitchAt 8 4 frame035scope03_s008 h12
  have h4 := stitchAt 4 4 frame035scope03_s004 h8
  have h0 := stitchAt 0 4 frame035scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch03 : batch03.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope03

private abbrev frame035test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch04.stop,F)

private theorem frame035scope04_s000 : ((fits04.drop 0).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s004 : ((fits04.drop 4).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s008 : ((fits04.drop 8).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s012 : ((fits04.drop 12).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s016 : ((fits04.drop 16).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s020 : ((fits04.drop 20).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s024 : ((fits04.drop 24).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s028 : ((fits04.drop 28).take 4).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_s032 : ((fits04.drop 32).take 3).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04_end : (fits04.drop 35).all frame035test04=true := by
  decide +kernel

private theorem frame035scope04 : fits04.all frame035test04=true := by
  have h32 := stitchAt 32 3 frame035scope04_s032 frame035scope04_end
  have h28 := stitchAt 28 4 frame035scope04_s028 h32
  have h24 := stitchAt 24 4 frame035scope04_s024 h28
  have h20 := stitchAt 20 4 frame035scope04_s020 h24
  have h16 := stitchAt 16 4 frame035scope04_s016 h20
  have h12 := stitchAt 12 4 frame035scope04_s012 h16
  have h8 := stitchAt 8 4 frame035scope04_s008 h12
  have h4 := stitchAt 4 4 frame035scope04_s004 h8
  have h0 := stitchAt 0 4 frame035scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch04 : batch04.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope04

private abbrev frame035test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch05.stop,F)

private theorem frame035scope05_s000 : ((fits05.drop 0).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s004 : ((fits05.drop 4).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s008 : ((fits05.drop 8).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s012 : ((fits05.drop 12).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s016 : ((fits05.drop 16).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s020 : ((fits05.drop 20).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s024 : ((fits05.drop 24).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s028 : ((fits05.drop 28).take 4).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_s032 : ((fits05.drop 32).take 3).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05_end : (fits05.drop 35).all frame035test05=true := by
  decide +kernel

private theorem frame035scope05 : fits05.all frame035test05=true := by
  have h32 := stitchAt 32 3 frame035scope05_s032 frame035scope05_end
  have h28 := stitchAt 28 4 frame035scope05_s028 h32
  have h24 := stitchAt 24 4 frame035scope05_s024 h28
  have h20 := stitchAt 20 4 frame035scope05_s020 h24
  have h16 := stitchAt 16 4 frame035scope05_s016 h20
  have h12 := stitchAt 12 4 frame035scope05_s012 h16
  have h8 := stitchAt 8 4 frame035scope05_s008 h12
  have h4 := stitchAt 4 4 frame035scope05_s004 h8
  have h0 := stitchAt 0 4 frame035scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch05 : batch05.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope05

private abbrev frame035test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch06.stop,F)

private theorem frame035scope06_s000 : ((fits06.drop 0).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s004 : ((fits06.drop 4).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s008 : ((fits06.drop 8).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s012 : ((fits06.drop 12).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s016 : ((fits06.drop 16).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s020 : ((fits06.drop 20).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s024 : ((fits06.drop 24).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s028 : ((fits06.drop 28).take 4).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_s032 : ((fits06.drop 32).take 3).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06_end : (fits06.drop 35).all frame035test06=true := by
  decide +kernel

private theorem frame035scope06 : fits06.all frame035test06=true := by
  have h32 := stitchAt 32 3 frame035scope06_s032 frame035scope06_end
  have h28 := stitchAt 28 4 frame035scope06_s028 h32
  have h24 := stitchAt 24 4 frame035scope06_s024 h28
  have h20 := stitchAt 20 4 frame035scope06_s020 h24
  have h16 := stitchAt 16 4 frame035scope06_s016 h20
  have h12 := stitchAt 12 4 frame035scope06_s012 h16
  have h8 := stitchAt 8 4 frame035scope06_s008 h12
  have h4 := stitchAt 4 4 frame035scope06_s004 h8
  have h0 := stitchAt 0 4 frame035scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch06 : batch06.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope06

private abbrev frame035test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame73 (fun z => List.lookup (guideCode z) guide035)
    (batch07.stop,F)

private theorem frame035scope07_s000 : ((fits07.drop 0).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s004 : ((fits07.drop 4).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s008 : ((fits07.drop 8).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s012 : ((fits07.drop 12).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s016 : ((fits07.drop 16).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s020 : ((fits07.drop 20).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s024 : ((fits07.drop 24).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s028 : ((fits07.drop 28).take 4).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_s032 : ((fits07.drop 32).take 3).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07_end : (fits07.drop 35).all frame035test07=true := by
  decide +kernel

private theorem frame035scope07 : fits07.all frame035test07=true := by
  have h32 := stitchAt 32 3 frame035scope07_s032 frame035scope07_end
  have h28 := stitchAt 28 4 frame035scope07_s028 h32
  have h24 := stitchAt 24 4 frame035scope07_s024 h28
  have h20 := stitchAt 20 4 frame035scope07_s020 h24
  have h16 := stitchAt 16 4 frame035scope07_s016 h20
  have h12 := stitchAt 12 4 frame035scope07_s012 h16
  have h8 := stitchAt 8 4 frame035scope07_s008 h12
  have h4 := stitchAt 4 4 frame035scope07_s004 h8
  have h0 := stitchAt 0 4 frame035scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame035batch07 : batch07.pickTest original frame73=true :=
  FitBatch.pickTest_of_scoped scoped035 frame035scope07

private theorem frameBatches035 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame73)=true := by
  simp only [List.all_cons,List.all_nil,frame035batch00,frame035batch01,frame035batch02,frame035batch03,frame035batch04,frame035batch05,frame035batch06,frame035batch07,Bool.and_self]

theorem frameOK035 : frameRankTest original useStop frame73=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches035


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
