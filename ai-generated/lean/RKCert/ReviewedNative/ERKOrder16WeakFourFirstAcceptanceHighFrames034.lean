module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK068 : stripTest frame142=true := by decide +kernel

theorem spanOK068 : checkChain 1796 1792 [frame142.span]=true := by decide +kernel

private theorem guideAt068 : List.lookup frame142.span.1 guideTable=some guide068 := by
  decide +kernel

private theorem scoped068 : original.guide frame142.span.1 =
    (fun z => List.lookup (guideCode z) guide068) := by
  funext z
  change (List.lookup frame142.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide068
  simp only [guideAt068,Option.bind_some]

private abbrev frame068test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch00.stop,F)

private theorem frame068scope00_s000 : ((fits00.drop 0).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s004 : ((fits00.drop 4).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s008 : ((fits00.drop 8).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s012 : ((fits00.drop 12).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s016 : ((fits00.drop 16).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s020 : ((fits00.drop 20).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s024 : ((fits00.drop 24).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s028 : ((fits00.drop 28).take 4).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_s032 : ((fits00.drop 32).take 3).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00_end : (fits00.drop 35).all frame068test00=true := by
  decide +kernel

private theorem frame068scope00 : fits00.all frame068test00=true := by
  have h32 := stitchAt 32 3 frame068scope00_s032 frame068scope00_end
  have h28 := stitchAt 28 4 frame068scope00_s028 h32
  have h24 := stitchAt 24 4 frame068scope00_s024 h28
  have h20 := stitchAt 20 4 frame068scope00_s020 h24
  have h16 := stitchAt 16 4 frame068scope00_s016 h20
  have h12 := stitchAt 12 4 frame068scope00_s012 h16
  have h8 := stitchAt 8 4 frame068scope00_s008 h12
  have h4 := stitchAt 4 4 frame068scope00_s004 h8
  have h0 := stitchAt 0 4 frame068scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch00 : batch00.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope00

private abbrev frame068test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch01.stop,F)

private theorem frame068scope01_s000 : ((fits01.drop 0).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s004 : ((fits01.drop 4).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s008 : ((fits01.drop 8).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s012 : ((fits01.drop 12).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s016 : ((fits01.drop 16).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s020 : ((fits01.drop 20).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s024 : ((fits01.drop 24).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s028 : ((fits01.drop 28).take 4).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_s032 : ((fits01.drop 32).take 3).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01_end : (fits01.drop 35).all frame068test01=true := by
  decide +kernel

private theorem frame068scope01 : fits01.all frame068test01=true := by
  have h32 := stitchAt 32 3 frame068scope01_s032 frame068scope01_end
  have h28 := stitchAt 28 4 frame068scope01_s028 h32
  have h24 := stitchAt 24 4 frame068scope01_s024 h28
  have h20 := stitchAt 20 4 frame068scope01_s020 h24
  have h16 := stitchAt 16 4 frame068scope01_s016 h20
  have h12 := stitchAt 12 4 frame068scope01_s012 h16
  have h8 := stitchAt 8 4 frame068scope01_s008 h12
  have h4 := stitchAt 4 4 frame068scope01_s004 h8
  have h0 := stitchAt 0 4 frame068scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch01 : batch01.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope01

private abbrev frame068test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch02.stop,F)

private theorem frame068scope02_s000 : ((fits02.drop 0).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s004 : ((fits02.drop 4).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s008 : ((fits02.drop 8).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s012 : ((fits02.drop 12).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s016 : ((fits02.drop 16).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s020 : ((fits02.drop 20).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s024 : ((fits02.drop 24).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s028 : ((fits02.drop 28).take 4).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_s032 : ((fits02.drop 32).take 3).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02_end : (fits02.drop 35).all frame068test02=true := by
  decide +kernel

private theorem frame068scope02 : fits02.all frame068test02=true := by
  have h32 := stitchAt 32 3 frame068scope02_s032 frame068scope02_end
  have h28 := stitchAt 28 4 frame068scope02_s028 h32
  have h24 := stitchAt 24 4 frame068scope02_s024 h28
  have h20 := stitchAt 20 4 frame068scope02_s020 h24
  have h16 := stitchAt 16 4 frame068scope02_s016 h20
  have h12 := stitchAt 12 4 frame068scope02_s012 h16
  have h8 := stitchAt 8 4 frame068scope02_s008 h12
  have h4 := stitchAt 4 4 frame068scope02_s004 h8
  have h0 := stitchAt 0 4 frame068scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch02 : batch02.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope02

private abbrev frame068test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch03.stop,F)

private theorem frame068scope03_s000 : ((fits03.drop 0).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s004 : ((fits03.drop 4).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s008 : ((fits03.drop 8).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s012 : ((fits03.drop 12).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s016 : ((fits03.drop 16).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s020 : ((fits03.drop 20).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s024 : ((fits03.drop 24).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s028 : ((fits03.drop 28).take 4).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_s032 : ((fits03.drop 32).take 3).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03_end : (fits03.drop 35).all frame068test03=true := by
  decide +kernel

private theorem frame068scope03 : fits03.all frame068test03=true := by
  have h32 := stitchAt 32 3 frame068scope03_s032 frame068scope03_end
  have h28 := stitchAt 28 4 frame068scope03_s028 h32
  have h24 := stitchAt 24 4 frame068scope03_s024 h28
  have h20 := stitchAt 20 4 frame068scope03_s020 h24
  have h16 := stitchAt 16 4 frame068scope03_s016 h20
  have h12 := stitchAt 12 4 frame068scope03_s012 h16
  have h8 := stitchAt 8 4 frame068scope03_s008 h12
  have h4 := stitchAt 4 4 frame068scope03_s004 h8
  have h0 := stitchAt 0 4 frame068scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch03 : batch03.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope03

private abbrev frame068test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch04.stop,F)

private theorem frame068scope04_s000 : ((fits04.drop 0).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s004 : ((fits04.drop 4).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s008 : ((fits04.drop 8).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s012 : ((fits04.drop 12).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s016 : ((fits04.drop 16).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s020 : ((fits04.drop 20).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s024 : ((fits04.drop 24).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s028 : ((fits04.drop 28).take 4).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_s032 : ((fits04.drop 32).take 3).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04_end : (fits04.drop 35).all frame068test04=true := by
  decide +kernel

private theorem frame068scope04 : fits04.all frame068test04=true := by
  have h32 := stitchAt 32 3 frame068scope04_s032 frame068scope04_end
  have h28 := stitchAt 28 4 frame068scope04_s028 h32
  have h24 := stitchAt 24 4 frame068scope04_s024 h28
  have h20 := stitchAt 20 4 frame068scope04_s020 h24
  have h16 := stitchAt 16 4 frame068scope04_s016 h20
  have h12 := stitchAt 12 4 frame068scope04_s012 h16
  have h8 := stitchAt 8 4 frame068scope04_s008 h12
  have h4 := stitchAt 4 4 frame068scope04_s004 h8
  have h0 := stitchAt 0 4 frame068scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch04 : batch04.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope04

private abbrev frame068test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch05.stop,F)

private theorem frame068scope05_s000 : ((fits05.drop 0).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s004 : ((fits05.drop 4).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s008 : ((fits05.drop 8).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s012 : ((fits05.drop 12).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s016 : ((fits05.drop 16).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s020 : ((fits05.drop 20).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s024 : ((fits05.drop 24).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s028 : ((fits05.drop 28).take 4).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_s032 : ((fits05.drop 32).take 3).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05_end : (fits05.drop 35).all frame068test05=true := by
  decide +kernel

private theorem frame068scope05 : fits05.all frame068test05=true := by
  have h32 := stitchAt 32 3 frame068scope05_s032 frame068scope05_end
  have h28 := stitchAt 28 4 frame068scope05_s028 h32
  have h24 := stitchAt 24 4 frame068scope05_s024 h28
  have h20 := stitchAt 20 4 frame068scope05_s020 h24
  have h16 := stitchAt 16 4 frame068scope05_s016 h20
  have h12 := stitchAt 12 4 frame068scope05_s012 h16
  have h8 := stitchAt 8 4 frame068scope05_s008 h12
  have h4 := stitchAt 4 4 frame068scope05_s004 h8
  have h0 := stitchAt 0 4 frame068scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch05 : batch05.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope05

private abbrev frame068test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch06.stop,F)

private theorem frame068scope06_s000 : ((fits06.drop 0).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s004 : ((fits06.drop 4).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s008 : ((fits06.drop 8).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s012 : ((fits06.drop 12).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s016 : ((fits06.drop 16).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s020 : ((fits06.drop 20).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s024 : ((fits06.drop 24).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s028 : ((fits06.drop 28).take 4).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_s032 : ((fits06.drop 32).take 3).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06_end : (fits06.drop 35).all frame068test06=true := by
  decide +kernel

private theorem frame068scope06 : fits06.all frame068test06=true := by
  have h32 := stitchAt 32 3 frame068scope06_s032 frame068scope06_end
  have h28 := stitchAt 28 4 frame068scope06_s028 h32
  have h24 := stitchAt 24 4 frame068scope06_s024 h28
  have h20 := stitchAt 20 4 frame068scope06_s020 h24
  have h16 := stitchAt 16 4 frame068scope06_s016 h20
  have h12 := stitchAt 12 4 frame068scope06_s012 h16
  have h8 := stitchAt 8 4 frame068scope06_s008 h12
  have h4 := stitchAt 4 4 frame068scope06_s004 h8
  have h0 := stitchAt 0 4 frame068scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch06 : batch06.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope06

private abbrev frame068test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame142 (fun z => List.lookup (guideCode z) guide068)
    (batch07.stop,F)

private theorem frame068scope07_s000 : ((fits07.drop 0).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s004 : ((fits07.drop 4).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s008 : ((fits07.drop 8).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s012 : ((fits07.drop 12).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s016 : ((fits07.drop 16).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s020 : ((fits07.drop 20).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s024 : ((fits07.drop 24).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s028 : ((fits07.drop 28).take 4).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_s032 : ((fits07.drop 32).take 3).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07_end : (fits07.drop 35).all frame068test07=true := by
  decide +kernel

private theorem frame068scope07 : fits07.all frame068test07=true := by
  have h32 := stitchAt 32 3 frame068scope07_s032 frame068scope07_end
  have h28 := stitchAt 28 4 frame068scope07_s028 h32
  have h24 := stitchAt 24 4 frame068scope07_s024 h28
  have h20 := stitchAt 20 4 frame068scope07_s020 h24
  have h16 := stitchAt 16 4 frame068scope07_s016 h20
  have h12 := stitchAt 12 4 frame068scope07_s012 h16
  have h8 := stitchAt 8 4 frame068scope07_s008 h12
  have h4 := stitchAt 4 4 frame068scope07_s004 h8
  have h0 := stitchAt 0 4 frame068scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame068batch07 : batch07.pickTest original frame142=true :=
  FitBatch.pickTest_of_scoped scoped068 frame068scope07

private theorem frameBatches068 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame142)=true := by
  simp only [List.all_cons,List.all_nil,frame068batch00,frame068batch01,frame068batch02,frame068batch03,frame068batch04,frame068batch05,frame068batch06,frame068batch07,Bool.and_self]

theorem frameOK068 : frameRankTest original useStop frame142=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches068

theorem stripOK069 : stripTest frame143=true := by decide +kernel

theorem spanOK069 : checkChain 1800 1796 [frame143.span]=true := by decide +kernel

private theorem guideAt069 : List.lookup frame143.span.1 guideTable=some guide069 := by
  decide +kernel

private theorem scoped069 : original.guide frame143.span.1 =
    (fun z => List.lookup (guideCode z) guide069) := by
  funext z
  change (List.lookup frame143.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide069
  simp only [guideAt069,Option.bind_some]

private abbrev frame069test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch00.stop,F)

private theorem frame069scope00_s000 : ((fits00.drop 0).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s004 : ((fits00.drop 4).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s008 : ((fits00.drop 8).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s012 : ((fits00.drop 12).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s016 : ((fits00.drop 16).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s020 : ((fits00.drop 20).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s024 : ((fits00.drop 24).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s028 : ((fits00.drop 28).take 4).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_s032 : ((fits00.drop 32).take 3).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00_end : (fits00.drop 35).all frame069test00=true := by
  decide +kernel

private theorem frame069scope00 : fits00.all frame069test00=true := by
  have h32 := stitchAt 32 3 frame069scope00_s032 frame069scope00_end
  have h28 := stitchAt 28 4 frame069scope00_s028 h32
  have h24 := stitchAt 24 4 frame069scope00_s024 h28
  have h20 := stitchAt 20 4 frame069scope00_s020 h24
  have h16 := stitchAt 16 4 frame069scope00_s016 h20
  have h12 := stitchAt 12 4 frame069scope00_s012 h16
  have h8 := stitchAt 8 4 frame069scope00_s008 h12
  have h4 := stitchAt 4 4 frame069scope00_s004 h8
  have h0 := stitchAt 0 4 frame069scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch00 : batch00.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope00

private abbrev frame069test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch01.stop,F)

private theorem frame069scope01_s000 : ((fits01.drop 0).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s004 : ((fits01.drop 4).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s008 : ((fits01.drop 8).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s012 : ((fits01.drop 12).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s016 : ((fits01.drop 16).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s020 : ((fits01.drop 20).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s024 : ((fits01.drop 24).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s028 : ((fits01.drop 28).take 4).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_s032 : ((fits01.drop 32).take 3).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01_end : (fits01.drop 35).all frame069test01=true := by
  decide +kernel

private theorem frame069scope01 : fits01.all frame069test01=true := by
  have h32 := stitchAt 32 3 frame069scope01_s032 frame069scope01_end
  have h28 := stitchAt 28 4 frame069scope01_s028 h32
  have h24 := stitchAt 24 4 frame069scope01_s024 h28
  have h20 := stitchAt 20 4 frame069scope01_s020 h24
  have h16 := stitchAt 16 4 frame069scope01_s016 h20
  have h12 := stitchAt 12 4 frame069scope01_s012 h16
  have h8 := stitchAt 8 4 frame069scope01_s008 h12
  have h4 := stitchAt 4 4 frame069scope01_s004 h8
  have h0 := stitchAt 0 4 frame069scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch01 : batch01.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope01

private abbrev frame069test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch02.stop,F)

private theorem frame069scope02_s000 : ((fits02.drop 0).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s004 : ((fits02.drop 4).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s008 : ((fits02.drop 8).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s012 : ((fits02.drop 12).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s016 : ((fits02.drop 16).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s020 : ((fits02.drop 20).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s024 : ((fits02.drop 24).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s028 : ((fits02.drop 28).take 4).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_s032 : ((fits02.drop 32).take 3).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02_end : (fits02.drop 35).all frame069test02=true := by
  decide +kernel

private theorem frame069scope02 : fits02.all frame069test02=true := by
  have h32 := stitchAt 32 3 frame069scope02_s032 frame069scope02_end
  have h28 := stitchAt 28 4 frame069scope02_s028 h32
  have h24 := stitchAt 24 4 frame069scope02_s024 h28
  have h20 := stitchAt 20 4 frame069scope02_s020 h24
  have h16 := stitchAt 16 4 frame069scope02_s016 h20
  have h12 := stitchAt 12 4 frame069scope02_s012 h16
  have h8 := stitchAt 8 4 frame069scope02_s008 h12
  have h4 := stitchAt 4 4 frame069scope02_s004 h8
  have h0 := stitchAt 0 4 frame069scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch02 : batch02.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope02

private abbrev frame069test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch03.stop,F)

private theorem frame069scope03_s000 : ((fits03.drop 0).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s004 : ((fits03.drop 4).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s008 : ((fits03.drop 8).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s012 : ((fits03.drop 12).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s016 : ((fits03.drop 16).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s020 : ((fits03.drop 20).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s024 : ((fits03.drop 24).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s028 : ((fits03.drop 28).take 4).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_s032 : ((fits03.drop 32).take 3).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03_end : (fits03.drop 35).all frame069test03=true := by
  decide +kernel

private theorem frame069scope03 : fits03.all frame069test03=true := by
  have h32 := stitchAt 32 3 frame069scope03_s032 frame069scope03_end
  have h28 := stitchAt 28 4 frame069scope03_s028 h32
  have h24 := stitchAt 24 4 frame069scope03_s024 h28
  have h20 := stitchAt 20 4 frame069scope03_s020 h24
  have h16 := stitchAt 16 4 frame069scope03_s016 h20
  have h12 := stitchAt 12 4 frame069scope03_s012 h16
  have h8 := stitchAt 8 4 frame069scope03_s008 h12
  have h4 := stitchAt 4 4 frame069scope03_s004 h8
  have h0 := stitchAt 0 4 frame069scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch03 : batch03.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope03

private abbrev frame069test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch04.stop,F)

private theorem frame069scope04_s000 : ((fits04.drop 0).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s004 : ((fits04.drop 4).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s008 : ((fits04.drop 8).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s012 : ((fits04.drop 12).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s016 : ((fits04.drop 16).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s020 : ((fits04.drop 20).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s024 : ((fits04.drop 24).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s028 : ((fits04.drop 28).take 4).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_s032 : ((fits04.drop 32).take 3).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04_end : (fits04.drop 35).all frame069test04=true := by
  decide +kernel

private theorem frame069scope04 : fits04.all frame069test04=true := by
  have h32 := stitchAt 32 3 frame069scope04_s032 frame069scope04_end
  have h28 := stitchAt 28 4 frame069scope04_s028 h32
  have h24 := stitchAt 24 4 frame069scope04_s024 h28
  have h20 := stitchAt 20 4 frame069scope04_s020 h24
  have h16 := stitchAt 16 4 frame069scope04_s016 h20
  have h12 := stitchAt 12 4 frame069scope04_s012 h16
  have h8 := stitchAt 8 4 frame069scope04_s008 h12
  have h4 := stitchAt 4 4 frame069scope04_s004 h8
  have h0 := stitchAt 0 4 frame069scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch04 : batch04.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope04

private abbrev frame069test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch05.stop,F)

private theorem frame069scope05_s000 : ((fits05.drop 0).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s004 : ((fits05.drop 4).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s008 : ((fits05.drop 8).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s012 : ((fits05.drop 12).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s016 : ((fits05.drop 16).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s020 : ((fits05.drop 20).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s024 : ((fits05.drop 24).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s028 : ((fits05.drop 28).take 4).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_s032 : ((fits05.drop 32).take 3).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05_end : (fits05.drop 35).all frame069test05=true := by
  decide +kernel

private theorem frame069scope05 : fits05.all frame069test05=true := by
  have h32 := stitchAt 32 3 frame069scope05_s032 frame069scope05_end
  have h28 := stitchAt 28 4 frame069scope05_s028 h32
  have h24 := stitchAt 24 4 frame069scope05_s024 h28
  have h20 := stitchAt 20 4 frame069scope05_s020 h24
  have h16 := stitchAt 16 4 frame069scope05_s016 h20
  have h12 := stitchAt 12 4 frame069scope05_s012 h16
  have h8 := stitchAt 8 4 frame069scope05_s008 h12
  have h4 := stitchAt 4 4 frame069scope05_s004 h8
  have h0 := stitchAt 0 4 frame069scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch05 : batch05.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope05

private abbrev frame069test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch06.stop,F)

private theorem frame069scope06_s000 : ((fits06.drop 0).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s004 : ((fits06.drop 4).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s008 : ((fits06.drop 8).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s012 : ((fits06.drop 12).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s016 : ((fits06.drop 16).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s020 : ((fits06.drop 20).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s024 : ((fits06.drop 24).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s028 : ((fits06.drop 28).take 4).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_s032 : ((fits06.drop 32).take 3).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06_end : (fits06.drop 35).all frame069test06=true := by
  decide +kernel

private theorem frame069scope06 : fits06.all frame069test06=true := by
  have h32 := stitchAt 32 3 frame069scope06_s032 frame069scope06_end
  have h28 := stitchAt 28 4 frame069scope06_s028 h32
  have h24 := stitchAt 24 4 frame069scope06_s024 h28
  have h20 := stitchAt 20 4 frame069scope06_s020 h24
  have h16 := stitchAt 16 4 frame069scope06_s016 h20
  have h12 := stitchAt 12 4 frame069scope06_s012 h16
  have h8 := stitchAt 8 4 frame069scope06_s008 h12
  have h4 := stitchAt 4 4 frame069scope06_s004 h8
  have h0 := stitchAt 0 4 frame069scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch06 : batch06.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope06

private abbrev frame069test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame143 (fun z => List.lookup (guideCode z) guide069)
    (batch07.stop,F)

private theorem frame069scope07_s000 : ((fits07.drop 0).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s004 : ((fits07.drop 4).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s008 : ((fits07.drop 8).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s012 : ((fits07.drop 12).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s016 : ((fits07.drop 16).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s020 : ((fits07.drop 20).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s024 : ((fits07.drop 24).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s028 : ((fits07.drop 28).take 4).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_s032 : ((fits07.drop 32).take 3).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07_end : (fits07.drop 35).all frame069test07=true := by
  decide +kernel

private theorem frame069scope07 : fits07.all frame069test07=true := by
  have h32 := stitchAt 32 3 frame069scope07_s032 frame069scope07_end
  have h28 := stitchAt 28 4 frame069scope07_s028 h32
  have h24 := stitchAt 24 4 frame069scope07_s024 h28
  have h20 := stitchAt 20 4 frame069scope07_s020 h24
  have h16 := stitchAt 16 4 frame069scope07_s016 h20
  have h12 := stitchAt 12 4 frame069scope07_s012 h16
  have h8 := stitchAt 8 4 frame069scope07_s008 h12
  have h4 := stitchAt 4 4 frame069scope07_s004 h8
  have h0 := stitchAt 0 4 frame069scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame069batch07 : batch07.pickTest original frame143=true :=
  FitBatch.pickTest_of_scoped scoped069 frame069scope07

private theorem frameBatches069 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame143)=true := by
  simp only [List.all_cons,List.all_nil,frame069batch00,frame069batch01,frame069batch02,frame069batch03,frame069batch04,frame069batch05,frame069batch06,frame069batch07,Bool.and_self]

theorem frameOK069 : frameRankTest original useStop frame143=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches069


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
