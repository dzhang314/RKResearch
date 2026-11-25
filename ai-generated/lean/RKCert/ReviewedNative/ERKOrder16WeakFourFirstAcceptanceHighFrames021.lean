module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK042 : stripTest frame89=true := by decide +kernel

theorem spanOK042 : checkChain 1746 1744 [frame89.span]=true := by decide +kernel

private theorem guideAt042 : List.lookup frame89.span.1 guideTable=some guide042 := by
  decide +kernel

private theorem scoped042 : original.guide frame89.span.1 =
    (fun z => List.lookup (guideCode z) guide042) := by
  funext z
  change (List.lookup frame89.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide042
  simp only [guideAt042,Option.bind_some]

private abbrev frame042test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch00.stop,F)

private theorem frame042scope00_s000 : ((fits00.drop 0).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s004 : ((fits00.drop 4).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s008 : ((fits00.drop 8).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s012 : ((fits00.drop 12).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s016 : ((fits00.drop 16).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s020 : ((fits00.drop 20).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s024 : ((fits00.drop 24).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s028 : ((fits00.drop 28).take 4).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_s032 : ((fits00.drop 32).take 3).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00_end : (fits00.drop 35).all frame042test00=true := by
  decide +kernel

private theorem frame042scope00 : fits00.all frame042test00=true := by
  have h32 := stitchAt 32 3 frame042scope00_s032 frame042scope00_end
  have h28 := stitchAt 28 4 frame042scope00_s028 h32
  have h24 := stitchAt 24 4 frame042scope00_s024 h28
  have h20 := stitchAt 20 4 frame042scope00_s020 h24
  have h16 := stitchAt 16 4 frame042scope00_s016 h20
  have h12 := stitchAt 12 4 frame042scope00_s012 h16
  have h8 := stitchAt 8 4 frame042scope00_s008 h12
  have h4 := stitchAt 4 4 frame042scope00_s004 h8
  have h0 := stitchAt 0 4 frame042scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch00 : batch00.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope00

private abbrev frame042test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch01.stop,F)

private theorem frame042scope01_s000 : ((fits01.drop 0).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s004 : ((fits01.drop 4).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s008 : ((fits01.drop 8).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s012 : ((fits01.drop 12).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s016 : ((fits01.drop 16).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s020 : ((fits01.drop 20).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s024 : ((fits01.drop 24).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s028 : ((fits01.drop 28).take 4).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_s032 : ((fits01.drop 32).take 3).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01_end : (fits01.drop 35).all frame042test01=true := by
  decide +kernel

private theorem frame042scope01 : fits01.all frame042test01=true := by
  have h32 := stitchAt 32 3 frame042scope01_s032 frame042scope01_end
  have h28 := stitchAt 28 4 frame042scope01_s028 h32
  have h24 := stitchAt 24 4 frame042scope01_s024 h28
  have h20 := stitchAt 20 4 frame042scope01_s020 h24
  have h16 := stitchAt 16 4 frame042scope01_s016 h20
  have h12 := stitchAt 12 4 frame042scope01_s012 h16
  have h8 := stitchAt 8 4 frame042scope01_s008 h12
  have h4 := stitchAt 4 4 frame042scope01_s004 h8
  have h0 := stitchAt 0 4 frame042scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch01 : batch01.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope01

private abbrev frame042test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch02.stop,F)

private theorem frame042scope02_s000 : ((fits02.drop 0).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s004 : ((fits02.drop 4).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s008 : ((fits02.drop 8).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s012 : ((fits02.drop 12).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s016 : ((fits02.drop 16).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s020 : ((fits02.drop 20).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s024 : ((fits02.drop 24).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s028 : ((fits02.drop 28).take 4).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_s032 : ((fits02.drop 32).take 3).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02_end : (fits02.drop 35).all frame042test02=true := by
  decide +kernel

private theorem frame042scope02 : fits02.all frame042test02=true := by
  have h32 := stitchAt 32 3 frame042scope02_s032 frame042scope02_end
  have h28 := stitchAt 28 4 frame042scope02_s028 h32
  have h24 := stitchAt 24 4 frame042scope02_s024 h28
  have h20 := stitchAt 20 4 frame042scope02_s020 h24
  have h16 := stitchAt 16 4 frame042scope02_s016 h20
  have h12 := stitchAt 12 4 frame042scope02_s012 h16
  have h8 := stitchAt 8 4 frame042scope02_s008 h12
  have h4 := stitchAt 4 4 frame042scope02_s004 h8
  have h0 := stitchAt 0 4 frame042scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch02 : batch02.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope02

private abbrev frame042test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch03.stop,F)

private theorem frame042scope03_s000 : ((fits03.drop 0).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s004 : ((fits03.drop 4).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s008 : ((fits03.drop 8).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s012 : ((fits03.drop 12).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s016 : ((fits03.drop 16).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s020 : ((fits03.drop 20).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s024 : ((fits03.drop 24).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s028 : ((fits03.drop 28).take 4).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_s032 : ((fits03.drop 32).take 3).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03_end : (fits03.drop 35).all frame042test03=true := by
  decide +kernel

private theorem frame042scope03 : fits03.all frame042test03=true := by
  have h32 := stitchAt 32 3 frame042scope03_s032 frame042scope03_end
  have h28 := stitchAt 28 4 frame042scope03_s028 h32
  have h24 := stitchAt 24 4 frame042scope03_s024 h28
  have h20 := stitchAt 20 4 frame042scope03_s020 h24
  have h16 := stitchAt 16 4 frame042scope03_s016 h20
  have h12 := stitchAt 12 4 frame042scope03_s012 h16
  have h8 := stitchAt 8 4 frame042scope03_s008 h12
  have h4 := stitchAt 4 4 frame042scope03_s004 h8
  have h0 := stitchAt 0 4 frame042scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch03 : batch03.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope03

private abbrev frame042test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch04.stop,F)

private theorem frame042scope04_s000 : ((fits04.drop 0).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s004 : ((fits04.drop 4).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s008 : ((fits04.drop 8).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s012 : ((fits04.drop 12).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s016 : ((fits04.drop 16).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s020 : ((fits04.drop 20).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s024 : ((fits04.drop 24).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s028 : ((fits04.drop 28).take 4).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_s032 : ((fits04.drop 32).take 3).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04_end : (fits04.drop 35).all frame042test04=true := by
  decide +kernel

private theorem frame042scope04 : fits04.all frame042test04=true := by
  have h32 := stitchAt 32 3 frame042scope04_s032 frame042scope04_end
  have h28 := stitchAt 28 4 frame042scope04_s028 h32
  have h24 := stitchAt 24 4 frame042scope04_s024 h28
  have h20 := stitchAt 20 4 frame042scope04_s020 h24
  have h16 := stitchAt 16 4 frame042scope04_s016 h20
  have h12 := stitchAt 12 4 frame042scope04_s012 h16
  have h8 := stitchAt 8 4 frame042scope04_s008 h12
  have h4 := stitchAt 4 4 frame042scope04_s004 h8
  have h0 := stitchAt 0 4 frame042scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch04 : batch04.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope04

private abbrev frame042test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch05.stop,F)

private theorem frame042scope05_s000 : ((fits05.drop 0).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s004 : ((fits05.drop 4).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s008 : ((fits05.drop 8).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s012 : ((fits05.drop 12).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s016 : ((fits05.drop 16).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s020 : ((fits05.drop 20).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s024 : ((fits05.drop 24).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s028 : ((fits05.drop 28).take 4).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_s032 : ((fits05.drop 32).take 3).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05_end : (fits05.drop 35).all frame042test05=true := by
  decide +kernel

private theorem frame042scope05 : fits05.all frame042test05=true := by
  have h32 := stitchAt 32 3 frame042scope05_s032 frame042scope05_end
  have h28 := stitchAt 28 4 frame042scope05_s028 h32
  have h24 := stitchAt 24 4 frame042scope05_s024 h28
  have h20 := stitchAt 20 4 frame042scope05_s020 h24
  have h16 := stitchAt 16 4 frame042scope05_s016 h20
  have h12 := stitchAt 12 4 frame042scope05_s012 h16
  have h8 := stitchAt 8 4 frame042scope05_s008 h12
  have h4 := stitchAt 4 4 frame042scope05_s004 h8
  have h0 := stitchAt 0 4 frame042scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch05 : batch05.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope05

private abbrev frame042test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch06.stop,F)

private theorem frame042scope06_s000 : ((fits06.drop 0).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s004 : ((fits06.drop 4).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s008 : ((fits06.drop 8).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s012 : ((fits06.drop 12).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s016 : ((fits06.drop 16).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s020 : ((fits06.drop 20).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s024 : ((fits06.drop 24).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s028 : ((fits06.drop 28).take 4).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_s032 : ((fits06.drop 32).take 3).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06_end : (fits06.drop 35).all frame042test06=true := by
  decide +kernel

private theorem frame042scope06 : fits06.all frame042test06=true := by
  have h32 := stitchAt 32 3 frame042scope06_s032 frame042scope06_end
  have h28 := stitchAt 28 4 frame042scope06_s028 h32
  have h24 := stitchAt 24 4 frame042scope06_s024 h28
  have h20 := stitchAt 20 4 frame042scope06_s020 h24
  have h16 := stitchAt 16 4 frame042scope06_s016 h20
  have h12 := stitchAt 12 4 frame042scope06_s012 h16
  have h8 := stitchAt 8 4 frame042scope06_s008 h12
  have h4 := stitchAt 4 4 frame042scope06_s004 h8
  have h0 := stitchAt 0 4 frame042scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch06 : batch06.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope06

private abbrev frame042test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame89 (fun z => List.lookup (guideCode z) guide042)
    (batch07.stop,F)

private theorem frame042scope07_s000 : ((fits07.drop 0).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s004 : ((fits07.drop 4).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s008 : ((fits07.drop 8).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s012 : ((fits07.drop 12).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s016 : ((fits07.drop 16).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s020 : ((fits07.drop 20).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s024 : ((fits07.drop 24).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s028 : ((fits07.drop 28).take 4).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_s032 : ((fits07.drop 32).take 3).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07_end : (fits07.drop 35).all frame042test07=true := by
  decide +kernel

private theorem frame042scope07 : fits07.all frame042test07=true := by
  have h32 := stitchAt 32 3 frame042scope07_s032 frame042scope07_end
  have h28 := stitchAt 28 4 frame042scope07_s028 h32
  have h24 := stitchAt 24 4 frame042scope07_s024 h28
  have h20 := stitchAt 20 4 frame042scope07_s020 h24
  have h16 := stitchAt 16 4 frame042scope07_s016 h20
  have h12 := stitchAt 12 4 frame042scope07_s012 h16
  have h8 := stitchAt 8 4 frame042scope07_s008 h12
  have h4 := stitchAt 4 4 frame042scope07_s004 h8
  have h0 := stitchAt 0 4 frame042scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame042batch07 : batch07.pickTest original frame89=true :=
  FitBatch.pickTest_of_scoped scoped042 frame042scope07

private theorem frameBatches042 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame89)=true := by
  simp only [List.all_cons,List.all_nil,frame042batch00,frame042batch01,frame042batch02,frame042batch03,frame042batch04,frame042batch05,frame042batch06,frame042batch07,Bool.and_self]

theorem frameOK042 : frameRankTest original useStop frame89=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches042

theorem stripOK043 : stripTest frame90=true := by decide +kernel

theorem spanOK043 : checkChain 1748 1746 [frame90.span]=true := by decide +kernel

private theorem guideAt043 : List.lookup frame90.span.1 guideTable=some guide043 := by
  decide +kernel

private theorem scoped043 : original.guide frame90.span.1 =
    (fun z => List.lookup (guideCode z) guide043) := by
  funext z
  change (List.lookup frame90.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide043
  simp only [guideAt043,Option.bind_some]

private abbrev frame043test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch00.stop,F)

private theorem frame043scope00_s000 : ((fits00.drop 0).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s004 : ((fits00.drop 4).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s008 : ((fits00.drop 8).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s012 : ((fits00.drop 12).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s016 : ((fits00.drop 16).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s020 : ((fits00.drop 20).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s024 : ((fits00.drop 24).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s028 : ((fits00.drop 28).take 4).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_s032 : ((fits00.drop 32).take 3).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00_end : (fits00.drop 35).all frame043test00=true := by
  decide +kernel

private theorem frame043scope00 : fits00.all frame043test00=true := by
  have h32 := stitchAt 32 3 frame043scope00_s032 frame043scope00_end
  have h28 := stitchAt 28 4 frame043scope00_s028 h32
  have h24 := stitchAt 24 4 frame043scope00_s024 h28
  have h20 := stitchAt 20 4 frame043scope00_s020 h24
  have h16 := stitchAt 16 4 frame043scope00_s016 h20
  have h12 := stitchAt 12 4 frame043scope00_s012 h16
  have h8 := stitchAt 8 4 frame043scope00_s008 h12
  have h4 := stitchAt 4 4 frame043scope00_s004 h8
  have h0 := stitchAt 0 4 frame043scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch00 : batch00.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope00

private abbrev frame043test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch01.stop,F)

private theorem frame043scope01_s000 : ((fits01.drop 0).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s004 : ((fits01.drop 4).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s008 : ((fits01.drop 8).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s012 : ((fits01.drop 12).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s016 : ((fits01.drop 16).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s020 : ((fits01.drop 20).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s024 : ((fits01.drop 24).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s028 : ((fits01.drop 28).take 4).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_s032 : ((fits01.drop 32).take 3).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01_end : (fits01.drop 35).all frame043test01=true := by
  decide +kernel

private theorem frame043scope01 : fits01.all frame043test01=true := by
  have h32 := stitchAt 32 3 frame043scope01_s032 frame043scope01_end
  have h28 := stitchAt 28 4 frame043scope01_s028 h32
  have h24 := stitchAt 24 4 frame043scope01_s024 h28
  have h20 := stitchAt 20 4 frame043scope01_s020 h24
  have h16 := stitchAt 16 4 frame043scope01_s016 h20
  have h12 := stitchAt 12 4 frame043scope01_s012 h16
  have h8 := stitchAt 8 4 frame043scope01_s008 h12
  have h4 := stitchAt 4 4 frame043scope01_s004 h8
  have h0 := stitchAt 0 4 frame043scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch01 : batch01.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope01

private abbrev frame043test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch02.stop,F)

private theorem frame043scope02_s000 : ((fits02.drop 0).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s004 : ((fits02.drop 4).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s008 : ((fits02.drop 8).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s012 : ((fits02.drop 12).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s016 : ((fits02.drop 16).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s020 : ((fits02.drop 20).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s024 : ((fits02.drop 24).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s028 : ((fits02.drop 28).take 4).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_s032 : ((fits02.drop 32).take 3).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02_end : (fits02.drop 35).all frame043test02=true := by
  decide +kernel

private theorem frame043scope02 : fits02.all frame043test02=true := by
  have h32 := stitchAt 32 3 frame043scope02_s032 frame043scope02_end
  have h28 := stitchAt 28 4 frame043scope02_s028 h32
  have h24 := stitchAt 24 4 frame043scope02_s024 h28
  have h20 := stitchAt 20 4 frame043scope02_s020 h24
  have h16 := stitchAt 16 4 frame043scope02_s016 h20
  have h12 := stitchAt 12 4 frame043scope02_s012 h16
  have h8 := stitchAt 8 4 frame043scope02_s008 h12
  have h4 := stitchAt 4 4 frame043scope02_s004 h8
  have h0 := stitchAt 0 4 frame043scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch02 : batch02.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope02

private abbrev frame043test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch03.stop,F)

private theorem frame043scope03_s000 : ((fits03.drop 0).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s004 : ((fits03.drop 4).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s008 : ((fits03.drop 8).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s012 : ((fits03.drop 12).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s016 : ((fits03.drop 16).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s020 : ((fits03.drop 20).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s024 : ((fits03.drop 24).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s028 : ((fits03.drop 28).take 4).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_s032 : ((fits03.drop 32).take 3).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03_end : (fits03.drop 35).all frame043test03=true := by
  decide +kernel

private theorem frame043scope03 : fits03.all frame043test03=true := by
  have h32 := stitchAt 32 3 frame043scope03_s032 frame043scope03_end
  have h28 := stitchAt 28 4 frame043scope03_s028 h32
  have h24 := stitchAt 24 4 frame043scope03_s024 h28
  have h20 := stitchAt 20 4 frame043scope03_s020 h24
  have h16 := stitchAt 16 4 frame043scope03_s016 h20
  have h12 := stitchAt 12 4 frame043scope03_s012 h16
  have h8 := stitchAt 8 4 frame043scope03_s008 h12
  have h4 := stitchAt 4 4 frame043scope03_s004 h8
  have h0 := stitchAt 0 4 frame043scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch03 : batch03.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope03

private abbrev frame043test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch04.stop,F)

private theorem frame043scope04_s000 : ((fits04.drop 0).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s004 : ((fits04.drop 4).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s008 : ((fits04.drop 8).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s012 : ((fits04.drop 12).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s016 : ((fits04.drop 16).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s020 : ((fits04.drop 20).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s024 : ((fits04.drop 24).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s028 : ((fits04.drop 28).take 4).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_s032 : ((fits04.drop 32).take 3).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04_end : (fits04.drop 35).all frame043test04=true := by
  decide +kernel

private theorem frame043scope04 : fits04.all frame043test04=true := by
  have h32 := stitchAt 32 3 frame043scope04_s032 frame043scope04_end
  have h28 := stitchAt 28 4 frame043scope04_s028 h32
  have h24 := stitchAt 24 4 frame043scope04_s024 h28
  have h20 := stitchAt 20 4 frame043scope04_s020 h24
  have h16 := stitchAt 16 4 frame043scope04_s016 h20
  have h12 := stitchAt 12 4 frame043scope04_s012 h16
  have h8 := stitchAt 8 4 frame043scope04_s008 h12
  have h4 := stitchAt 4 4 frame043scope04_s004 h8
  have h0 := stitchAt 0 4 frame043scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch04 : batch04.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope04

private abbrev frame043test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch05.stop,F)

private theorem frame043scope05_s000 : ((fits05.drop 0).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s004 : ((fits05.drop 4).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s008 : ((fits05.drop 8).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s012 : ((fits05.drop 12).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s016 : ((fits05.drop 16).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s020 : ((fits05.drop 20).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s024 : ((fits05.drop 24).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s028 : ((fits05.drop 28).take 4).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_s032 : ((fits05.drop 32).take 3).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05_end : (fits05.drop 35).all frame043test05=true := by
  decide +kernel

private theorem frame043scope05 : fits05.all frame043test05=true := by
  have h32 := stitchAt 32 3 frame043scope05_s032 frame043scope05_end
  have h28 := stitchAt 28 4 frame043scope05_s028 h32
  have h24 := stitchAt 24 4 frame043scope05_s024 h28
  have h20 := stitchAt 20 4 frame043scope05_s020 h24
  have h16 := stitchAt 16 4 frame043scope05_s016 h20
  have h12 := stitchAt 12 4 frame043scope05_s012 h16
  have h8 := stitchAt 8 4 frame043scope05_s008 h12
  have h4 := stitchAt 4 4 frame043scope05_s004 h8
  have h0 := stitchAt 0 4 frame043scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch05 : batch05.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope05

private abbrev frame043test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch06.stop,F)

private theorem frame043scope06_s000 : ((fits06.drop 0).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s004 : ((fits06.drop 4).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s008 : ((fits06.drop 8).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s012 : ((fits06.drop 12).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s016 : ((fits06.drop 16).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s020 : ((fits06.drop 20).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s024 : ((fits06.drop 24).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s028 : ((fits06.drop 28).take 4).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_s032 : ((fits06.drop 32).take 3).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06_end : (fits06.drop 35).all frame043test06=true := by
  decide +kernel

private theorem frame043scope06 : fits06.all frame043test06=true := by
  have h32 := stitchAt 32 3 frame043scope06_s032 frame043scope06_end
  have h28 := stitchAt 28 4 frame043scope06_s028 h32
  have h24 := stitchAt 24 4 frame043scope06_s024 h28
  have h20 := stitchAt 20 4 frame043scope06_s020 h24
  have h16 := stitchAt 16 4 frame043scope06_s016 h20
  have h12 := stitchAt 12 4 frame043scope06_s012 h16
  have h8 := stitchAt 8 4 frame043scope06_s008 h12
  have h4 := stitchAt 4 4 frame043scope06_s004 h8
  have h0 := stitchAt 0 4 frame043scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch06 : batch06.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope06

private abbrev frame043test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame90 (fun z => List.lookup (guideCode z) guide043)
    (batch07.stop,F)

private theorem frame043scope07_s000 : ((fits07.drop 0).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s004 : ((fits07.drop 4).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s008 : ((fits07.drop 8).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s012 : ((fits07.drop 12).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s016 : ((fits07.drop 16).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s020 : ((fits07.drop 20).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s024 : ((fits07.drop 24).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s028 : ((fits07.drop 28).take 4).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_s032 : ((fits07.drop 32).take 3).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07_end : (fits07.drop 35).all frame043test07=true := by
  decide +kernel

private theorem frame043scope07 : fits07.all frame043test07=true := by
  have h32 := stitchAt 32 3 frame043scope07_s032 frame043scope07_end
  have h28 := stitchAt 28 4 frame043scope07_s028 h32
  have h24 := stitchAt 24 4 frame043scope07_s024 h28
  have h20 := stitchAt 20 4 frame043scope07_s020 h24
  have h16 := stitchAt 16 4 frame043scope07_s016 h20
  have h12 := stitchAt 12 4 frame043scope07_s012 h16
  have h8 := stitchAt 8 4 frame043scope07_s008 h12
  have h4 := stitchAt 4 4 frame043scope07_s004 h8
  have h0 := stitchAt 0 4 frame043scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame043batch07 : batch07.pickTest original frame90=true :=
  FitBatch.pickTest_of_scoped scoped043 frame043scope07

private theorem frameBatches043 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame90)=true := by
  simp only [List.all_cons,List.all_nil,frame043batch00,frame043batch01,frame043batch02,frame043batch03,frame043batch04,frame043batch05,frame043batch06,frame043batch07,Bool.and_self]

theorem frameOK043 : frameRankTest original useStop frame90=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches043


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
