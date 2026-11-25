module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK088 : stripTest frame178=true := by decide +kernel

theorem spanOK088 : checkChain 2000 1984 [frame178.span]=true := by decide +kernel

private theorem guideAt088 : List.lookup frame178.span.1 guideTable=some guide088 := by
  decide +kernel

private theorem scoped088 : original.guide frame178.span.1 =
    (fun z => List.lookup (guideCode z) guide088) := by
  funext z
  change (List.lookup frame178.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide088
  simp only [guideAt088,Option.bind_some]

private abbrev frame088test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch00.stop,F)

private theorem frame088scope00_s000 : ((fits00.drop 0).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s004 : ((fits00.drop 4).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s008 : ((fits00.drop 8).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s012 : ((fits00.drop 12).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s016 : ((fits00.drop 16).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s020 : ((fits00.drop 20).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s024 : ((fits00.drop 24).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s028 : ((fits00.drop 28).take 4).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_s032 : ((fits00.drop 32).take 3).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00_end : (fits00.drop 35).all frame088test00=true := by
  decide +kernel

private theorem frame088scope00 : fits00.all frame088test00=true := by
  have h32 := stitchAt 32 3 frame088scope00_s032 frame088scope00_end
  have h28 := stitchAt 28 4 frame088scope00_s028 h32
  have h24 := stitchAt 24 4 frame088scope00_s024 h28
  have h20 := stitchAt 20 4 frame088scope00_s020 h24
  have h16 := stitchAt 16 4 frame088scope00_s016 h20
  have h12 := stitchAt 12 4 frame088scope00_s012 h16
  have h8 := stitchAt 8 4 frame088scope00_s008 h12
  have h4 := stitchAt 4 4 frame088scope00_s004 h8
  have h0 := stitchAt 0 4 frame088scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch00 : batch00.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope00

private abbrev frame088test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch01.stop,F)

private theorem frame088scope01_s000 : ((fits01.drop 0).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s004 : ((fits01.drop 4).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s008 : ((fits01.drop 8).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s012 : ((fits01.drop 12).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s016 : ((fits01.drop 16).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s020 : ((fits01.drop 20).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s024 : ((fits01.drop 24).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s028 : ((fits01.drop 28).take 4).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_s032 : ((fits01.drop 32).take 3).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01_end : (fits01.drop 35).all frame088test01=true := by
  decide +kernel

private theorem frame088scope01 : fits01.all frame088test01=true := by
  have h32 := stitchAt 32 3 frame088scope01_s032 frame088scope01_end
  have h28 := stitchAt 28 4 frame088scope01_s028 h32
  have h24 := stitchAt 24 4 frame088scope01_s024 h28
  have h20 := stitchAt 20 4 frame088scope01_s020 h24
  have h16 := stitchAt 16 4 frame088scope01_s016 h20
  have h12 := stitchAt 12 4 frame088scope01_s012 h16
  have h8 := stitchAt 8 4 frame088scope01_s008 h12
  have h4 := stitchAt 4 4 frame088scope01_s004 h8
  have h0 := stitchAt 0 4 frame088scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch01 : batch01.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope01

private abbrev frame088test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch02.stop,F)

private theorem frame088scope02_s000 : ((fits02.drop 0).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s004 : ((fits02.drop 4).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s008 : ((fits02.drop 8).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s012 : ((fits02.drop 12).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s016 : ((fits02.drop 16).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s020 : ((fits02.drop 20).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s024 : ((fits02.drop 24).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s028 : ((fits02.drop 28).take 4).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_s032 : ((fits02.drop 32).take 3).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02_end : (fits02.drop 35).all frame088test02=true := by
  decide +kernel

private theorem frame088scope02 : fits02.all frame088test02=true := by
  have h32 := stitchAt 32 3 frame088scope02_s032 frame088scope02_end
  have h28 := stitchAt 28 4 frame088scope02_s028 h32
  have h24 := stitchAt 24 4 frame088scope02_s024 h28
  have h20 := stitchAt 20 4 frame088scope02_s020 h24
  have h16 := stitchAt 16 4 frame088scope02_s016 h20
  have h12 := stitchAt 12 4 frame088scope02_s012 h16
  have h8 := stitchAt 8 4 frame088scope02_s008 h12
  have h4 := stitchAt 4 4 frame088scope02_s004 h8
  have h0 := stitchAt 0 4 frame088scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch02 : batch02.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope02

private abbrev frame088test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch03.stop,F)

private theorem frame088scope03_s000 : ((fits03.drop 0).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s004 : ((fits03.drop 4).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s008 : ((fits03.drop 8).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s012 : ((fits03.drop 12).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s016 : ((fits03.drop 16).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s020 : ((fits03.drop 20).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s024 : ((fits03.drop 24).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s028 : ((fits03.drop 28).take 4).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_s032 : ((fits03.drop 32).take 3).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03_end : (fits03.drop 35).all frame088test03=true := by
  decide +kernel

private theorem frame088scope03 : fits03.all frame088test03=true := by
  have h32 := stitchAt 32 3 frame088scope03_s032 frame088scope03_end
  have h28 := stitchAt 28 4 frame088scope03_s028 h32
  have h24 := stitchAt 24 4 frame088scope03_s024 h28
  have h20 := stitchAt 20 4 frame088scope03_s020 h24
  have h16 := stitchAt 16 4 frame088scope03_s016 h20
  have h12 := stitchAt 12 4 frame088scope03_s012 h16
  have h8 := stitchAt 8 4 frame088scope03_s008 h12
  have h4 := stitchAt 4 4 frame088scope03_s004 h8
  have h0 := stitchAt 0 4 frame088scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch03 : batch03.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope03

private abbrev frame088test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch04.stop,F)

private theorem frame088scope04_s000 : ((fits04.drop 0).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s004 : ((fits04.drop 4).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s008 : ((fits04.drop 8).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s012 : ((fits04.drop 12).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s016 : ((fits04.drop 16).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s020 : ((fits04.drop 20).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s024 : ((fits04.drop 24).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s028 : ((fits04.drop 28).take 4).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_s032 : ((fits04.drop 32).take 3).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04_end : (fits04.drop 35).all frame088test04=true := by
  decide +kernel

private theorem frame088scope04 : fits04.all frame088test04=true := by
  have h32 := stitchAt 32 3 frame088scope04_s032 frame088scope04_end
  have h28 := stitchAt 28 4 frame088scope04_s028 h32
  have h24 := stitchAt 24 4 frame088scope04_s024 h28
  have h20 := stitchAt 20 4 frame088scope04_s020 h24
  have h16 := stitchAt 16 4 frame088scope04_s016 h20
  have h12 := stitchAt 12 4 frame088scope04_s012 h16
  have h8 := stitchAt 8 4 frame088scope04_s008 h12
  have h4 := stitchAt 4 4 frame088scope04_s004 h8
  have h0 := stitchAt 0 4 frame088scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch04 : batch04.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope04

private abbrev frame088test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch05.stop,F)

private theorem frame088scope05_s000 : ((fits05.drop 0).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s004 : ((fits05.drop 4).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s008 : ((fits05.drop 8).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s012 : ((fits05.drop 12).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s016 : ((fits05.drop 16).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s020 : ((fits05.drop 20).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s024 : ((fits05.drop 24).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s028 : ((fits05.drop 28).take 4).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_s032 : ((fits05.drop 32).take 3).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05_end : (fits05.drop 35).all frame088test05=true := by
  decide +kernel

private theorem frame088scope05 : fits05.all frame088test05=true := by
  have h32 := stitchAt 32 3 frame088scope05_s032 frame088scope05_end
  have h28 := stitchAt 28 4 frame088scope05_s028 h32
  have h24 := stitchAt 24 4 frame088scope05_s024 h28
  have h20 := stitchAt 20 4 frame088scope05_s020 h24
  have h16 := stitchAt 16 4 frame088scope05_s016 h20
  have h12 := stitchAt 12 4 frame088scope05_s012 h16
  have h8 := stitchAt 8 4 frame088scope05_s008 h12
  have h4 := stitchAt 4 4 frame088scope05_s004 h8
  have h0 := stitchAt 0 4 frame088scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch05 : batch05.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope05

private abbrev frame088test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch06.stop,F)

private theorem frame088scope06_s000 : ((fits06.drop 0).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s004 : ((fits06.drop 4).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s008 : ((fits06.drop 8).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s012 : ((fits06.drop 12).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s016 : ((fits06.drop 16).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s020 : ((fits06.drop 20).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s024 : ((fits06.drop 24).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s028 : ((fits06.drop 28).take 4).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_s032 : ((fits06.drop 32).take 3).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06_end : (fits06.drop 35).all frame088test06=true := by
  decide +kernel

private theorem frame088scope06 : fits06.all frame088test06=true := by
  have h32 := stitchAt 32 3 frame088scope06_s032 frame088scope06_end
  have h28 := stitchAt 28 4 frame088scope06_s028 h32
  have h24 := stitchAt 24 4 frame088scope06_s024 h28
  have h20 := stitchAt 20 4 frame088scope06_s020 h24
  have h16 := stitchAt 16 4 frame088scope06_s016 h20
  have h12 := stitchAt 12 4 frame088scope06_s012 h16
  have h8 := stitchAt 8 4 frame088scope06_s008 h12
  have h4 := stitchAt 4 4 frame088scope06_s004 h8
  have h0 := stitchAt 0 4 frame088scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch06 : batch06.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope06

private abbrev frame088test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame178 (fun z => List.lookup (guideCode z) guide088)
    (batch07.stop,F)

private theorem frame088scope07_s000 : ((fits07.drop 0).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s004 : ((fits07.drop 4).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s008 : ((fits07.drop 8).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s012 : ((fits07.drop 12).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s016 : ((fits07.drop 16).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s020 : ((fits07.drop 20).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s024 : ((fits07.drop 24).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s028 : ((fits07.drop 28).take 4).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_s032 : ((fits07.drop 32).take 3).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07_end : (fits07.drop 35).all frame088test07=true := by
  decide +kernel

private theorem frame088scope07 : fits07.all frame088test07=true := by
  have h32 := stitchAt 32 3 frame088scope07_s032 frame088scope07_end
  have h28 := stitchAt 28 4 frame088scope07_s028 h32
  have h24 := stitchAt 24 4 frame088scope07_s024 h28
  have h20 := stitchAt 20 4 frame088scope07_s020 h24
  have h16 := stitchAt 16 4 frame088scope07_s016 h20
  have h12 := stitchAt 12 4 frame088scope07_s012 h16
  have h8 := stitchAt 8 4 frame088scope07_s008 h12
  have h4 := stitchAt 4 4 frame088scope07_s004 h8
  have h0 := stitchAt 0 4 frame088scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame088batch07 : batch07.pickTest original frame178=true :=
  FitBatch.pickTest_of_scoped scoped088 frame088scope07

private theorem frameBatches088 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame178)=true := by
  simp only [List.all_cons,List.all_nil,frame088batch00,frame088batch01,frame088batch02,frame088batch03,frame088batch04,frame088batch05,frame088batch06,frame088batch07,Bool.and_self]

theorem frameOK088 : frameRankTest original useStop frame178=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches088

theorem stripOK089 : stripTest frame179=true := by decide +kernel

theorem spanOK089 : checkChain 2016 2000 [frame179.span]=true := by decide +kernel

private theorem guideAt089 : List.lookup frame179.span.1 guideTable=some guide089 := by
  decide +kernel

private theorem scoped089 : original.guide frame179.span.1 =
    (fun z => List.lookup (guideCode z) guide089) := by
  funext z
  change (List.lookup frame179.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide089
  simp only [guideAt089,Option.bind_some]

private abbrev frame089test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch00.stop,F)

private theorem frame089scope00_s000 : ((fits00.drop 0).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s004 : ((fits00.drop 4).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s008 : ((fits00.drop 8).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s012 : ((fits00.drop 12).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s016 : ((fits00.drop 16).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s020 : ((fits00.drop 20).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s024 : ((fits00.drop 24).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s028 : ((fits00.drop 28).take 4).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_s032 : ((fits00.drop 32).take 3).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00_end : (fits00.drop 35).all frame089test00=true := by
  decide +kernel

private theorem frame089scope00 : fits00.all frame089test00=true := by
  have h32 := stitchAt 32 3 frame089scope00_s032 frame089scope00_end
  have h28 := stitchAt 28 4 frame089scope00_s028 h32
  have h24 := stitchAt 24 4 frame089scope00_s024 h28
  have h20 := stitchAt 20 4 frame089scope00_s020 h24
  have h16 := stitchAt 16 4 frame089scope00_s016 h20
  have h12 := stitchAt 12 4 frame089scope00_s012 h16
  have h8 := stitchAt 8 4 frame089scope00_s008 h12
  have h4 := stitchAt 4 4 frame089scope00_s004 h8
  have h0 := stitchAt 0 4 frame089scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch00 : batch00.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope00

private abbrev frame089test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch01.stop,F)

private theorem frame089scope01_s000 : ((fits01.drop 0).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s004 : ((fits01.drop 4).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s008 : ((fits01.drop 8).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s012 : ((fits01.drop 12).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s016 : ((fits01.drop 16).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s020 : ((fits01.drop 20).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s024 : ((fits01.drop 24).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s028 : ((fits01.drop 28).take 4).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_s032 : ((fits01.drop 32).take 3).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01_end : (fits01.drop 35).all frame089test01=true := by
  decide +kernel

private theorem frame089scope01 : fits01.all frame089test01=true := by
  have h32 := stitchAt 32 3 frame089scope01_s032 frame089scope01_end
  have h28 := stitchAt 28 4 frame089scope01_s028 h32
  have h24 := stitchAt 24 4 frame089scope01_s024 h28
  have h20 := stitchAt 20 4 frame089scope01_s020 h24
  have h16 := stitchAt 16 4 frame089scope01_s016 h20
  have h12 := stitchAt 12 4 frame089scope01_s012 h16
  have h8 := stitchAt 8 4 frame089scope01_s008 h12
  have h4 := stitchAt 4 4 frame089scope01_s004 h8
  have h0 := stitchAt 0 4 frame089scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch01 : batch01.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope01

private abbrev frame089test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch02.stop,F)

private theorem frame089scope02_s000 : ((fits02.drop 0).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s004 : ((fits02.drop 4).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s008 : ((fits02.drop 8).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s012 : ((fits02.drop 12).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s016 : ((fits02.drop 16).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s020 : ((fits02.drop 20).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s024 : ((fits02.drop 24).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s028 : ((fits02.drop 28).take 4).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_s032 : ((fits02.drop 32).take 3).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02_end : (fits02.drop 35).all frame089test02=true := by
  decide +kernel

private theorem frame089scope02 : fits02.all frame089test02=true := by
  have h32 := stitchAt 32 3 frame089scope02_s032 frame089scope02_end
  have h28 := stitchAt 28 4 frame089scope02_s028 h32
  have h24 := stitchAt 24 4 frame089scope02_s024 h28
  have h20 := stitchAt 20 4 frame089scope02_s020 h24
  have h16 := stitchAt 16 4 frame089scope02_s016 h20
  have h12 := stitchAt 12 4 frame089scope02_s012 h16
  have h8 := stitchAt 8 4 frame089scope02_s008 h12
  have h4 := stitchAt 4 4 frame089scope02_s004 h8
  have h0 := stitchAt 0 4 frame089scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch02 : batch02.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope02

private abbrev frame089test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch03.stop,F)

private theorem frame089scope03_s000 : ((fits03.drop 0).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s004 : ((fits03.drop 4).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s008 : ((fits03.drop 8).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s012 : ((fits03.drop 12).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s016 : ((fits03.drop 16).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s020 : ((fits03.drop 20).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s024 : ((fits03.drop 24).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s028 : ((fits03.drop 28).take 4).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_s032 : ((fits03.drop 32).take 3).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03_end : (fits03.drop 35).all frame089test03=true := by
  decide +kernel

private theorem frame089scope03 : fits03.all frame089test03=true := by
  have h32 := stitchAt 32 3 frame089scope03_s032 frame089scope03_end
  have h28 := stitchAt 28 4 frame089scope03_s028 h32
  have h24 := stitchAt 24 4 frame089scope03_s024 h28
  have h20 := stitchAt 20 4 frame089scope03_s020 h24
  have h16 := stitchAt 16 4 frame089scope03_s016 h20
  have h12 := stitchAt 12 4 frame089scope03_s012 h16
  have h8 := stitchAt 8 4 frame089scope03_s008 h12
  have h4 := stitchAt 4 4 frame089scope03_s004 h8
  have h0 := stitchAt 0 4 frame089scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch03 : batch03.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope03

private abbrev frame089test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch04.stop,F)

private theorem frame089scope04_s000 : ((fits04.drop 0).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s004 : ((fits04.drop 4).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s008 : ((fits04.drop 8).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s012 : ((fits04.drop 12).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s016 : ((fits04.drop 16).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s020 : ((fits04.drop 20).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s024 : ((fits04.drop 24).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s028 : ((fits04.drop 28).take 4).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_s032 : ((fits04.drop 32).take 3).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04_end : (fits04.drop 35).all frame089test04=true := by
  decide +kernel

private theorem frame089scope04 : fits04.all frame089test04=true := by
  have h32 := stitchAt 32 3 frame089scope04_s032 frame089scope04_end
  have h28 := stitchAt 28 4 frame089scope04_s028 h32
  have h24 := stitchAt 24 4 frame089scope04_s024 h28
  have h20 := stitchAt 20 4 frame089scope04_s020 h24
  have h16 := stitchAt 16 4 frame089scope04_s016 h20
  have h12 := stitchAt 12 4 frame089scope04_s012 h16
  have h8 := stitchAt 8 4 frame089scope04_s008 h12
  have h4 := stitchAt 4 4 frame089scope04_s004 h8
  have h0 := stitchAt 0 4 frame089scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch04 : batch04.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope04

private abbrev frame089test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch05.stop,F)

private theorem frame089scope05_s000 : ((fits05.drop 0).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s004 : ((fits05.drop 4).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s008 : ((fits05.drop 8).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s012 : ((fits05.drop 12).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s016 : ((fits05.drop 16).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s020 : ((fits05.drop 20).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s024 : ((fits05.drop 24).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s028 : ((fits05.drop 28).take 4).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_s032 : ((fits05.drop 32).take 3).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05_end : (fits05.drop 35).all frame089test05=true := by
  decide +kernel

private theorem frame089scope05 : fits05.all frame089test05=true := by
  have h32 := stitchAt 32 3 frame089scope05_s032 frame089scope05_end
  have h28 := stitchAt 28 4 frame089scope05_s028 h32
  have h24 := stitchAt 24 4 frame089scope05_s024 h28
  have h20 := stitchAt 20 4 frame089scope05_s020 h24
  have h16 := stitchAt 16 4 frame089scope05_s016 h20
  have h12 := stitchAt 12 4 frame089scope05_s012 h16
  have h8 := stitchAt 8 4 frame089scope05_s008 h12
  have h4 := stitchAt 4 4 frame089scope05_s004 h8
  have h0 := stitchAt 0 4 frame089scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch05 : batch05.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope05

private abbrev frame089test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch06.stop,F)

private theorem frame089scope06_s000 : ((fits06.drop 0).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s004 : ((fits06.drop 4).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s008 : ((fits06.drop 8).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s012 : ((fits06.drop 12).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s016 : ((fits06.drop 16).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s020 : ((fits06.drop 20).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s024 : ((fits06.drop 24).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s028 : ((fits06.drop 28).take 4).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_s032 : ((fits06.drop 32).take 3).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06_end : (fits06.drop 35).all frame089test06=true := by
  decide +kernel

private theorem frame089scope06 : fits06.all frame089test06=true := by
  have h32 := stitchAt 32 3 frame089scope06_s032 frame089scope06_end
  have h28 := stitchAt 28 4 frame089scope06_s028 h32
  have h24 := stitchAt 24 4 frame089scope06_s024 h28
  have h20 := stitchAt 20 4 frame089scope06_s020 h24
  have h16 := stitchAt 16 4 frame089scope06_s016 h20
  have h12 := stitchAt 12 4 frame089scope06_s012 h16
  have h8 := stitchAt 8 4 frame089scope06_s008 h12
  have h4 := stitchAt 4 4 frame089scope06_s004 h8
  have h0 := stitchAt 0 4 frame089scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch06 : batch06.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope06

private abbrev frame089test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame179 (fun z => List.lookup (guideCode z) guide089)
    (batch07.stop,F)

private theorem frame089scope07_s000 : ((fits07.drop 0).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s004 : ((fits07.drop 4).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s008 : ((fits07.drop 8).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s012 : ((fits07.drop 12).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s016 : ((fits07.drop 16).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s020 : ((fits07.drop 20).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s024 : ((fits07.drop 24).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s028 : ((fits07.drop 28).take 4).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_s032 : ((fits07.drop 32).take 3).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07_end : (fits07.drop 35).all frame089test07=true := by
  decide +kernel

private theorem frame089scope07 : fits07.all frame089test07=true := by
  have h32 := stitchAt 32 3 frame089scope07_s032 frame089scope07_end
  have h28 := stitchAt 28 4 frame089scope07_s028 h32
  have h24 := stitchAt 24 4 frame089scope07_s024 h28
  have h20 := stitchAt 20 4 frame089scope07_s020 h24
  have h16 := stitchAt 16 4 frame089scope07_s016 h20
  have h12 := stitchAt 12 4 frame089scope07_s012 h16
  have h8 := stitchAt 8 4 frame089scope07_s008 h12
  have h4 := stitchAt 4 4 frame089scope07_s004 h8
  have h0 := stitchAt 0 4 frame089scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame089batch07 : batch07.pickTest original frame179=true :=
  FitBatch.pickTest_of_scoped scoped089 frame089scope07

private theorem frameBatches089 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame179)=true := by
  simp only [List.all_cons,List.all_nil,frame089batch00,frame089batch01,frame089batch02,frame089batch03,frame089batch04,frame089batch05,frame089batch06,frame089batch07,Bool.and_self]

theorem frameOK089 : frameRankTest original useStop frame179=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches089


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
