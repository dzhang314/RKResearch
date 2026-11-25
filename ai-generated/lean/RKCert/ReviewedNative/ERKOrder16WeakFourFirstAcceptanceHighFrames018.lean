module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK036 : stripTest frame75=true := by decide +kernel

theorem spanOK036 : checkChain 1724 1720 [frame75.span]=true := by decide +kernel

private theorem guideAt036 : List.lookup frame75.span.1 guideTable=some guide036 := by
  decide +kernel

private theorem scoped036 : original.guide frame75.span.1 =
    (fun z => List.lookup (guideCode z) guide036) := by
  funext z
  change (List.lookup frame75.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide036
  simp only [guideAt036,Option.bind_some]

private abbrev frame036test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch00.stop,F)

private theorem frame036scope00_s000 : ((fits00.drop 0).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s004 : ((fits00.drop 4).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s008 : ((fits00.drop 8).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s012 : ((fits00.drop 12).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s016 : ((fits00.drop 16).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s020 : ((fits00.drop 20).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s024 : ((fits00.drop 24).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s028 : ((fits00.drop 28).take 4).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_s032 : ((fits00.drop 32).take 3).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00_end : (fits00.drop 35).all frame036test00=true := by
  decide +kernel

private theorem frame036scope00 : fits00.all frame036test00=true := by
  have h32 := stitchAt 32 3 frame036scope00_s032 frame036scope00_end
  have h28 := stitchAt 28 4 frame036scope00_s028 h32
  have h24 := stitchAt 24 4 frame036scope00_s024 h28
  have h20 := stitchAt 20 4 frame036scope00_s020 h24
  have h16 := stitchAt 16 4 frame036scope00_s016 h20
  have h12 := stitchAt 12 4 frame036scope00_s012 h16
  have h8 := stitchAt 8 4 frame036scope00_s008 h12
  have h4 := stitchAt 4 4 frame036scope00_s004 h8
  have h0 := stitchAt 0 4 frame036scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch00 : batch00.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope00

private abbrev frame036test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch01.stop,F)

private theorem frame036scope01_s000 : ((fits01.drop 0).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s004 : ((fits01.drop 4).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s008 : ((fits01.drop 8).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s012 : ((fits01.drop 12).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s016 : ((fits01.drop 16).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s020 : ((fits01.drop 20).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s024 : ((fits01.drop 24).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s028 : ((fits01.drop 28).take 4).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_s032 : ((fits01.drop 32).take 3).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01_end : (fits01.drop 35).all frame036test01=true := by
  decide +kernel

private theorem frame036scope01 : fits01.all frame036test01=true := by
  have h32 := stitchAt 32 3 frame036scope01_s032 frame036scope01_end
  have h28 := stitchAt 28 4 frame036scope01_s028 h32
  have h24 := stitchAt 24 4 frame036scope01_s024 h28
  have h20 := stitchAt 20 4 frame036scope01_s020 h24
  have h16 := stitchAt 16 4 frame036scope01_s016 h20
  have h12 := stitchAt 12 4 frame036scope01_s012 h16
  have h8 := stitchAt 8 4 frame036scope01_s008 h12
  have h4 := stitchAt 4 4 frame036scope01_s004 h8
  have h0 := stitchAt 0 4 frame036scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch01 : batch01.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope01

private abbrev frame036test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch02.stop,F)

private theorem frame036scope02_s000 : ((fits02.drop 0).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s004 : ((fits02.drop 4).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s008 : ((fits02.drop 8).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s012 : ((fits02.drop 12).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s016 : ((fits02.drop 16).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s020 : ((fits02.drop 20).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s024 : ((fits02.drop 24).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s028 : ((fits02.drop 28).take 4).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_s032 : ((fits02.drop 32).take 3).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02_end : (fits02.drop 35).all frame036test02=true := by
  decide +kernel

private theorem frame036scope02 : fits02.all frame036test02=true := by
  have h32 := stitchAt 32 3 frame036scope02_s032 frame036scope02_end
  have h28 := stitchAt 28 4 frame036scope02_s028 h32
  have h24 := stitchAt 24 4 frame036scope02_s024 h28
  have h20 := stitchAt 20 4 frame036scope02_s020 h24
  have h16 := stitchAt 16 4 frame036scope02_s016 h20
  have h12 := stitchAt 12 4 frame036scope02_s012 h16
  have h8 := stitchAt 8 4 frame036scope02_s008 h12
  have h4 := stitchAt 4 4 frame036scope02_s004 h8
  have h0 := stitchAt 0 4 frame036scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch02 : batch02.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope02

private abbrev frame036test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch03.stop,F)

private theorem frame036scope03_s000 : ((fits03.drop 0).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s004 : ((fits03.drop 4).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s008 : ((fits03.drop 8).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s012 : ((fits03.drop 12).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s016 : ((fits03.drop 16).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s020 : ((fits03.drop 20).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s024 : ((fits03.drop 24).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s028 : ((fits03.drop 28).take 4).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_s032 : ((fits03.drop 32).take 3).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03_end : (fits03.drop 35).all frame036test03=true := by
  decide +kernel

private theorem frame036scope03 : fits03.all frame036test03=true := by
  have h32 := stitchAt 32 3 frame036scope03_s032 frame036scope03_end
  have h28 := stitchAt 28 4 frame036scope03_s028 h32
  have h24 := stitchAt 24 4 frame036scope03_s024 h28
  have h20 := stitchAt 20 4 frame036scope03_s020 h24
  have h16 := stitchAt 16 4 frame036scope03_s016 h20
  have h12 := stitchAt 12 4 frame036scope03_s012 h16
  have h8 := stitchAt 8 4 frame036scope03_s008 h12
  have h4 := stitchAt 4 4 frame036scope03_s004 h8
  have h0 := stitchAt 0 4 frame036scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch03 : batch03.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope03

private abbrev frame036test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch04.stop,F)

private theorem frame036scope04_s000 : ((fits04.drop 0).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s004 : ((fits04.drop 4).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s008 : ((fits04.drop 8).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s012 : ((fits04.drop 12).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s016 : ((fits04.drop 16).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s020 : ((fits04.drop 20).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s024 : ((fits04.drop 24).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s028 : ((fits04.drop 28).take 4).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_s032 : ((fits04.drop 32).take 3).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04_end : (fits04.drop 35).all frame036test04=true := by
  decide +kernel

private theorem frame036scope04 : fits04.all frame036test04=true := by
  have h32 := stitchAt 32 3 frame036scope04_s032 frame036scope04_end
  have h28 := stitchAt 28 4 frame036scope04_s028 h32
  have h24 := stitchAt 24 4 frame036scope04_s024 h28
  have h20 := stitchAt 20 4 frame036scope04_s020 h24
  have h16 := stitchAt 16 4 frame036scope04_s016 h20
  have h12 := stitchAt 12 4 frame036scope04_s012 h16
  have h8 := stitchAt 8 4 frame036scope04_s008 h12
  have h4 := stitchAt 4 4 frame036scope04_s004 h8
  have h0 := stitchAt 0 4 frame036scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch04 : batch04.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope04

private abbrev frame036test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch05.stop,F)

private theorem frame036scope05_s000 : ((fits05.drop 0).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s004 : ((fits05.drop 4).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s008 : ((fits05.drop 8).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s012 : ((fits05.drop 12).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s016 : ((fits05.drop 16).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s020 : ((fits05.drop 20).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s024 : ((fits05.drop 24).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s028 : ((fits05.drop 28).take 4).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_s032 : ((fits05.drop 32).take 3).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05_end : (fits05.drop 35).all frame036test05=true := by
  decide +kernel

private theorem frame036scope05 : fits05.all frame036test05=true := by
  have h32 := stitchAt 32 3 frame036scope05_s032 frame036scope05_end
  have h28 := stitchAt 28 4 frame036scope05_s028 h32
  have h24 := stitchAt 24 4 frame036scope05_s024 h28
  have h20 := stitchAt 20 4 frame036scope05_s020 h24
  have h16 := stitchAt 16 4 frame036scope05_s016 h20
  have h12 := stitchAt 12 4 frame036scope05_s012 h16
  have h8 := stitchAt 8 4 frame036scope05_s008 h12
  have h4 := stitchAt 4 4 frame036scope05_s004 h8
  have h0 := stitchAt 0 4 frame036scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch05 : batch05.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope05

private abbrev frame036test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch06.stop,F)

private theorem frame036scope06_s000 : ((fits06.drop 0).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s004 : ((fits06.drop 4).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s008 : ((fits06.drop 8).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s012 : ((fits06.drop 12).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s016 : ((fits06.drop 16).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s020 : ((fits06.drop 20).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s024 : ((fits06.drop 24).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s028 : ((fits06.drop 28).take 4).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_s032 : ((fits06.drop 32).take 3).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06_end : (fits06.drop 35).all frame036test06=true := by
  decide +kernel

private theorem frame036scope06 : fits06.all frame036test06=true := by
  have h32 := stitchAt 32 3 frame036scope06_s032 frame036scope06_end
  have h28 := stitchAt 28 4 frame036scope06_s028 h32
  have h24 := stitchAt 24 4 frame036scope06_s024 h28
  have h20 := stitchAt 20 4 frame036scope06_s020 h24
  have h16 := stitchAt 16 4 frame036scope06_s016 h20
  have h12 := stitchAt 12 4 frame036scope06_s012 h16
  have h8 := stitchAt 8 4 frame036scope06_s008 h12
  have h4 := stitchAt 4 4 frame036scope06_s004 h8
  have h0 := stitchAt 0 4 frame036scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch06 : batch06.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope06

private abbrev frame036test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame75 (fun z => List.lookup (guideCode z) guide036)
    (batch07.stop,F)

private theorem frame036scope07_s000 : ((fits07.drop 0).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s004 : ((fits07.drop 4).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s008 : ((fits07.drop 8).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s012 : ((fits07.drop 12).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s016 : ((fits07.drop 16).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s020 : ((fits07.drop 20).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s024 : ((fits07.drop 24).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s028 : ((fits07.drop 28).take 4).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_s032 : ((fits07.drop 32).take 3).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07_end : (fits07.drop 35).all frame036test07=true := by
  decide +kernel

private theorem frame036scope07 : fits07.all frame036test07=true := by
  have h32 := stitchAt 32 3 frame036scope07_s032 frame036scope07_end
  have h28 := stitchAt 28 4 frame036scope07_s028 h32
  have h24 := stitchAt 24 4 frame036scope07_s024 h28
  have h20 := stitchAt 20 4 frame036scope07_s020 h24
  have h16 := stitchAt 16 4 frame036scope07_s016 h20
  have h12 := stitchAt 12 4 frame036scope07_s012 h16
  have h8 := stitchAt 8 4 frame036scope07_s008 h12
  have h4 := stitchAt 4 4 frame036scope07_s004 h8
  have h0 := stitchAt 0 4 frame036scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame036batch07 : batch07.pickTest original frame75=true :=
  FitBatch.pickTest_of_scoped scoped036 frame036scope07

private theorem frameBatches036 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame75)=true := by
  simp only [List.all_cons,List.all_nil,frame036batch00,frame036batch01,frame036batch02,frame036batch03,frame036batch04,frame036batch05,frame036batch06,frame036batch07,Bool.and_self]

theorem frameOK036 : frameRankTest original useStop frame75=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches036

theorem stripOK037 : stripTest frame76=true := by decide +kernel

theorem spanOK037 : checkChain 1728 1724 [frame76.span]=true := by decide +kernel

private theorem guideAt037 : List.lookup frame76.span.1 guideTable=some guide037 := by
  decide +kernel

private theorem scoped037 : original.guide frame76.span.1 =
    (fun z => List.lookup (guideCode z) guide037) := by
  funext z
  change (List.lookup frame76.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide037
  simp only [guideAt037,Option.bind_some]

private abbrev frame037test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch00.stop,F)

private theorem frame037scope00_s000 : ((fits00.drop 0).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s004 : ((fits00.drop 4).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s008 : ((fits00.drop 8).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s012 : ((fits00.drop 12).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s016 : ((fits00.drop 16).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s020 : ((fits00.drop 20).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s024 : ((fits00.drop 24).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s028 : ((fits00.drop 28).take 4).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_s032 : ((fits00.drop 32).take 3).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00_end : (fits00.drop 35).all frame037test00=true := by
  decide +kernel

private theorem frame037scope00 : fits00.all frame037test00=true := by
  have h32 := stitchAt 32 3 frame037scope00_s032 frame037scope00_end
  have h28 := stitchAt 28 4 frame037scope00_s028 h32
  have h24 := stitchAt 24 4 frame037scope00_s024 h28
  have h20 := stitchAt 20 4 frame037scope00_s020 h24
  have h16 := stitchAt 16 4 frame037scope00_s016 h20
  have h12 := stitchAt 12 4 frame037scope00_s012 h16
  have h8 := stitchAt 8 4 frame037scope00_s008 h12
  have h4 := stitchAt 4 4 frame037scope00_s004 h8
  have h0 := stitchAt 0 4 frame037scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch00 : batch00.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope00

private abbrev frame037test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch01.stop,F)

private theorem frame037scope01_s000 : ((fits01.drop 0).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s004 : ((fits01.drop 4).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s008 : ((fits01.drop 8).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s012 : ((fits01.drop 12).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s016 : ((fits01.drop 16).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s020 : ((fits01.drop 20).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s024 : ((fits01.drop 24).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s028 : ((fits01.drop 28).take 4).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_s032 : ((fits01.drop 32).take 3).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01_end : (fits01.drop 35).all frame037test01=true := by
  decide +kernel

private theorem frame037scope01 : fits01.all frame037test01=true := by
  have h32 := stitchAt 32 3 frame037scope01_s032 frame037scope01_end
  have h28 := stitchAt 28 4 frame037scope01_s028 h32
  have h24 := stitchAt 24 4 frame037scope01_s024 h28
  have h20 := stitchAt 20 4 frame037scope01_s020 h24
  have h16 := stitchAt 16 4 frame037scope01_s016 h20
  have h12 := stitchAt 12 4 frame037scope01_s012 h16
  have h8 := stitchAt 8 4 frame037scope01_s008 h12
  have h4 := stitchAt 4 4 frame037scope01_s004 h8
  have h0 := stitchAt 0 4 frame037scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch01 : batch01.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope01

private abbrev frame037test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch02.stop,F)

private theorem frame037scope02_s000 : ((fits02.drop 0).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s004 : ((fits02.drop 4).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s008 : ((fits02.drop 8).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s012 : ((fits02.drop 12).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s016 : ((fits02.drop 16).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s020 : ((fits02.drop 20).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s024 : ((fits02.drop 24).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s028 : ((fits02.drop 28).take 4).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_s032 : ((fits02.drop 32).take 3).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02_end : (fits02.drop 35).all frame037test02=true := by
  decide +kernel

private theorem frame037scope02 : fits02.all frame037test02=true := by
  have h32 := stitchAt 32 3 frame037scope02_s032 frame037scope02_end
  have h28 := stitchAt 28 4 frame037scope02_s028 h32
  have h24 := stitchAt 24 4 frame037scope02_s024 h28
  have h20 := stitchAt 20 4 frame037scope02_s020 h24
  have h16 := stitchAt 16 4 frame037scope02_s016 h20
  have h12 := stitchAt 12 4 frame037scope02_s012 h16
  have h8 := stitchAt 8 4 frame037scope02_s008 h12
  have h4 := stitchAt 4 4 frame037scope02_s004 h8
  have h0 := stitchAt 0 4 frame037scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch02 : batch02.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope02

private abbrev frame037test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch03.stop,F)

private theorem frame037scope03_s000 : ((fits03.drop 0).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s004 : ((fits03.drop 4).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s008 : ((fits03.drop 8).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s012 : ((fits03.drop 12).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s016 : ((fits03.drop 16).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s020 : ((fits03.drop 20).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s024 : ((fits03.drop 24).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s028 : ((fits03.drop 28).take 4).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_s032 : ((fits03.drop 32).take 3).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03_end : (fits03.drop 35).all frame037test03=true := by
  decide +kernel

private theorem frame037scope03 : fits03.all frame037test03=true := by
  have h32 := stitchAt 32 3 frame037scope03_s032 frame037scope03_end
  have h28 := stitchAt 28 4 frame037scope03_s028 h32
  have h24 := stitchAt 24 4 frame037scope03_s024 h28
  have h20 := stitchAt 20 4 frame037scope03_s020 h24
  have h16 := stitchAt 16 4 frame037scope03_s016 h20
  have h12 := stitchAt 12 4 frame037scope03_s012 h16
  have h8 := stitchAt 8 4 frame037scope03_s008 h12
  have h4 := stitchAt 4 4 frame037scope03_s004 h8
  have h0 := stitchAt 0 4 frame037scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch03 : batch03.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope03

private abbrev frame037test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch04.stop,F)

private theorem frame037scope04_s000 : ((fits04.drop 0).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s004 : ((fits04.drop 4).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s008 : ((fits04.drop 8).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s012 : ((fits04.drop 12).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s016 : ((fits04.drop 16).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s020 : ((fits04.drop 20).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s024 : ((fits04.drop 24).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s028 : ((fits04.drop 28).take 4).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_s032 : ((fits04.drop 32).take 3).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04_end : (fits04.drop 35).all frame037test04=true := by
  decide +kernel

private theorem frame037scope04 : fits04.all frame037test04=true := by
  have h32 := stitchAt 32 3 frame037scope04_s032 frame037scope04_end
  have h28 := stitchAt 28 4 frame037scope04_s028 h32
  have h24 := stitchAt 24 4 frame037scope04_s024 h28
  have h20 := stitchAt 20 4 frame037scope04_s020 h24
  have h16 := stitchAt 16 4 frame037scope04_s016 h20
  have h12 := stitchAt 12 4 frame037scope04_s012 h16
  have h8 := stitchAt 8 4 frame037scope04_s008 h12
  have h4 := stitchAt 4 4 frame037scope04_s004 h8
  have h0 := stitchAt 0 4 frame037scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch04 : batch04.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope04

private abbrev frame037test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch05.stop,F)

private theorem frame037scope05_s000 : ((fits05.drop 0).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s004 : ((fits05.drop 4).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s008 : ((fits05.drop 8).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s012 : ((fits05.drop 12).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s016 : ((fits05.drop 16).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s020 : ((fits05.drop 20).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s024 : ((fits05.drop 24).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s028 : ((fits05.drop 28).take 4).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_s032 : ((fits05.drop 32).take 3).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05_end : (fits05.drop 35).all frame037test05=true := by
  decide +kernel

private theorem frame037scope05 : fits05.all frame037test05=true := by
  have h32 := stitchAt 32 3 frame037scope05_s032 frame037scope05_end
  have h28 := stitchAt 28 4 frame037scope05_s028 h32
  have h24 := stitchAt 24 4 frame037scope05_s024 h28
  have h20 := stitchAt 20 4 frame037scope05_s020 h24
  have h16 := stitchAt 16 4 frame037scope05_s016 h20
  have h12 := stitchAt 12 4 frame037scope05_s012 h16
  have h8 := stitchAt 8 4 frame037scope05_s008 h12
  have h4 := stitchAt 4 4 frame037scope05_s004 h8
  have h0 := stitchAt 0 4 frame037scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch05 : batch05.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope05

private abbrev frame037test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch06.stop,F)

private theorem frame037scope06_s000 : ((fits06.drop 0).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s004 : ((fits06.drop 4).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s008 : ((fits06.drop 8).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s012 : ((fits06.drop 12).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s016 : ((fits06.drop 16).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s020 : ((fits06.drop 20).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s024 : ((fits06.drop 24).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s028 : ((fits06.drop 28).take 4).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_s032 : ((fits06.drop 32).take 3).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06_end : (fits06.drop 35).all frame037test06=true := by
  decide +kernel

private theorem frame037scope06 : fits06.all frame037test06=true := by
  have h32 := stitchAt 32 3 frame037scope06_s032 frame037scope06_end
  have h28 := stitchAt 28 4 frame037scope06_s028 h32
  have h24 := stitchAt 24 4 frame037scope06_s024 h28
  have h20 := stitchAt 20 4 frame037scope06_s020 h24
  have h16 := stitchAt 16 4 frame037scope06_s016 h20
  have h12 := stitchAt 12 4 frame037scope06_s012 h16
  have h8 := stitchAt 8 4 frame037scope06_s008 h12
  have h4 := stitchAt 4 4 frame037scope06_s004 h8
  have h0 := stitchAt 0 4 frame037scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch06 : batch06.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope06

private abbrev frame037test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame76 (fun z => List.lookup (guideCode z) guide037)
    (batch07.stop,F)

private theorem frame037scope07_s000 : ((fits07.drop 0).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s004 : ((fits07.drop 4).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s008 : ((fits07.drop 8).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s012 : ((fits07.drop 12).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s016 : ((fits07.drop 16).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s020 : ((fits07.drop 20).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s024 : ((fits07.drop 24).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s028 : ((fits07.drop 28).take 4).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_s032 : ((fits07.drop 32).take 3).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07_end : (fits07.drop 35).all frame037test07=true := by
  decide +kernel

private theorem frame037scope07 : fits07.all frame037test07=true := by
  have h32 := stitchAt 32 3 frame037scope07_s032 frame037scope07_end
  have h28 := stitchAt 28 4 frame037scope07_s028 h32
  have h24 := stitchAt 24 4 frame037scope07_s024 h28
  have h20 := stitchAt 20 4 frame037scope07_s020 h24
  have h16 := stitchAt 16 4 frame037scope07_s016 h20
  have h12 := stitchAt 12 4 frame037scope07_s012 h16
  have h8 := stitchAt 8 4 frame037scope07_s008 h12
  have h4 := stitchAt 4 4 frame037scope07_s004 h8
  have h0 := stitchAt 0 4 frame037scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame037batch07 : batch07.pickTest original frame76=true :=
  FitBatch.pickTest_of_scoped scoped037 frame037scope07

private theorem frameBatches037 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame76)=true := by
  simp only [List.all_cons,List.all_nil,frame037batch00,frame037batch01,frame037batch02,frame037batch03,frame037batch04,frame037batch05,frame037batch06,frame037batch07,Bool.and_self]

theorem frameOK037 : frameRankTest original useStop frame76=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches037


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
