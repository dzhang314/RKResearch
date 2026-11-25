module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK018 : stripTest frame37=true := by decide +kernel

theorem spanOK018 : checkChain 1536 1528 [frame37.span]=true := by decide +kernel

private theorem guideAt018 : List.lookup frame37.span.1 guideTable=some guide018 := by
  decide +kernel

private theorem scoped018 : original.guide frame37.span.1 =
    (fun z => List.lookup (guideCode z) guide018) := by
  funext z
  change (List.lookup frame37.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide018
  simp only [guideAt018,Option.bind_some]

private abbrev frame018test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch00.stop,F)

private theorem frame018scope00_s000 : ((fits00.drop 0).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s004 : ((fits00.drop 4).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s008 : ((fits00.drop 8).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s012 : ((fits00.drop 12).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s016 : ((fits00.drop 16).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s020 : ((fits00.drop 20).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s024 : ((fits00.drop 24).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s028 : ((fits00.drop 28).take 4).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_s032 : ((fits00.drop 32).take 3).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00_end : (fits00.drop 35).all frame018test00=true := by
  decide +kernel

private theorem frame018scope00 : fits00.all frame018test00=true := by
  have h32 := stitchAt 32 3 frame018scope00_s032 frame018scope00_end
  have h28 := stitchAt 28 4 frame018scope00_s028 h32
  have h24 := stitchAt 24 4 frame018scope00_s024 h28
  have h20 := stitchAt 20 4 frame018scope00_s020 h24
  have h16 := stitchAt 16 4 frame018scope00_s016 h20
  have h12 := stitchAt 12 4 frame018scope00_s012 h16
  have h8 := stitchAt 8 4 frame018scope00_s008 h12
  have h4 := stitchAt 4 4 frame018scope00_s004 h8
  have h0 := stitchAt 0 4 frame018scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch00 : batch00.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope00

private abbrev frame018test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch01.stop,F)

private theorem frame018scope01_s000 : ((fits01.drop 0).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s004 : ((fits01.drop 4).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s008 : ((fits01.drop 8).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s012 : ((fits01.drop 12).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s016 : ((fits01.drop 16).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s020 : ((fits01.drop 20).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s024 : ((fits01.drop 24).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s028 : ((fits01.drop 28).take 4).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_s032 : ((fits01.drop 32).take 3).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01_end : (fits01.drop 35).all frame018test01=true := by
  decide +kernel

private theorem frame018scope01 : fits01.all frame018test01=true := by
  have h32 := stitchAt 32 3 frame018scope01_s032 frame018scope01_end
  have h28 := stitchAt 28 4 frame018scope01_s028 h32
  have h24 := stitchAt 24 4 frame018scope01_s024 h28
  have h20 := stitchAt 20 4 frame018scope01_s020 h24
  have h16 := stitchAt 16 4 frame018scope01_s016 h20
  have h12 := stitchAt 12 4 frame018scope01_s012 h16
  have h8 := stitchAt 8 4 frame018scope01_s008 h12
  have h4 := stitchAt 4 4 frame018scope01_s004 h8
  have h0 := stitchAt 0 4 frame018scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch01 : batch01.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope01

private abbrev frame018test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch02.stop,F)

private theorem frame018scope02_s000 : ((fits02.drop 0).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s004 : ((fits02.drop 4).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s008 : ((fits02.drop 8).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s012 : ((fits02.drop 12).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s016 : ((fits02.drop 16).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s020 : ((fits02.drop 20).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s024 : ((fits02.drop 24).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s028 : ((fits02.drop 28).take 4).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_s032 : ((fits02.drop 32).take 3).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02_end : (fits02.drop 35).all frame018test02=true := by
  decide +kernel

private theorem frame018scope02 : fits02.all frame018test02=true := by
  have h32 := stitchAt 32 3 frame018scope02_s032 frame018scope02_end
  have h28 := stitchAt 28 4 frame018scope02_s028 h32
  have h24 := stitchAt 24 4 frame018scope02_s024 h28
  have h20 := stitchAt 20 4 frame018scope02_s020 h24
  have h16 := stitchAt 16 4 frame018scope02_s016 h20
  have h12 := stitchAt 12 4 frame018scope02_s012 h16
  have h8 := stitchAt 8 4 frame018scope02_s008 h12
  have h4 := stitchAt 4 4 frame018scope02_s004 h8
  have h0 := stitchAt 0 4 frame018scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch02 : batch02.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope02

private abbrev frame018test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch03.stop,F)

private theorem frame018scope03_s000 : ((fits03.drop 0).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s004 : ((fits03.drop 4).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s008 : ((fits03.drop 8).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s012 : ((fits03.drop 12).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s016 : ((fits03.drop 16).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s020 : ((fits03.drop 20).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s024 : ((fits03.drop 24).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s028 : ((fits03.drop 28).take 4).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_s032 : ((fits03.drop 32).take 3).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03_end : (fits03.drop 35).all frame018test03=true := by
  decide +kernel

private theorem frame018scope03 : fits03.all frame018test03=true := by
  have h32 := stitchAt 32 3 frame018scope03_s032 frame018scope03_end
  have h28 := stitchAt 28 4 frame018scope03_s028 h32
  have h24 := stitchAt 24 4 frame018scope03_s024 h28
  have h20 := stitchAt 20 4 frame018scope03_s020 h24
  have h16 := stitchAt 16 4 frame018scope03_s016 h20
  have h12 := stitchAt 12 4 frame018scope03_s012 h16
  have h8 := stitchAt 8 4 frame018scope03_s008 h12
  have h4 := stitchAt 4 4 frame018scope03_s004 h8
  have h0 := stitchAt 0 4 frame018scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch03 : batch03.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope03

private abbrev frame018test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch04.stop,F)

private theorem frame018scope04_s000 : ((fits04.drop 0).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s004 : ((fits04.drop 4).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s008 : ((fits04.drop 8).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s012 : ((fits04.drop 12).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s016 : ((fits04.drop 16).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s020 : ((fits04.drop 20).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s024 : ((fits04.drop 24).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s028 : ((fits04.drop 28).take 4).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_s032 : ((fits04.drop 32).take 3).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04_end : (fits04.drop 35).all frame018test04=true := by
  decide +kernel

private theorem frame018scope04 : fits04.all frame018test04=true := by
  have h32 := stitchAt 32 3 frame018scope04_s032 frame018scope04_end
  have h28 := stitchAt 28 4 frame018scope04_s028 h32
  have h24 := stitchAt 24 4 frame018scope04_s024 h28
  have h20 := stitchAt 20 4 frame018scope04_s020 h24
  have h16 := stitchAt 16 4 frame018scope04_s016 h20
  have h12 := stitchAt 12 4 frame018scope04_s012 h16
  have h8 := stitchAt 8 4 frame018scope04_s008 h12
  have h4 := stitchAt 4 4 frame018scope04_s004 h8
  have h0 := stitchAt 0 4 frame018scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch04 : batch04.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope04

private abbrev frame018test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch05.stop,F)

private theorem frame018scope05_s000 : ((fits05.drop 0).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s004 : ((fits05.drop 4).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s008 : ((fits05.drop 8).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s012 : ((fits05.drop 12).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s016 : ((fits05.drop 16).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s020 : ((fits05.drop 20).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s024 : ((fits05.drop 24).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s028 : ((fits05.drop 28).take 4).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_s032 : ((fits05.drop 32).take 3).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05_end : (fits05.drop 35).all frame018test05=true := by
  decide +kernel

private theorem frame018scope05 : fits05.all frame018test05=true := by
  have h32 := stitchAt 32 3 frame018scope05_s032 frame018scope05_end
  have h28 := stitchAt 28 4 frame018scope05_s028 h32
  have h24 := stitchAt 24 4 frame018scope05_s024 h28
  have h20 := stitchAt 20 4 frame018scope05_s020 h24
  have h16 := stitchAt 16 4 frame018scope05_s016 h20
  have h12 := stitchAt 12 4 frame018scope05_s012 h16
  have h8 := stitchAt 8 4 frame018scope05_s008 h12
  have h4 := stitchAt 4 4 frame018scope05_s004 h8
  have h0 := stitchAt 0 4 frame018scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch05 : batch05.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope05

private abbrev frame018test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch06.stop,F)

private theorem frame018scope06_s000 : ((fits06.drop 0).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s004 : ((fits06.drop 4).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s008 : ((fits06.drop 8).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s012 : ((fits06.drop 12).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s016 : ((fits06.drop 16).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s020 : ((fits06.drop 20).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s024 : ((fits06.drop 24).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s028 : ((fits06.drop 28).take 4).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_s032 : ((fits06.drop 32).take 3).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06_end : (fits06.drop 35).all frame018test06=true := by
  decide +kernel

private theorem frame018scope06 : fits06.all frame018test06=true := by
  have h32 := stitchAt 32 3 frame018scope06_s032 frame018scope06_end
  have h28 := stitchAt 28 4 frame018scope06_s028 h32
  have h24 := stitchAt 24 4 frame018scope06_s024 h28
  have h20 := stitchAt 20 4 frame018scope06_s020 h24
  have h16 := stitchAt 16 4 frame018scope06_s016 h20
  have h12 := stitchAt 12 4 frame018scope06_s012 h16
  have h8 := stitchAt 8 4 frame018scope06_s008 h12
  have h4 := stitchAt 4 4 frame018scope06_s004 h8
  have h0 := stitchAt 0 4 frame018scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch06 : batch06.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope06

private abbrev frame018test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame37 (fun z => List.lookup (guideCode z) guide018)
    (batch07.stop,F)

private theorem frame018scope07_s000 : ((fits07.drop 0).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s004 : ((fits07.drop 4).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s008 : ((fits07.drop 8).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s012 : ((fits07.drop 12).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s016 : ((fits07.drop 16).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s020 : ((fits07.drop 20).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s024 : ((fits07.drop 24).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s028 : ((fits07.drop 28).take 4).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_s032 : ((fits07.drop 32).take 3).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07_end : (fits07.drop 35).all frame018test07=true := by
  decide +kernel

private theorem frame018scope07 : fits07.all frame018test07=true := by
  have h32 := stitchAt 32 3 frame018scope07_s032 frame018scope07_end
  have h28 := stitchAt 28 4 frame018scope07_s028 h32
  have h24 := stitchAt 24 4 frame018scope07_s024 h28
  have h20 := stitchAt 20 4 frame018scope07_s020 h24
  have h16 := stitchAt 16 4 frame018scope07_s016 h20
  have h12 := stitchAt 12 4 frame018scope07_s012 h16
  have h8 := stitchAt 8 4 frame018scope07_s008 h12
  have h4 := stitchAt 4 4 frame018scope07_s004 h8
  have h0 := stitchAt 0 4 frame018scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame018batch07 : batch07.pickTest original frame37=true :=
  FitBatch.pickTest_of_scoped scoped018 frame018scope07

private theorem frameBatches018 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame37)=true := by
  simp only [List.all_cons,List.all_nil,frame018batch00,frame018batch01,frame018batch02,frame018batch03,frame018batch04,frame018batch05,frame018batch06,frame018batch07,Bool.and_self]

theorem frameOK018 : frameRankTest original useStop frame37=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches018

theorem stripOK019 : stripTest frame44=true := by decide +kernel

theorem spanOK019 : checkChain 1544 1536 [frame44.span]=true := by decide +kernel

private theorem guideAt019 : List.lookup frame44.span.1 guideTable=some guide019 := by
  decide +kernel

private theorem scoped019 : original.guide frame44.span.1 =
    (fun z => List.lookup (guideCode z) guide019) := by
  funext z
  change (List.lookup frame44.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide019
  simp only [guideAt019,Option.bind_some]

private abbrev frame019test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch00.stop,F)

private theorem frame019scope00_s000 : ((fits00.drop 0).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s004 : ((fits00.drop 4).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s008 : ((fits00.drop 8).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s012 : ((fits00.drop 12).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s016 : ((fits00.drop 16).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s020 : ((fits00.drop 20).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s024 : ((fits00.drop 24).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s028 : ((fits00.drop 28).take 4).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_s032 : ((fits00.drop 32).take 3).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00_end : (fits00.drop 35).all frame019test00=true := by
  decide +kernel

private theorem frame019scope00 : fits00.all frame019test00=true := by
  have h32 := stitchAt 32 3 frame019scope00_s032 frame019scope00_end
  have h28 := stitchAt 28 4 frame019scope00_s028 h32
  have h24 := stitchAt 24 4 frame019scope00_s024 h28
  have h20 := stitchAt 20 4 frame019scope00_s020 h24
  have h16 := stitchAt 16 4 frame019scope00_s016 h20
  have h12 := stitchAt 12 4 frame019scope00_s012 h16
  have h8 := stitchAt 8 4 frame019scope00_s008 h12
  have h4 := stitchAt 4 4 frame019scope00_s004 h8
  have h0 := stitchAt 0 4 frame019scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch00 : batch00.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope00

private abbrev frame019test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch01.stop,F)

private theorem frame019scope01_s000 : ((fits01.drop 0).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s004 : ((fits01.drop 4).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s008 : ((fits01.drop 8).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s012 : ((fits01.drop 12).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s016 : ((fits01.drop 16).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s020 : ((fits01.drop 20).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s024 : ((fits01.drop 24).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s028 : ((fits01.drop 28).take 4).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_s032 : ((fits01.drop 32).take 3).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01_end : (fits01.drop 35).all frame019test01=true := by
  decide +kernel

private theorem frame019scope01 : fits01.all frame019test01=true := by
  have h32 := stitchAt 32 3 frame019scope01_s032 frame019scope01_end
  have h28 := stitchAt 28 4 frame019scope01_s028 h32
  have h24 := stitchAt 24 4 frame019scope01_s024 h28
  have h20 := stitchAt 20 4 frame019scope01_s020 h24
  have h16 := stitchAt 16 4 frame019scope01_s016 h20
  have h12 := stitchAt 12 4 frame019scope01_s012 h16
  have h8 := stitchAt 8 4 frame019scope01_s008 h12
  have h4 := stitchAt 4 4 frame019scope01_s004 h8
  have h0 := stitchAt 0 4 frame019scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch01 : batch01.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope01

private abbrev frame019test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch02.stop,F)

private theorem frame019scope02_s000 : ((fits02.drop 0).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s004 : ((fits02.drop 4).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s008 : ((fits02.drop 8).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s012 : ((fits02.drop 12).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s016 : ((fits02.drop 16).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s020 : ((fits02.drop 20).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s024 : ((fits02.drop 24).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s028 : ((fits02.drop 28).take 4).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_s032 : ((fits02.drop 32).take 3).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02_end : (fits02.drop 35).all frame019test02=true := by
  decide +kernel

private theorem frame019scope02 : fits02.all frame019test02=true := by
  have h32 := stitchAt 32 3 frame019scope02_s032 frame019scope02_end
  have h28 := stitchAt 28 4 frame019scope02_s028 h32
  have h24 := stitchAt 24 4 frame019scope02_s024 h28
  have h20 := stitchAt 20 4 frame019scope02_s020 h24
  have h16 := stitchAt 16 4 frame019scope02_s016 h20
  have h12 := stitchAt 12 4 frame019scope02_s012 h16
  have h8 := stitchAt 8 4 frame019scope02_s008 h12
  have h4 := stitchAt 4 4 frame019scope02_s004 h8
  have h0 := stitchAt 0 4 frame019scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch02 : batch02.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope02

private abbrev frame019test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch03.stop,F)

private theorem frame019scope03_s000 : ((fits03.drop 0).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s004 : ((fits03.drop 4).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s008 : ((fits03.drop 8).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s012 : ((fits03.drop 12).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s016 : ((fits03.drop 16).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s020 : ((fits03.drop 20).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s024 : ((fits03.drop 24).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s028 : ((fits03.drop 28).take 4).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_s032 : ((fits03.drop 32).take 3).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03_end : (fits03.drop 35).all frame019test03=true := by
  decide +kernel

private theorem frame019scope03 : fits03.all frame019test03=true := by
  have h32 := stitchAt 32 3 frame019scope03_s032 frame019scope03_end
  have h28 := stitchAt 28 4 frame019scope03_s028 h32
  have h24 := stitchAt 24 4 frame019scope03_s024 h28
  have h20 := stitchAt 20 4 frame019scope03_s020 h24
  have h16 := stitchAt 16 4 frame019scope03_s016 h20
  have h12 := stitchAt 12 4 frame019scope03_s012 h16
  have h8 := stitchAt 8 4 frame019scope03_s008 h12
  have h4 := stitchAt 4 4 frame019scope03_s004 h8
  have h0 := stitchAt 0 4 frame019scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch03 : batch03.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope03

private abbrev frame019test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch04.stop,F)

private theorem frame019scope04_s000 : ((fits04.drop 0).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s004 : ((fits04.drop 4).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s008 : ((fits04.drop 8).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s012 : ((fits04.drop 12).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s016 : ((fits04.drop 16).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s020 : ((fits04.drop 20).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s024 : ((fits04.drop 24).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s028 : ((fits04.drop 28).take 4).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_s032 : ((fits04.drop 32).take 3).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04_end : (fits04.drop 35).all frame019test04=true := by
  decide +kernel

private theorem frame019scope04 : fits04.all frame019test04=true := by
  have h32 := stitchAt 32 3 frame019scope04_s032 frame019scope04_end
  have h28 := stitchAt 28 4 frame019scope04_s028 h32
  have h24 := stitchAt 24 4 frame019scope04_s024 h28
  have h20 := stitchAt 20 4 frame019scope04_s020 h24
  have h16 := stitchAt 16 4 frame019scope04_s016 h20
  have h12 := stitchAt 12 4 frame019scope04_s012 h16
  have h8 := stitchAt 8 4 frame019scope04_s008 h12
  have h4 := stitchAt 4 4 frame019scope04_s004 h8
  have h0 := stitchAt 0 4 frame019scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch04 : batch04.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope04

private abbrev frame019test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch05.stop,F)

private theorem frame019scope05_s000 : ((fits05.drop 0).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s004 : ((fits05.drop 4).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s008 : ((fits05.drop 8).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s012 : ((fits05.drop 12).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s016 : ((fits05.drop 16).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s020 : ((fits05.drop 20).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s024 : ((fits05.drop 24).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s028 : ((fits05.drop 28).take 4).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_s032 : ((fits05.drop 32).take 3).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05_end : (fits05.drop 35).all frame019test05=true := by
  decide +kernel

private theorem frame019scope05 : fits05.all frame019test05=true := by
  have h32 := stitchAt 32 3 frame019scope05_s032 frame019scope05_end
  have h28 := stitchAt 28 4 frame019scope05_s028 h32
  have h24 := stitchAt 24 4 frame019scope05_s024 h28
  have h20 := stitchAt 20 4 frame019scope05_s020 h24
  have h16 := stitchAt 16 4 frame019scope05_s016 h20
  have h12 := stitchAt 12 4 frame019scope05_s012 h16
  have h8 := stitchAt 8 4 frame019scope05_s008 h12
  have h4 := stitchAt 4 4 frame019scope05_s004 h8
  have h0 := stitchAt 0 4 frame019scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch05 : batch05.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope05

private abbrev frame019test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch06.stop,F)

private theorem frame019scope06_s000 : ((fits06.drop 0).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s004 : ((fits06.drop 4).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s008 : ((fits06.drop 8).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s012 : ((fits06.drop 12).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s016 : ((fits06.drop 16).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s020 : ((fits06.drop 20).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s024 : ((fits06.drop 24).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s028 : ((fits06.drop 28).take 4).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_s032 : ((fits06.drop 32).take 3).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06_end : (fits06.drop 35).all frame019test06=true := by
  decide +kernel

private theorem frame019scope06 : fits06.all frame019test06=true := by
  have h32 := stitchAt 32 3 frame019scope06_s032 frame019scope06_end
  have h28 := stitchAt 28 4 frame019scope06_s028 h32
  have h24 := stitchAt 24 4 frame019scope06_s024 h28
  have h20 := stitchAt 20 4 frame019scope06_s020 h24
  have h16 := stitchAt 16 4 frame019scope06_s016 h20
  have h12 := stitchAt 12 4 frame019scope06_s012 h16
  have h8 := stitchAt 8 4 frame019scope06_s008 h12
  have h4 := stitchAt 4 4 frame019scope06_s004 h8
  have h0 := stitchAt 0 4 frame019scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch06 : batch06.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope06

private abbrev frame019test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame44 (fun z => List.lookup (guideCode z) guide019)
    (batch07.stop,F)

private theorem frame019scope07_s000 : ((fits07.drop 0).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s004 : ((fits07.drop 4).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s008 : ((fits07.drop 8).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s012 : ((fits07.drop 12).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s016 : ((fits07.drop 16).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s020 : ((fits07.drop 20).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s024 : ((fits07.drop 24).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s028 : ((fits07.drop 28).take 4).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_s032 : ((fits07.drop 32).take 3).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07_end : (fits07.drop 35).all frame019test07=true := by
  decide +kernel

private theorem frame019scope07 : fits07.all frame019test07=true := by
  have h32 := stitchAt 32 3 frame019scope07_s032 frame019scope07_end
  have h28 := stitchAt 28 4 frame019scope07_s028 h32
  have h24 := stitchAt 24 4 frame019scope07_s024 h28
  have h20 := stitchAt 20 4 frame019scope07_s020 h24
  have h16 := stitchAt 16 4 frame019scope07_s016 h20
  have h12 := stitchAt 12 4 frame019scope07_s012 h16
  have h8 := stitchAt 8 4 frame019scope07_s008 h12
  have h4 := stitchAt 4 4 frame019scope07_s004 h8
  have h0 := stitchAt 0 4 frame019scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame019batch07 : batch07.pickTest original frame44=true :=
  FitBatch.pickTest_of_scoped scoped019 frame019scope07

private theorem frameBatches019 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame44)=true := by
  simp only [List.all_cons,List.all_nil,frame019batch00,frame019batch01,frame019batch02,frame019batch03,frame019batch04,frame019batch05,frame019batch06,frame019batch07,Bool.and_self]

theorem frameOK019 : frameRankTest original useStop frame44=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches019


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
