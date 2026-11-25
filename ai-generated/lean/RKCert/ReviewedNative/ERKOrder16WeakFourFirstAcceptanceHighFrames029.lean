module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK058 : stripTest frame119=true := by decide +kernel

theorem spanOK058 : checkChain 1768 1767 [frame119.span]=true := by decide +kernel

private theorem guideAt058 : List.lookup frame119.span.1 guideTable=some guide058 := by
  decide +kernel

private theorem scoped058 : original.guide frame119.span.1 =
    (fun z => List.lookup (guideCode z) guide058) := by
  funext z
  change (List.lookup frame119.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide058
  simp only [guideAt058,Option.bind_some]

private abbrev frame058test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch00.stop,F)

private theorem frame058scope00_s000 : ((fits00.drop 0).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s004 : ((fits00.drop 4).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s008 : ((fits00.drop 8).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s012 : ((fits00.drop 12).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s016 : ((fits00.drop 16).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s020 : ((fits00.drop 20).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s024 : ((fits00.drop 24).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s028 : ((fits00.drop 28).take 4).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_s032 : ((fits00.drop 32).take 3).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00_end : (fits00.drop 35).all frame058test00=true := by
  decide +kernel

private theorem frame058scope00 : fits00.all frame058test00=true := by
  have h32 := stitchAt 32 3 frame058scope00_s032 frame058scope00_end
  have h28 := stitchAt 28 4 frame058scope00_s028 h32
  have h24 := stitchAt 24 4 frame058scope00_s024 h28
  have h20 := stitchAt 20 4 frame058scope00_s020 h24
  have h16 := stitchAt 16 4 frame058scope00_s016 h20
  have h12 := stitchAt 12 4 frame058scope00_s012 h16
  have h8 := stitchAt 8 4 frame058scope00_s008 h12
  have h4 := stitchAt 4 4 frame058scope00_s004 h8
  have h0 := stitchAt 0 4 frame058scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch00 : batch00.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope00

private abbrev frame058test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch01.stop,F)

private theorem frame058scope01_s000 : ((fits01.drop 0).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s004 : ((fits01.drop 4).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s008 : ((fits01.drop 8).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s012 : ((fits01.drop 12).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s016 : ((fits01.drop 16).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s020 : ((fits01.drop 20).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s024 : ((fits01.drop 24).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s028 : ((fits01.drop 28).take 4).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_s032 : ((fits01.drop 32).take 3).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01_end : (fits01.drop 35).all frame058test01=true := by
  decide +kernel

private theorem frame058scope01 : fits01.all frame058test01=true := by
  have h32 := stitchAt 32 3 frame058scope01_s032 frame058scope01_end
  have h28 := stitchAt 28 4 frame058scope01_s028 h32
  have h24 := stitchAt 24 4 frame058scope01_s024 h28
  have h20 := stitchAt 20 4 frame058scope01_s020 h24
  have h16 := stitchAt 16 4 frame058scope01_s016 h20
  have h12 := stitchAt 12 4 frame058scope01_s012 h16
  have h8 := stitchAt 8 4 frame058scope01_s008 h12
  have h4 := stitchAt 4 4 frame058scope01_s004 h8
  have h0 := stitchAt 0 4 frame058scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch01 : batch01.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope01

private abbrev frame058test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch02.stop,F)

private theorem frame058scope02_s000 : ((fits02.drop 0).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s004 : ((fits02.drop 4).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s008 : ((fits02.drop 8).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s012 : ((fits02.drop 12).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s016 : ((fits02.drop 16).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s020 : ((fits02.drop 20).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s024 : ((fits02.drop 24).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s028 : ((fits02.drop 28).take 4).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_s032 : ((fits02.drop 32).take 3).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02_end : (fits02.drop 35).all frame058test02=true := by
  decide +kernel

private theorem frame058scope02 : fits02.all frame058test02=true := by
  have h32 := stitchAt 32 3 frame058scope02_s032 frame058scope02_end
  have h28 := stitchAt 28 4 frame058scope02_s028 h32
  have h24 := stitchAt 24 4 frame058scope02_s024 h28
  have h20 := stitchAt 20 4 frame058scope02_s020 h24
  have h16 := stitchAt 16 4 frame058scope02_s016 h20
  have h12 := stitchAt 12 4 frame058scope02_s012 h16
  have h8 := stitchAt 8 4 frame058scope02_s008 h12
  have h4 := stitchAt 4 4 frame058scope02_s004 h8
  have h0 := stitchAt 0 4 frame058scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch02 : batch02.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope02

private abbrev frame058test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch03.stop,F)

private theorem frame058scope03_s000 : ((fits03.drop 0).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s004 : ((fits03.drop 4).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s008 : ((fits03.drop 8).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s012 : ((fits03.drop 12).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s016 : ((fits03.drop 16).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s020 : ((fits03.drop 20).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s024 : ((fits03.drop 24).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s028 : ((fits03.drop 28).take 4).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_s032 : ((fits03.drop 32).take 3).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03_end : (fits03.drop 35).all frame058test03=true := by
  decide +kernel

private theorem frame058scope03 : fits03.all frame058test03=true := by
  have h32 := stitchAt 32 3 frame058scope03_s032 frame058scope03_end
  have h28 := stitchAt 28 4 frame058scope03_s028 h32
  have h24 := stitchAt 24 4 frame058scope03_s024 h28
  have h20 := stitchAt 20 4 frame058scope03_s020 h24
  have h16 := stitchAt 16 4 frame058scope03_s016 h20
  have h12 := stitchAt 12 4 frame058scope03_s012 h16
  have h8 := stitchAt 8 4 frame058scope03_s008 h12
  have h4 := stitchAt 4 4 frame058scope03_s004 h8
  have h0 := stitchAt 0 4 frame058scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch03 : batch03.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope03

private abbrev frame058test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch04.stop,F)

private theorem frame058scope04_s000 : ((fits04.drop 0).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s004 : ((fits04.drop 4).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s008 : ((fits04.drop 8).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s012 : ((fits04.drop 12).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s016 : ((fits04.drop 16).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s020 : ((fits04.drop 20).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s024 : ((fits04.drop 24).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s028 : ((fits04.drop 28).take 4).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_s032 : ((fits04.drop 32).take 3).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04_end : (fits04.drop 35).all frame058test04=true := by
  decide +kernel

private theorem frame058scope04 : fits04.all frame058test04=true := by
  have h32 := stitchAt 32 3 frame058scope04_s032 frame058scope04_end
  have h28 := stitchAt 28 4 frame058scope04_s028 h32
  have h24 := stitchAt 24 4 frame058scope04_s024 h28
  have h20 := stitchAt 20 4 frame058scope04_s020 h24
  have h16 := stitchAt 16 4 frame058scope04_s016 h20
  have h12 := stitchAt 12 4 frame058scope04_s012 h16
  have h8 := stitchAt 8 4 frame058scope04_s008 h12
  have h4 := stitchAt 4 4 frame058scope04_s004 h8
  have h0 := stitchAt 0 4 frame058scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch04 : batch04.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope04

private abbrev frame058test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch05.stop,F)

private theorem frame058scope05_s000 : ((fits05.drop 0).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s004 : ((fits05.drop 4).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s008 : ((fits05.drop 8).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s012 : ((fits05.drop 12).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s016 : ((fits05.drop 16).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s020 : ((fits05.drop 20).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s024 : ((fits05.drop 24).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s028 : ((fits05.drop 28).take 4).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_s032 : ((fits05.drop 32).take 3).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05_end : (fits05.drop 35).all frame058test05=true := by
  decide +kernel

private theorem frame058scope05 : fits05.all frame058test05=true := by
  have h32 := stitchAt 32 3 frame058scope05_s032 frame058scope05_end
  have h28 := stitchAt 28 4 frame058scope05_s028 h32
  have h24 := stitchAt 24 4 frame058scope05_s024 h28
  have h20 := stitchAt 20 4 frame058scope05_s020 h24
  have h16 := stitchAt 16 4 frame058scope05_s016 h20
  have h12 := stitchAt 12 4 frame058scope05_s012 h16
  have h8 := stitchAt 8 4 frame058scope05_s008 h12
  have h4 := stitchAt 4 4 frame058scope05_s004 h8
  have h0 := stitchAt 0 4 frame058scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch05 : batch05.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope05

private abbrev frame058test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch06.stop,F)

private theorem frame058scope06_s000 : ((fits06.drop 0).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s004 : ((fits06.drop 4).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s008 : ((fits06.drop 8).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s012 : ((fits06.drop 12).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s016 : ((fits06.drop 16).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s020 : ((fits06.drop 20).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s024 : ((fits06.drop 24).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s028 : ((fits06.drop 28).take 4).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_s032 : ((fits06.drop 32).take 3).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06_end : (fits06.drop 35).all frame058test06=true := by
  decide +kernel

private theorem frame058scope06 : fits06.all frame058test06=true := by
  have h32 := stitchAt 32 3 frame058scope06_s032 frame058scope06_end
  have h28 := stitchAt 28 4 frame058scope06_s028 h32
  have h24 := stitchAt 24 4 frame058scope06_s024 h28
  have h20 := stitchAt 20 4 frame058scope06_s020 h24
  have h16 := stitchAt 16 4 frame058scope06_s016 h20
  have h12 := stitchAt 12 4 frame058scope06_s012 h16
  have h8 := stitchAt 8 4 frame058scope06_s008 h12
  have h4 := stitchAt 4 4 frame058scope06_s004 h8
  have h0 := stitchAt 0 4 frame058scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch06 : batch06.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope06

private abbrev frame058test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame119 (fun z => List.lookup (guideCode z) guide058)
    (batch07.stop,F)

private theorem frame058scope07_s000 : ((fits07.drop 0).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s004 : ((fits07.drop 4).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s008 : ((fits07.drop 8).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s012 : ((fits07.drop 12).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s016 : ((fits07.drop 16).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s020 : ((fits07.drop 20).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s024 : ((fits07.drop 24).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s028 : ((fits07.drop 28).take 4).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_s032 : ((fits07.drop 32).take 3).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07_end : (fits07.drop 35).all frame058test07=true := by
  decide +kernel

private theorem frame058scope07 : fits07.all frame058test07=true := by
  have h32 := stitchAt 32 3 frame058scope07_s032 frame058scope07_end
  have h28 := stitchAt 28 4 frame058scope07_s028 h32
  have h24 := stitchAt 24 4 frame058scope07_s024 h28
  have h20 := stitchAt 20 4 frame058scope07_s020 h24
  have h16 := stitchAt 16 4 frame058scope07_s016 h20
  have h12 := stitchAt 12 4 frame058scope07_s012 h16
  have h8 := stitchAt 8 4 frame058scope07_s008 h12
  have h4 := stitchAt 4 4 frame058scope07_s004 h8
  have h0 := stitchAt 0 4 frame058scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame058batch07 : batch07.pickTest original frame119=true :=
  FitBatch.pickTest_of_scoped scoped058 frame058scope07

private theorem frameBatches058 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame119)=true := by
  simp only [List.all_cons,List.all_nil,frame058batch00,frame058batch01,frame058batch02,frame058batch03,frame058batch04,frame058batch05,frame058batch06,frame058batch07,Bool.and_self]

theorem frameOK058 : frameRankTest original useStop frame119=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches058

theorem stripOK059 : stripTest frame122=true := by decide +kernel

theorem spanOK059 : checkChain 1770 1768 [frame122.span]=true := by decide +kernel

private theorem guideAt059 : List.lookup frame122.span.1 guideTable=some guide059 := by
  decide +kernel

private theorem scoped059 : original.guide frame122.span.1 =
    (fun z => List.lookup (guideCode z) guide059) := by
  funext z
  change (List.lookup frame122.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide059
  simp only [guideAt059,Option.bind_some]

private abbrev frame059test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch00.stop,F)

private theorem frame059scope00_s000 : ((fits00.drop 0).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s004 : ((fits00.drop 4).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s008 : ((fits00.drop 8).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s012 : ((fits00.drop 12).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s016 : ((fits00.drop 16).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s020 : ((fits00.drop 20).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s024 : ((fits00.drop 24).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s028 : ((fits00.drop 28).take 4).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_s032 : ((fits00.drop 32).take 3).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00_end : (fits00.drop 35).all frame059test00=true := by
  decide +kernel

private theorem frame059scope00 : fits00.all frame059test00=true := by
  have h32 := stitchAt 32 3 frame059scope00_s032 frame059scope00_end
  have h28 := stitchAt 28 4 frame059scope00_s028 h32
  have h24 := stitchAt 24 4 frame059scope00_s024 h28
  have h20 := stitchAt 20 4 frame059scope00_s020 h24
  have h16 := stitchAt 16 4 frame059scope00_s016 h20
  have h12 := stitchAt 12 4 frame059scope00_s012 h16
  have h8 := stitchAt 8 4 frame059scope00_s008 h12
  have h4 := stitchAt 4 4 frame059scope00_s004 h8
  have h0 := stitchAt 0 4 frame059scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch00 : batch00.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope00

private abbrev frame059test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch01.stop,F)

private theorem frame059scope01_s000 : ((fits01.drop 0).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s004 : ((fits01.drop 4).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s008 : ((fits01.drop 8).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s012 : ((fits01.drop 12).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s016 : ((fits01.drop 16).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s020 : ((fits01.drop 20).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s024 : ((fits01.drop 24).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s028 : ((fits01.drop 28).take 4).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_s032 : ((fits01.drop 32).take 3).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01_end : (fits01.drop 35).all frame059test01=true := by
  decide +kernel

private theorem frame059scope01 : fits01.all frame059test01=true := by
  have h32 := stitchAt 32 3 frame059scope01_s032 frame059scope01_end
  have h28 := stitchAt 28 4 frame059scope01_s028 h32
  have h24 := stitchAt 24 4 frame059scope01_s024 h28
  have h20 := stitchAt 20 4 frame059scope01_s020 h24
  have h16 := stitchAt 16 4 frame059scope01_s016 h20
  have h12 := stitchAt 12 4 frame059scope01_s012 h16
  have h8 := stitchAt 8 4 frame059scope01_s008 h12
  have h4 := stitchAt 4 4 frame059scope01_s004 h8
  have h0 := stitchAt 0 4 frame059scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch01 : batch01.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope01

private abbrev frame059test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch02.stop,F)

private theorem frame059scope02_s000 : ((fits02.drop 0).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s004 : ((fits02.drop 4).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s008 : ((fits02.drop 8).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s012 : ((fits02.drop 12).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s016 : ((fits02.drop 16).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s020 : ((fits02.drop 20).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s024 : ((fits02.drop 24).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s028 : ((fits02.drop 28).take 4).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_s032 : ((fits02.drop 32).take 3).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02_end : (fits02.drop 35).all frame059test02=true := by
  decide +kernel

private theorem frame059scope02 : fits02.all frame059test02=true := by
  have h32 := stitchAt 32 3 frame059scope02_s032 frame059scope02_end
  have h28 := stitchAt 28 4 frame059scope02_s028 h32
  have h24 := stitchAt 24 4 frame059scope02_s024 h28
  have h20 := stitchAt 20 4 frame059scope02_s020 h24
  have h16 := stitchAt 16 4 frame059scope02_s016 h20
  have h12 := stitchAt 12 4 frame059scope02_s012 h16
  have h8 := stitchAt 8 4 frame059scope02_s008 h12
  have h4 := stitchAt 4 4 frame059scope02_s004 h8
  have h0 := stitchAt 0 4 frame059scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch02 : batch02.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope02

private abbrev frame059test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch03.stop,F)

private theorem frame059scope03_s000 : ((fits03.drop 0).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s004 : ((fits03.drop 4).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s008 : ((fits03.drop 8).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s012 : ((fits03.drop 12).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s016 : ((fits03.drop 16).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s020 : ((fits03.drop 20).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s024 : ((fits03.drop 24).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s028 : ((fits03.drop 28).take 4).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_s032 : ((fits03.drop 32).take 3).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03_end : (fits03.drop 35).all frame059test03=true := by
  decide +kernel

private theorem frame059scope03 : fits03.all frame059test03=true := by
  have h32 := stitchAt 32 3 frame059scope03_s032 frame059scope03_end
  have h28 := stitchAt 28 4 frame059scope03_s028 h32
  have h24 := stitchAt 24 4 frame059scope03_s024 h28
  have h20 := stitchAt 20 4 frame059scope03_s020 h24
  have h16 := stitchAt 16 4 frame059scope03_s016 h20
  have h12 := stitchAt 12 4 frame059scope03_s012 h16
  have h8 := stitchAt 8 4 frame059scope03_s008 h12
  have h4 := stitchAt 4 4 frame059scope03_s004 h8
  have h0 := stitchAt 0 4 frame059scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch03 : batch03.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope03

private abbrev frame059test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch04.stop,F)

private theorem frame059scope04_s000 : ((fits04.drop 0).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s004 : ((fits04.drop 4).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s008 : ((fits04.drop 8).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s012 : ((fits04.drop 12).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s016 : ((fits04.drop 16).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s020 : ((fits04.drop 20).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s024 : ((fits04.drop 24).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s028 : ((fits04.drop 28).take 4).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_s032 : ((fits04.drop 32).take 3).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04_end : (fits04.drop 35).all frame059test04=true := by
  decide +kernel

private theorem frame059scope04 : fits04.all frame059test04=true := by
  have h32 := stitchAt 32 3 frame059scope04_s032 frame059scope04_end
  have h28 := stitchAt 28 4 frame059scope04_s028 h32
  have h24 := stitchAt 24 4 frame059scope04_s024 h28
  have h20 := stitchAt 20 4 frame059scope04_s020 h24
  have h16 := stitchAt 16 4 frame059scope04_s016 h20
  have h12 := stitchAt 12 4 frame059scope04_s012 h16
  have h8 := stitchAt 8 4 frame059scope04_s008 h12
  have h4 := stitchAt 4 4 frame059scope04_s004 h8
  have h0 := stitchAt 0 4 frame059scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch04 : batch04.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope04

private abbrev frame059test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch05.stop,F)

private theorem frame059scope05_s000 : ((fits05.drop 0).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s004 : ((fits05.drop 4).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s008 : ((fits05.drop 8).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s012 : ((fits05.drop 12).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s016 : ((fits05.drop 16).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s020 : ((fits05.drop 20).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s024 : ((fits05.drop 24).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s028 : ((fits05.drop 28).take 4).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_s032 : ((fits05.drop 32).take 3).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05_end : (fits05.drop 35).all frame059test05=true := by
  decide +kernel

private theorem frame059scope05 : fits05.all frame059test05=true := by
  have h32 := stitchAt 32 3 frame059scope05_s032 frame059scope05_end
  have h28 := stitchAt 28 4 frame059scope05_s028 h32
  have h24 := stitchAt 24 4 frame059scope05_s024 h28
  have h20 := stitchAt 20 4 frame059scope05_s020 h24
  have h16 := stitchAt 16 4 frame059scope05_s016 h20
  have h12 := stitchAt 12 4 frame059scope05_s012 h16
  have h8 := stitchAt 8 4 frame059scope05_s008 h12
  have h4 := stitchAt 4 4 frame059scope05_s004 h8
  have h0 := stitchAt 0 4 frame059scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch05 : batch05.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope05

private abbrev frame059test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch06.stop,F)

private theorem frame059scope06_s000 : ((fits06.drop 0).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s004 : ((fits06.drop 4).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s008 : ((fits06.drop 8).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s012 : ((fits06.drop 12).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s016 : ((fits06.drop 16).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s020 : ((fits06.drop 20).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s024 : ((fits06.drop 24).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s028 : ((fits06.drop 28).take 4).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_s032 : ((fits06.drop 32).take 3).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06_end : (fits06.drop 35).all frame059test06=true := by
  decide +kernel

private theorem frame059scope06 : fits06.all frame059test06=true := by
  have h32 := stitchAt 32 3 frame059scope06_s032 frame059scope06_end
  have h28 := stitchAt 28 4 frame059scope06_s028 h32
  have h24 := stitchAt 24 4 frame059scope06_s024 h28
  have h20 := stitchAt 20 4 frame059scope06_s020 h24
  have h16 := stitchAt 16 4 frame059scope06_s016 h20
  have h12 := stitchAt 12 4 frame059scope06_s012 h16
  have h8 := stitchAt 8 4 frame059scope06_s008 h12
  have h4 := stitchAt 4 4 frame059scope06_s004 h8
  have h0 := stitchAt 0 4 frame059scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch06 : batch06.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope06

private abbrev frame059test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame122 (fun z => List.lookup (guideCode z) guide059)
    (batch07.stop,F)

private theorem frame059scope07_s000 : ((fits07.drop 0).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s004 : ((fits07.drop 4).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s008 : ((fits07.drop 8).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s012 : ((fits07.drop 12).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s016 : ((fits07.drop 16).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s020 : ((fits07.drop 20).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s024 : ((fits07.drop 24).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s028 : ((fits07.drop 28).take 4).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_s032 : ((fits07.drop 32).take 3).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07_end : (fits07.drop 35).all frame059test07=true := by
  decide +kernel

private theorem frame059scope07 : fits07.all frame059test07=true := by
  have h32 := stitchAt 32 3 frame059scope07_s032 frame059scope07_end
  have h28 := stitchAt 28 4 frame059scope07_s028 h32
  have h24 := stitchAt 24 4 frame059scope07_s024 h28
  have h20 := stitchAt 20 4 frame059scope07_s020 h24
  have h16 := stitchAt 16 4 frame059scope07_s016 h20
  have h12 := stitchAt 12 4 frame059scope07_s012 h16
  have h8 := stitchAt 8 4 frame059scope07_s008 h12
  have h4 := stitchAt 4 4 frame059scope07_s004 h8
  have h0 := stitchAt 0 4 frame059scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame059batch07 : batch07.pickTest original frame122=true :=
  FitBatch.pickTest_of_scoped scoped059 frame059scope07

private theorem frameBatches059 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame122)=true := by
  simp only [List.all_cons,List.all_nil,frame059batch00,frame059batch01,frame059batch02,frame059batch03,frame059batch04,frame059batch05,frame059batch06,frame059batch07,Bool.and_self]

theorem frameOK059 : frameRankTest original useStop frame122=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches059


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
