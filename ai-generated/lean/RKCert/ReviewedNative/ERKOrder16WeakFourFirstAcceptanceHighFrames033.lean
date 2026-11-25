module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK066 : stripTest frame134=true := by decide +kernel

theorem spanOK066 : checkChain 1788 1784 [frame134.span]=true := by decide +kernel

private theorem guideAt066 : List.lookup frame134.span.1 guideTable=some guide066 := by
  decide +kernel

private theorem scoped066 : original.guide frame134.span.1 =
    (fun z => List.lookup (guideCode z) guide066) := by
  funext z
  change (List.lookup frame134.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide066
  simp only [guideAt066,Option.bind_some]

private abbrev frame066test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch00.stop,F)

private theorem frame066scope00_s000 : ((fits00.drop 0).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s004 : ((fits00.drop 4).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s008 : ((fits00.drop 8).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s012 : ((fits00.drop 12).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s016 : ((fits00.drop 16).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s020 : ((fits00.drop 20).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s024 : ((fits00.drop 24).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s028 : ((fits00.drop 28).take 4).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_s032 : ((fits00.drop 32).take 3).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00_end : (fits00.drop 35).all frame066test00=true := by
  decide +kernel

private theorem frame066scope00 : fits00.all frame066test00=true := by
  have h32 := stitchAt 32 3 frame066scope00_s032 frame066scope00_end
  have h28 := stitchAt 28 4 frame066scope00_s028 h32
  have h24 := stitchAt 24 4 frame066scope00_s024 h28
  have h20 := stitchAt 20 4 frame066scope00_s020 h24
  have h16 := stitchAt 16 4 frame066scope00_s016 h20
  have h12 := stitchAt 12 4 frame066scope00_s012 h16
  have h8 := stitchAt 8 4 frame066scope00_s008 h12
  have h4 := stitchAt 4 4 frame066scope00_s004 h8
  have h0 := stitchAt 0 4 frame066scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch00 : batch00.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope00

private abbrev frame066test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch01.stop,F)

private theorem frame066scope01_s000 : ((fits01.drop 0).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s004 : ((fits01.drop 4).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s008 : ((fits01.drop 8).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s012 : ((fits01.drop 12).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s016 : ((fits01.drop 16).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s020 : ((fits01.drop 20).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s024 : ((fits01.drop 24).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s028 : ((fits01.drop 28).take 4).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_s032 : ((fits01.drop 32).take 3).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01_end : (fits01.drop 35).all frame066test01=true := by
  decide +kernel

private theorem frame066scope01 : fits01.all frame066test01=true := by
  have h32 := stitchAt 32 3 frame066scope01_s032 frame066scope01_end
  have h28 := stitchAt 28 4 frame066scope01_s028 h32
  have h24 := stitchAt 24 4 frame066scope01_s024 h28
  have h20 := stitchAt 20 4 frame066scope01_s020 h24
  have h16 := stitchAt 16 4 frame066scope01_s016 h20
  have h12 := stitchAt 12 4 frame066scope01_s012 h16
  have h8 := stitchAt 8 4 frame066scope01_s008 h12
  have h4 := stitchAt 4 4 frame066scope01_s004 h8
  have h0 := stitchAt 0 4 frame066scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch01 : batch01.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope01

private abbrev frame066test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch02.stop,F)

private theorem frame066scope02_s000 : ((fits02.drop 0).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s004 : ((fits02.drop 4).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s008 : ((fits02.drop 8).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s012 : ((fits02.drop 12).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s016 : ((fits02.drop 16).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s020 : ((fits02.drop 20).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s024 : ((fits02.drop 24).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s028 : ((fits02.drop 28).take 4).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_s032 : ((fits02.drop 32).take 3).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02_end : (fits02.drop 35).all frame066test02=true := by
  decide +kernel

private theorem frame066scope02 : fits02.all frame066test02=true := by
  have h32 := stitchAt 32 3 frame066scope02_s032 frame066scope02_end
  have h28 := stitchAt 28 4 frame066scope02_s028 h32
  have h24 := stitchAt 24 4 frame066scope02_s024 h28
  have h20 := stitchAt 20 4 frame066scope02_s020 h24
  have h16 := stitchAt 16 4 frame066scope02_s016 h20
  have h12 := stitchAt 12 4 frame066scope02_s012 h16
  have h8 := stitchAt 8 4 frame066scope02_s008 h12
  have h4 := stitchAt 4 4 frame066scope02_s004 h8
  have h0 := stitchAt 0 4 frame066scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch02 : batch02.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope02

private abbrev frame066test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch03.stop,F)

private theorem frame066scope03_s000 : ((fits03.drop 0).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s004 : ((fits03.drop 4).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s008 : ((fits03.drop 8).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s012 : ((fits03.drop 12).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s016 : ((fits03.drop 16).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s020 : ((fits03.drop 20).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s024 : ((fits03.drop 24).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s028 : ((fits03.drop 28).take 4).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_s032 : ((fits03.drop 32).take 3).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03_end : (fits03.drop 35).all frame066test03=true := by
  decide +kernel

private theorem frame066scope03 : fits03.all frame066test03=true := by
  have h32 := stitchAt 32 3 frame066scope03_s032 frame066scope03_end
  have h28 := stitchAt 28 4 frame066scope03_s028 h32
  have h24 := stitchAt 24 4 frame066scope03_s024 h28
  have h20 := stitchAt 20 4 frame066scope03_s020 h24
  have h16 := stitchAt 16 4 frame066scope03_s016 h20
  have h12 := stitchAt 12 4 frame066scope03_s012 h16
  have h8 := stitchAt 8 4 frame066scope03_s008 h12
  have h4 := stitchAt 4 4 frame066scope03_s004 h8
  have h0 := stitchAt 0 4 frame066scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch03 : batch03.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope03

private abbrev frame066test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch04.stop,F)

private theorem frame066scope04_s000 : ((fits04.drop 0).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s004 : ((fits04.drop 4).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s008 : ((fits04.drop 8).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s012 : ((fits04.drop 12).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s016 : ((fits04.drop 16).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s020 : ((fits04.drop 20).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s024 : ((fits04.drop 24).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s028 : ((fits04.drop 28).take 4).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_s032 : ((fits04.drop 32).take 3).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04_end : (fits04.drop 35).all frame066test04=true := by
  decide +kernel

private theorem frame066scope04 : fits04.all frame066test04=true := by
  have h32 := stitchAt 32 3 frame066scope04_s032 frame066scope04_end
  have h28 := stitchAt 28 4 frame066scope04_s028 h32
  have h24 := stitchAt 24 4 frame066scope04_s024 h28
  have h20 := stitchAt 20 4 frame066scope04_s020 h24
  have h16 := stitchAt 16 4 frame066scope04_s016 h20
  have h12 := stitchAt 12 4 frame066scope04_s012 h16
  have h8 := stitchAt 8 4 frame066scope04_s008 h12
  have h4 := stitchAt 4 4 frame066scope04_s004 h8
  have h0 := stitchAt 0 4 frame066scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch04 : batch04.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope04

private abbrev frame066test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch05.stop,F)

private theorem frame066scope05_s000 : ((fits05.drop 0).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s004 : ((fits05.drop 4).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s008 : ((fits05.drop 8).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s012 : ((fits05.drop 12).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s016 : ((fits05.drop 16).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s020 : ((fits05.drop 20).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s024 : ((fits05.drop 24).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s028 : ((fits05.drop 28).take 4).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_s032 : ((fits05.drop 32).take 3).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05_end : (fits05.drop 35).all frame066test05=true := by
  decide +kernel

private theorem frame066scope05 : fits05.all frame066test05=true := by
  have h32 := stitchAt 32 3 frame066scope05_s032 frame066scope05_end
  have h28 := stitchAt 28 4 frame066scope05_s028 h32
  have h24 := stitchAt 24 4 frame066scope05_s024 h28
  have h20 := stitchAt 20 4 frame066scope05_s020 h24
  have h16 := stitchAt 16 4 frame066scope05_s016 h20
  have h12 := stitchAt 12 4 frame066scope05_s012 h16
  have h8 := stitchAt 8 4 frame066scope05_s008 h12
  have h4 := stitchAt 4 4 frame066scope05_s004 h8
  have h0 := stitchAt 0 4 frame066scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch05 : batch05.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope05

private abbrev frame066test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch06.stop,F)

private theorem frame066scope06_s000 : ((fits06.drop 0).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s004 : ((fits06.drop 4).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s008 : ((fits06.drop 8).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s012 : ((fits06.drop 12).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s016 : ((fits06.drop 16).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s020 : ((fits06.drop 20).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s024 : ((fits06.drop 24).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s028 : ((fits06.drop 28).take 4).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_s032 : ((fits06.drop 32).take 3).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06_end : (fits06.drop 35).all frame066test06=true := by
  decide +kernel

private theorem frame066scope06 : fits06.all frame066test06=true := by
  have h32 := stitchAt 32 3 frame066scope06_s032 frame066scope06_end
  have h28 := stitchAt 28 4 frame066scope06_s028 h32
  have h24 := stitchAt 24 4 frame066scope06_s024 h28
  have h20 := stitchAt 20 4 frame066scope06_s020 h24
  have h16 := stitchAt 16 4 frame066scope06_s016 h20
  have h12 := stitchAt 12 4 frame066scope06_s012 h16
  have h8 := stitchAt 8 4 frame066scope06_s008 h12
  have h4 := stitchAt 4 4 frame066scope06_s004 h8
  have h0 := stitchAt 0 4 frame066scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch06 : batch06.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope06

private abbrev frame066test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame134 (fun z => List.lookup (guideCode z) guide066)
    (batch07.stop,F)

private theorem frame066scope07_s000 : ((fits07.drop 0).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s004 : ((fits07.drop 4).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s008 : ((fits07.drop 8).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s012 : ((fits07.drop 12).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s016 : ((fits07.drop 16).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s020 : ((fits07.drop 20).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s024 : ((fits07.drop 24).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s028 : ((fits07.drop 28).take 4).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_s032 : ((fits07.drop 32).take 3).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07_end : (fits07.drop 35).all frame066test07=true := by
  decide +kernel

private theorem frame066scope07 : fits07.all frame066test07=true := by
  have h32 := stitchAt 32 3 frame066scope07_s032 frame066scope07_end
  have h28 := stitchAt 28 4 frame066scope07_s028 h32
  have h24 := stitchAt 24 4 frame066scope07_s024 h28
  have h20 := stitchAt 20 4 frame066scope07_s020 h24
  have h16 := stitchAt 16 4 frame066scope07_s016 h20
  have h12 := stitchAt 12 4 frame066scope07_s012 h16
  have h8 := stitchAt 8 4 frame066scope07_s008 h12
  have h4 := stitchAt 4 4 frame066scope07_s004 h8
  have h0 := stitchAt 0 4 frame066scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame066batch07 : batch07.pickTest original frame134=true :=
  FitBatch.pickTest_of_scoped scoped066 frame066scope07

private theorem frameBatches066 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame134)=true := by
  simp only [List.all_cons,List.all_nil,frame066batch00,frame066batch01,frame066batch02,frame066batch03,frame066batch04,frame066batch05,frame066batch06,frame066batch07,Bool.and_self]

theorem frameOK066 : frameRankTest original useStop frame134=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches066

theorem stripOK067 : stripTest frame135=true := by decide +kernel

theorem spanOK067 : checkChain 1792 1788 [frame135.span]=true := by decide +kernel

private theorem guideAt067 : List.lookup frame135.span.1 guideTable=some guide067 := by
  decide +kernel

private theorem scoped067 : original.guide frame135.span.1 =
    (fun z => List.lookup (guideCode z) guide067) := by
  funext z
  change (List.lookup frame135.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide067
  simp only [guideAt067,Option.bind_some]

private abbrev frame067test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch00.stop,F)

private theorem frame067scope00_s000 : ((fits00.drop 0).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s004 : ((fits00.drop 4).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s008 : ((fits00.drop 8).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s012 : ((fits00.drop 12).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s016 : ((fits00.drop 16).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s020 : ((fits00.drop 20).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s024 : ((fits00.drop 24).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s028 : ((fits00.drop 28).take 4).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_s032 : ((fits00.drop 32).take 3).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00_end : (fits00.drop 35).all frame067test00=true := by
  decide +kernel

private theorem frame067scope00 : fits00.all frame067test00=true := by
  have h32 := stitchAt 32 3 frame067scope00_s032 frame067scope00_end
  have h28 := stitchAt 28 4 frame067scope00_s028 h32
  have h24 := stitchAt 24 4 frame067scope00_s024 h28
  have h20 := stitchAt 20 4 frame067scope00_s020 h24
  have h16 := stitchAt 16 4 frame067scope00_s016 h20
  have h12 := stitchAt 12 4 frame067scope00_s012 h16
  have h8 := stitchAt 8 4 frame067scope00_s008 h12
  have h4 := stitchAt 4 4 frame067scope00_s004 h8
  have h0 := stitchAt 0 4 frame067scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch00 : batch00.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope00

private abbrev frame067test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch01.stop,F)

private theorem frame067scope01_s000 : ((fits01.drop 0).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s004 : ((fits01.drop 4).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s008 : ((fits01.drop 8).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s012 : ((fits01.drop 12).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s016 : ((fits01.drop 16).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s020 : ((fits01.drop 20).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s024 : ((fits01.drop 24).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s028 : ((fits01.drop 28).take 4).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_s032 : ((fits01.drop 32).take 3).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01_end : (fits01.drop 35).all frame067test01=true := by
  decide +kernel

private theorem frame067scope01 : fits01.all frame067test01=true := by
  have h32 := stitchAt 32 3 frame067scope01_s032 frame067scope01_end
  have h28 := stitchAt 28 4 frame067scope01_s028 h32
  have h24 := stitchAt 24 4 frame067scope01_s024 h28
  have h20 := stitchAt 20 4 frame067scope01_s020 h24
  have h16 := stitchAt 16 4 frame067scope01_s016 h20
  have h12 := stitchAt 12 4 frame067scope01_s012 h16
  have h8 := stitchAt 8 4 frame067scope01_s008 h12
  have h4 := stitchAt 4 4 frame067scope01_s004 h8
  have h0 := stitchAt 0 4 frame067scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch01 : batch01.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope01

private abbrev frame067test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch02.stop,F)

private theorem frame067scope02_s000 : ((fits02.drop 0).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s004 : ((fits02.drop 4).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s008 : ((fits02.drop 8).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s012 : ((fits02.drop 12).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s016 : ((fits02.drop 16).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s020 : ((fits02.drop 20).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s024 : ((fits02.drop 24).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s028 : ((fits02.drop 28).take 4).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_s032 : ((fits02.drop 32).take 3).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02_end : (fits02.drop 35).all frame067test02=true := by
  decide +kernel

private theorem frame067scope02 : fits02.all frame067test02=true := by
  have h32 := stitchAt 32 3 frame067scope02_s032 frame067scope02_end
  have h28 := stitchAt 28 4 frame067scope02_s028 h32
  have h24 := stitchAt 24 4 frame067scope02_s024 h28
  have h20 := stitchAt 20 4 frame067scope02_s020 h24
  have h16 := stitchAt 16 4 frame067scope02_s016 h20
  have h12 := stitchAt 12 4 frame067scope02_s012 h16
  have h8 := stitchAt 8 4 frame067scope02_s008 h12
  have h4 := stitchAt 4 4 frame067scope02_s004 h8
  have h0 := stitchAt 0 4 frame067scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch02 : batch02.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope02

private abbrev frame067test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch03.stop,F)

private theorem frame067scope03_s000 : ((fits03.drop 0).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s004 : ((fits03.drop 4).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s008 : ((fits03.drop 8).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s012 : ((fits03.drop 12).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s016 : ((fits03.drop 16).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s020 : ((fits03.drop 20).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s024 : ((fits03.drop 24).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s028 : ((fits03.drop 28).take 4).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_s032 : ((fits03.drop 32).take 3).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03_end : (fits03.drop 35).all frame067test03=true := by
  decide +kernel

private theorem frame067scope03 : fits03.all frame067test03=true := by
  have h32 := stitchAt 32 3 frame067scope03_s032 frame067scope03_end
  have h28 := stitchAt 28 4 frame067scope03_s028 h32
  have h24 := stitchAt 24 4 frame067scope03_s024 h28
  have h20 := stitchAt 20 4 frame067scope03_s020 h24
  have h16 := stitchAt 16 4 frame067scope03_s016 h20
  have h12 := stitchAt 12 4 frame067scope03_s012 h16
  have h8 := stitchAt 8 4 frame067scope03_s008 h12
  have h4 := stitchAt 4 4 frame067scope03_s004 h8
  have h0 := stitchAt 0 4 frame067scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch03 : batch03.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope03

private abbrev frame067test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch04.stop,F)

private theorem frame067scope04_s000 : ((fits04.drop 0).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s004 : ((fits04.drop 4).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s008 : ((fits04.drop 8).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s012 : ((fits04.drop 12).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s016 : ((fits04.drop 16).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s020 : ((fits04.drop 20).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s024 : ((fits04.drop 24).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s028 : ((fits04.drop 28).take 4).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_s032 : ((fits04.drop 32).take 3).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04_end : (fits04.drop 35).all frame067test04=true := by
  decide +kernel

private theorem frame067scope04 : fits04.all frame067test04=true := by
  have h32 := stitchAt 32 3 frame067scope04_s032 frame067scope04_end
  have h28 := stitchAt 28 4 frame067scope04_s028 h32
  have h24 := stitchAt 24 4 frame067scope04_s024 h28
  have h20 := stitchAt 20 4 frame067scope04_s020 h24
  have h16 := stitchAt 16 4 frame067scope04_s016 h20
  have h12 := stitchAt 12 4 frame067scope04_s012 h16
  have h8 := stitchAt 8 4 frame067scope04_s008 h12
  have h4 := stitchAt 4 4 frame067scope04_s004 h8
  have h0 := stitchAt 0 4 frame067scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch04 : batch04.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope04

private abbrev frame067test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch05.stop,F)

private theorem frame067scope05_s000 : ((fits05.drop 0).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s004 : ((fits05.drop 4).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s008 : ((fits05.drop 8).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s012 : ((fits05.drop 12).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s016 : ((fits05.drop 16).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s020 : ((fits05.drop 20).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s024 : ((fits05.drop 24).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s028 : ((fits05.drop 28).take 4).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_s032 : ((fits05.drop 32).take 3).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05_end : (fits05.drop 35).all frame067test05=true := by
  decide +kernel

private theorem frame067scope05 : fits05.all frame067test05=true := by
  have h32 := stitchAt 32 3 frame067scope05_s032 frame067scope05_end
  have h28 := stitchAt 28 4 frame067scope05_s028 h32
  have h24 := stitchAt 24 4 frame067scope05_s024 h28
  have h20 := stitchAt 20 4 frame067scope05_s020 h24
  have h16 := stitchAt 16 4 frame067scope05_s016 h20
  have h12 := stitchAt 12 4 frame067scope05_s012 h16
  have h8 := stitchAt 8 4 frame067scope05_s008 h12
  have h4 := stitchAt 4 4 frame067scope05_s004 h8
  have h0 := stitchAt 0 4 frame067scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch05 : batch05.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope05

private abbrev frame067test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch06.stop,F)

private theorem frame067scope06_s000 : ((fits06.drop 0).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s004 : ((fits06.drop 4).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s008 : ((fits06.drop 8).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s012 : ((fits06.drop 12).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s016 : ((fits06.drop 16).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s020 : ((fits06.drop 20).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s024 : ((fits06.drop 24).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s028 : ((fits06.drop 28).take 4).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_s032 : ((fits06.drop 32).take 3).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06_end : (fits06.drop 35).all frame067test06=true := by
  decide +kernel

private theorem frame067scope06 : fits06.all frame067test06=true := by
  have h32 := stitchAt 32 3 frame067scope06_s032 frame067scope06_end
  have h28 := stitchAt 28 4 frame067scope06_s028 h32
  have h24 := stitchAt 24 4 frame067scope06_s024 h28
  have h20 := stitchAt 20 4 frame067scope06_s020 h24
  have h16 := stitchAt 16 4 frame067scope06_s016 h20
  have h12 := stitchAt 12 4 frame067scope06_s012 h16
  have h8 := stitchAt 8 4 frame067scope06_s008 h12
  have h4 := stitchAt 4 4 frame067scope06_s004 h8
  have h0 := stitchAt 0 4 frame067scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch06 : batch06.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope06

private abbrev frame067test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame135 (fun z => List.lookup (guideCode z) guide067)
    (batch07.stop,F)

private theorem frame067scope07_s000 : ((fits07.drop 0).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s004 : ((fits07.drop 4).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s008 : ((fits07.drop 8).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s012 : ((fits07.drop 12).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s016 : ((fits07.drop 16).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s020 : ((fits07.drop 20).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s024 : ((fits07.drop 24).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s028 : ((fits07.drop 28).take 4).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_s032 : ((fits07.drop 32).take 3).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07_end : (fits07.drop 35).all frame067test07=true := by
  decide +kernel

private theorem frame067scope07 : fits07.all frame067test07=true := by
  have h32 := stitchAt 32 3 frame067scope07_s032 frame067scope07_end
  have h28 := stitchAt 28 4 frame067scope07_s028 h32
  have h24 := stitchAt 24 4 frame067scope07_s024 h28
  have h20 := stitchAt 20 4 frame067scope07_s020 h24
  have h16 := stitchAt 16 4 frame067scope07_s016 h20
  have h12 := stitchAt 12 4 frame067scope07_s012 h16
  have h8 := stitchAt 8 4 frame067scope07_s008 h12
  have h4 := stitchAt 4 4 frame067scope07_s004 h8
  have h0 := stitchAt 0 4 frame067scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame067batch07 : batch07.pickTest original frame135=true :=
  FitBatch.pickTest_of_scoped scoped067 frame067scope07

private theorem frameBatches067 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame135)=true := by
  simp only [List.all_cons,List.all_nil,frame067batch00,frame067batch01,frame067batch02,frame067batch03,frame067batch04,frame067batch05,frame067batch06,frame067batch07,Bool.and_self]

theorem frameOK067 : frameRankTest original useStop frame135=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches067


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
