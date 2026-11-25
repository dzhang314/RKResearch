module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK028 : stripTest frame59=true := by decide +kernel

theorem spanOK028 : checkChain 1648 1640 [frame59.span]=true := by decide +kernel

private theorem guideAt028 : List.lookup frame59.span.1 guideTable=some guide028 := by
  decide +kernel

private theorem scoped028 : original.guide frame59.span.1 =
    (fun z => List.lookup (guideCode z) guide028) := by
  funext z
  change (List.lookup frame59.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide028
  simp only [guideAt028,Option.bind_some]

private abbrev frame028test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch00.stop,F)

private theorem frame028scope00_s000 : ((fits00.drop 0).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s004 : ((fits00.drop 4).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s008 : ((fits00.drop 8).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s012 : ((fits00.drop 12).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s016 : ((fits00.drop 16).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s020 : ((fits00.drop 20).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s024 : ((fits00.drop 24).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s028 : ((fits00.drop 28).take 4).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_s032 : ((fits00.drop 32).take 3).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00_end : (fits00.drop 35).all frame028test00=true := by
  decide +kernel

private theorem frame028scope00 : fits00.all frame028test00=true := by
  have h32 := stitchAt 32 3 frame028scope00_s032 frame028scope00_end
  have h28 := stitchAt 28 4 frame028scope00_s028 h32
  have h24 := stitchAt 24 4 frame028scope00_s024 h28
  have h20 := stitchAt 20 4 frame028scope00_s020 h24
  have h16 := stitchAt 16 4 frame028scope00_s016 h20
  have h12 := stitchAt 12 4 frame028scope00_s012 h16
  have h8 := stitchAt 8 4 frame028scope00_s008 h12
  have h4 := stitchAt 4 4 frame028scope00_s004 h8
  have h0 := stitchAt 0 4 frame028scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch00 : batch00.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope00

private abbrev frame028test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch01.stop,F)

private theorem frame028scope01_s000 : ((fits01.drop 0).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s004 : ((fits01.drop 4).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s008 : ((fits01.drop 8).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s012 : ((fits01.drop 12).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s016 : ((fits01.drop 16).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s020 : ((fits01.drop 20).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s024 : ((fits01.drop 24).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s028 : ((fits01.drop 28).take 4).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_s032 : ((fits01.drop 32).take 3).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01_end : (fits01.drop 35).all frame028test01=true := by
  decide +kernel

private theorem frame028scope01 : fits01.all frame028test01=true := by
  have h32 := stitchAt 32 3 frame028scope01_s032 frame028scope01_end
  have h28 := stitchAt 28 4 frame028scope01_s028 h32
  have h24 := stitchAt 24 4 frame028scope01_s024 h28
  have h20 := stitchAt 20 4 frame028scope01_s020 h24
  have h16 := stitchAt 16 4 frame028scope01_s016 h20
  have h12 := stitchAt 12 4 frame028scope01_s012 h16
  have h8 := stitchAt 8 4 frame028scope01_s008 h12
  have h4 := stitchAt 4 4 frame028scope01_s004 h8
  have h0 := stitchAt 0 4 frame028scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch01 : batch01.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope01

private abbrev frame028test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch02.stop,F)

private theorem frame028scope02_s000 : ((fits02.drop 0).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s004 : ((fits02.drop 4).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s008 : ((fits02.drop 8).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s012 : ((fits02.drop 12).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s016 : ((fits02.drop 16).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s020 : ((fits02.drop 20).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s024 : ((fits02.drop 24).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s028 : ((fits02.drop 28).take 4).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_s032 : ((fits02.drop 32).take 3).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02_end : (fits02.drop 35).all frame028test02=true := by
  decide +kernel

private theorem frame028scope02 : fits02.all frame028test02=true := by
  have h32 := stitchAt 32 3 frame028scope02_s032 frame028scope02_end
  have h28 := stitchAt 28 4 frame028scope02_s028 h32
  have h24 := stitchAt 24 4 frame028scope02_s024 h28
  have h20 := stitchAt 20 4 frame028scope02_s020 h24
  have h16 := stitchAt 16 4 frame028scope02_s016 h20
  have h12 := stitchAt 12 4 frame028scope02_s012 h16
  have h8 := stitchAt 8 4 frame028scope02_s008 h12
  have h4 := stitchAt 4 4 frame028scope02_s004 h8
  have h0 := stitchAt 0 4 frame028scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch02 : batch02.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope02

private abbrev frame028test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch03.stop,F)

private theorem frame028scope03_s000 : ((fits03.drop 0).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s004 : ((fits03.drop 4).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s008 : ((fits03.drop 8).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s012 : ((fits03.drop 12).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s016 : ((fits03.drop 16).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s020 : ((fits03.drop 20).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s024 : ((fits03.drop 24).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s028 : ((fits03.drop 28).take 4).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_s032 : ((fits03.drop 32).take 3).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03_end : (fits03.drop 35).all frame028test03=true := by
  decide +kernel

private theorem frame028scope03 : fits03.all frame028test03=true := by
  have h32 := stitchAt 32 3 frame028scope03_s032 frame028scope03_end
  have h28 := stitchAt 28 4 frame028scope03_s028 h32
  have h24 := stitchAt 24 4 frame028scope03_s024 h28
  have h20 := stitchAt 20 4 frame028scope03_s020 h24
  have h16 := stitchAt 16 4 frame028scope03_s016 h20
  have h12 := stitchAt 12 4 frame028scope03_s012 h16
  have h8 := stitchAt 8 4 frame028scope03_s008 h12
  have h4 := stitchAt 4 4 frame028scope03_s004 h8
  have h0 := stitchAt 0 4 frame028scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch03 : batch03.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope03

private abbrev frame028test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch04.stop,F)

private theorem frame028scope04_s000 : ((fits04.drop 0).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s004 : ((fits04.drop 4).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s008 : ((fits04.drop 8).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s012 : ((fits04.drop 12).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s016 : ((fits04.drop 16).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s020 : ((fits04.drop 20).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s024 : ((fits04.drop 24).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s028 : ((fits04.drop 28).take 4).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_s032 : ((fits04.drop 32).take 3).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04_end : (fits04.drop 35).all frame028test04=true := by
  decide +kernel

private theorem frame028scope04 : fits04.all frame028test04=true := by
  have h32 := stitchAt 32 3 frame028scope04_s032 frame028scope04_end
  have h28 := stitchAt 28 4 frame028scope04_s028 h32
  have h24 := stitchAt 24 4 frame028scope04_s024 h28
  have h20 := stitchAt 20 4 frame028scope04_s020 h24
  have h16 := stitchAt 16 4 frame028scope04_s016 h20
  have h12 := stitchAt 12 4 frame028scope04_s012 h16
  have h8 := stitchAt 8 4 frame028scope04_s008 h12
  have h4 := stitchAt 4 4 frame028scope04_s004 h8
  have h0 := stitchAt 0 4 frame028scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch04 : batch04.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope04

private abbrev frame028test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch05.stop,F)

private theorem frame028scope05_s000 : ((fits05.drop 0).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s004 : ((fits05.drop 4).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s008 : ((fits05.drop 8).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s012 : ((fits05.drop 12).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s016 : ((fits05.drop 16).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s020 : ((fits05.drop 20).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s024 : ((fits05.drop 24).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s028 : ((fits05.drop 28).take 4).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_s032 : ((fits05.drop 32).take 3).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05_end : (fits05.drop 35).all frame028test05=true := by
  decide +kernel

private theorem frame028scope05 : fits05.all frame028test05=true := by
  have h32 := stitchAt 32 3 frame028scope05_s032 frame028scope05_end
  have h28 := stitchAt 28 4 frame028scope05_s028 h32
  have h24 := stitchAt 24 4 frame028scope05_s024 h28
  have h20 := stitchAt 20 4 frame028scope05_s020 h24
  have h16 := stitchAt 16 4 frame028scope05_s016 h20
  have h12 := stitchAt 12 4 frame028scope05_s012 h16
  have h8 := stitchAt 8 4 frame028scope05_s008 h12
  have h4 := stitchAt 4 4 frame028scope05_s004 h8
  have h0 := stitchAt 0 4 frame028scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch05 : batch05.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope05

private abbrev frame028test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch06.stop,F)

private theorem frame028scope06_s000 : ((fits06.drop 0).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s004 : ((fits06.drop 4).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s008 : ((fits06.drop 8).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s012 : ((fits06.drop 12).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s016 : ((fits06.drop 16).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s020 : ((fits06.drop 20).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s024 : ((fits06.drop 24).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s028 : ((fits06.drop 28).take 4).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_s032 : ((fits06.drop 32).take 3).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06_end : (fits06.drop 35).all frame028test06=true := by
  decide +kernel

private theorem frame028scope06 : fits06.all frame028test06=true := by
  have h32 := stitchAt 32 3 frame028scope06_s032 frame028scope06_end
  have h28 := stitchAt 28 4 frame028scope06_s028 h32
  have h24 := stitchAt 24 4 frame028scope06_s024 h28
  have h20 := stitchAt 20 4 frame028scope06_s020 h24
  have h16 := stitchAt 16 4 frame028scope06_s016 h20
  have h12 := stitchAt 12 4 frame028scope06_s012 h16
  have h8 := stitchAt 8 4 frame028scope06_s008 h12
  have h4 := stitchAt 4 4 frame028scope06_s004 h8
  have h0 := stitchAt 0 4 frame028scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch06 : batch06.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope06

private abbrev frame028test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame59 (fun z => List.lookup (guideCode z) guide028)
    (batch07.stop,F)

private theorem frame028scope07_s000 : ((fits07.drop 0).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s004 : ((fits07.drop 4).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s008 : ((fits07.drop 8).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s012 : ((fits07.drop 12).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s016 : ((fits07.drop 16).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s020 : ((fits07.drop 20).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s024 : ((fits07.drop 24).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s028 : ((fits07.drop 28).take 4).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_s032 : ((fits07.drop 32).take 3).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07_end : (fits07.drop 35).all frame028test07=true := by
  decide +kernel

private theorem frame028scope07 : fits07.all frame028test07=true := by
  have h32 := stitchAt 32 3 frame028scope07_s032 frame028scope07_end
  have h28 := stitchAt 28 4 frame028scope07_s028 h32
  have h24 := stitchAt 24 4 frame028scope07_s024 h28
  have h20 := stitchAt 20 4 frame028scope07_s020 h24
  have h16 := stitchAt 16 4 frame028scope07_s016 h20
  have h12 := stitchAt 12 4 frame028scope07_s012 h16
  have h8 := stitchAt 8 4 frame028scope07_s008 h12
  have h4 := stitchAt 4 4 frame028scope07_s004 h8
  have h0 := stitchAt 0 4 frame028scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame028batch07 : batch07.pickTest original frame59=true :=
  FitBatch.pickTest_of_scoped scoped028 frame028scope07

private theorem frameBatches028 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame59)=true := by
  simp only [List.all_cons,List.all_nil,frame028batch00,frame028batch01,frame028batch02,frame028batch03,frame028batch04,frame028batch05,frame028batch06,frame028batch07,Bool.and_self]

theorem frameOK028 : frameRankTest original useStop frame59=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches028

theorem stripOK029 : stripTest frame60=true := by decide +kernel

theorem spanOK029 : checkChain 1664 1648 [frame60.span]=true := by decide +kernel

private theorem guideAt029 : List.lookup frame60.span.1 guideTable=some guide029 := by
  decide +kernel

private theorem scoped029 : original.guide frame60.span.1 =
    (fun z => List.lookup (guideCode z) guide029) := by
  funext z
  change (List.lookup frame60.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide029
  simp only [guideAt029,Option.bind_some]

private abbrev frame029test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch00.stop,F)

private theorem frame029scope00_s000 : ((fits00.drop 0).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s004 : ((fits00.drop 4).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s008 : ((fits00.drop 8).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s012 : ((fits00.drop 12).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s016 : ((fits00.drop 16).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s020 : ((fits00.drop 20).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s024 : ((fits00.drop 24).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s028 : ((fits00.drop 28).take 4).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_s032 : ((fits00.drop 32).take 3).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00_end : (fits00.drop 35).all frame029test00=true := by
  decide +kernel

private theorem frame029scope00 : fits00.all frame029test00=true := by
  have h32 := stitchAt 32 3 frame029scope00_s032 frame029scope00_end
  have h28 := stitchAt 28 4 frame029scope00_s028 h32
  have h24 := stitchAt 24 4 frame029scope00_s024 h28
  have h20 := stitchAt 20 4 frame029scope00_s020 h24
  have h16 := stitchAt 16 4 frame029scope00_s016 h20
  have h12 := stitchAt 12 4 frame029scope00_s012 h16
  have h8 := stitchAt 8 4 frame029scope00_s008 h12
  have h4 := stitchAt 4 4 frame029scope00_s004 h8
  have h0 := stitchAt 0 4 frame029scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch00 : batch00.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope00

private abbrev frame029test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch01.stop,F)

private theorem frame029scope01_s000 : ((fits01.drop 0).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s004 : ((fits01.drop 4).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s008 : ((fits01.drop 8).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s012 : ((fits01.drop 12).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s016 : ((fits01.drop 16).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s020 : ((fits01.drop 20).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s024 : ((fits01.drop 24).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s028 : ((fits01.drop 28).take 4).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_s032 : ((fits01.drop 32).take 3).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01_end : (fits01.drop 35).all frame029test01=true := by
  decide +kernel

private theorem frame029scope01 : fits01.all frame029test01=true := by
  have h32 := stitchAt 32 3 frame029scope01_s032 frame029scope01_end
  have h28 := stitchAt 28 4 frame029scope01_s028 h32
  have h24 := stitchAt 24 4 frame029scope01_s024 h28
  have h20 := stitchAt 20 4 frame029scope01_s020 h24
  have h16 := stitchAt 16 4 frame029scope01_s016 h20
  have h12 := stitchAt 12 4 frame029scope01_s012 h16
  have h8 := stitchAt 8 4 frame029scope01_s008 h12
  have h4 := stitchAt 4 4 frame029scope01_s004 h8
  have h0 := stitchAt 0 4 frame029scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch01 : batch01.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope01

private abbrev frame029test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch02.stop,F)

private theorem frame029scope02_s000 : ((fits02.drop 0).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s004 : ((fits02.drop 4).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s008 : ((fits02.drop 8).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s012 : ((fits02.drop 12).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s016 : ((fits02.drop 16).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s020 : ((fits02.drop 20).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s024 : ((fits02.drop 24).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s028 : ((fits02.drop 28).take 4).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_s032 : ((fits02.drop 32).take 3).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02_end : (fits02.drop 35).all frame029test02=true := by
  decide +kernel

private theorem frame029scope02 : fits02.all frame029test02=true := by
  have h32 := stitchAt 32 3 frame029scope02_s032 frame029scope02_end
  have h28 := stitchAt 28 4 frame029scope02_s028 h32
  have h24 := stitchAt 24 4 frame029scope02_s024 h28
  have h20 := stitchAt 20 4 frame029scope02_s020 h24
  have h16 := stitchAt 16 4 frame029scope02_s016 h20
  have h12 := stitchAt 12 4 frame029scope02_s012 h16
  have h8 := stitchAt 8 4 frame029scope02_s008 h12
  have h4 := stitchAt 4 4 frame029scope02_s004 h8
  have h0 := stitchAt 0 4 frame029scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch02 : batch02.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope02

private abbrev frame029test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch03.stop,F)

private theorem frame029scope03_s000 : ((fits03.drop 0).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s004 : ((fits03.drop 4).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s008 : ((fits03.drop 8).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s012 : ((fits03.drop 12).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s016 : ((fits03.drop 16).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s020 : ((fits03.drop 20).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s024 : ((fits03.drop 24).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s028 : ((fits03.drop 28).take 4).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_s032 : ((fits03.drop 32).take 3).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03_end : (fits03.drop 35).all frame029test03=true := by
  decide +kernel

private theorem frame029scope03 : fits03.all frame029test03=true := by
  have h32 := stitchAt 32 3 frame029scope03_s032 frame029scope03_end
  have h28 := stitchAt 28 4 frame029scope03_s028 h32
  have h24 := stitchAt 24 4 frame029scope03_s024 h28
  have h20 := stitchAt 20 4 frame029scope03_s020 h24
  have h16 := stitchAt 16 4 frame029scope03_s016 h20
  have h12 := stitchAt 12 4 frame029scope03_s012 h16
  have h8 := stitchAt 8 4 frame029scope03_s008 h12
  have h4 := stitchAt 4 4 frame029scope03_s004 h8
  have h0 := stitchAt 0 4 frame029scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch03 : batch03.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope03

private abbrev frame029test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch04.stop,F)

private theorem frame029scope04_s000 : ((fits04.drop 0).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s004 : ((fits04.drop 4).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s008 : ((fits04.drop 8).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s012 : ((fits04.drop 12).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s016 : ((fits04.drop 16).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s020 : ((fits04.drop 20).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s024 : ((fits04.drop 24).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s028 : ((fits04.drop 28).take 4).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_s032 : ((fits04.drop 32).take 3).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04_end : (fits04.drop 35).all frame029test04=true := by
  decide +kernel

private theorem frame029scope04 : fits04.all frame029test04=true := by
  have h32 := stitchAt 32 3 frame029scope04_s032 frame029scope04_end
  have h28 := stitchAt 28 4 frame029scope04_s028 h32
  have h24 := stitchAt 24 4 frame029scope04_s024 h28
  have h20 := stitchAt 20 4 frame029scope04_s020 h24
  have h16 := stitchAt 16 4 frame029scope04_s016 h20
  have h12 := stitchAt 12 4 frame029scope04_s012 h16
  have h8 := stitchAt 8 4 frame029scope04_s008 h12
  have h4 := stitchAt 4 4 frame029scope04_s004 h8
  have h0 := stitchAt 0 4 frame029scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch04 : batch04.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope04

private abbrev frame029test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch05.stop,F)

private theorem frame029scope05_s000 : ((fits05.drop 0).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s004 : ((fits05.drop 4).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s008 : ((fits05.drop 8).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s012 : ((fits05.drop 12).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s016 : ((fits05.drop 16).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s020 : ((fits05.drop 20).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s024 : ((fits05.drop 24).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s028 : ((fits05.drop 28).take 4).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_s032 : ((fits05.drop 32).take 3).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05_end : (fits05.drop 35).all frame029test05=true := by
  decide +kernel

private theorem frame029scope05 : fits05.all frame029test05=true := by
  have h32 := stitchAt 32 3 frame029scope05_s032 frame029scope05_end
  have h28 := stitchAt 28 4 frame029scope05_s028 h32
  have h24 := stitchAt 24 4 frame029scope05_s024 h28
  have h20 := stitchAt 20 4 frame029scope05_s020 h24
  have h16 := stitchAt 16 4 frame029scope05_s016 h20
  have h12 := stitchAt 12 4 frame029scope05_s012 h16
  have h8 := stitchAt 8 4 frame029scope05_s008 h12
  have h4 := stitchAt 4 4 frame029scope05_s004 h8
  have h0 := stitchAt 0 4 frame029scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch05 : batch05.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope05

private abbrev frame029test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch06.stop,F)

private theorem frame029scope06_s000 : ((fits06.drop 0).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s004 : ((fits06.drop 4).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s008 : ((fits06.drop 8).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s012 : ((fits06.drop 12).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s016 : ((fits06.drop 16).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s020 : ((fits06.drop 20).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s024 : ((fits06.drop 24).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s028 : ((fits06.drop 28).take 4).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_s032 : ((fits06.drop 32).take 3).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06_end : (fits06.drop 35).all frame029test06=true := by
  decide +kernel

private theorem frame029scope06 : fits06.all frame029test06=true := by
  have h32 := stitchAt 32 3 frame029scope06_s032 frame029scope06_end
  have h28 := stitchAt 28 4 frame029scope06_s028 h32
  have h24 := stitchAt 24 4 frame029scope06_s024 h28
  have h20 := stitchAt 20 4 frame029scope06_s020 h24
  have h16 := stitchAt 16 4 frame029scope06_s016 h20
  have h12 := stitchAt 12 4 frame029scope06_s012 h16
  have h8 := stitchAt 8 4 frame029scope06_s008 h12
  have h4 := stitchAt 4 4 frame029scope06_s004 h8
  have h0 := stitchAt 0 4 frame029scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch06 : batch06.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope06

private abbrev frame029test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame60 (fun z => List.lookup (guideCode z) guide029)
    (batch07.stop,F)

private theorem frame029scope07_s000 : ((fits07.drop 0).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s004 : ((fits07.drop 4).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s008 : ((fits07.drop 8).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s012 : ((fits07.drop 12).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s016 : ((fits07.drop 16).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s020 : ((fits07.drop 20).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s024 : ((fits07.drop 24).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s028 : ((fits07.drop 28).take 4).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_s032 : ((fits07.drop 32).take 3).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07_end : (fits07.drop 35).all frame029test07=true := by
  decide +kernel

private theorem frame029scope07 : fits07.all frame029test07=true := by
  have h32 := stitchAt 32 3 frame029scope07_s032 frame029scope07_end
  have h28 := stitchAt 28 4 frame029scope07_s028 h32
  have h24 := stitchAt 24 4 frame029scope07_s024 h28
  have h20 := stitchAt 20 4 frame029scope07_s020 h24
  have h16 := stitchAt 16 4 frame029scope07_s016 h20
  have h12 := stitchAt 12 4 frame029scope07_s012 h16
  have h8 := stitchAt 8 4 frame029scope07_s008 h12
  have h4 := stitchAt 4 4 frame029scope07_s004 h8
  have h0 := stitchAt 0 4 frame029scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame029batch07 : batch07.pickTest original frame60=true :=
  FitBatch.pickTest_of_scoped scoped029 frame029scope07

private theorem frameBatches029 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame60)=true := by
  simp only [List.all_cons,List.all_nil,frame029batch00,frame029batch01,frame029batch02,frame029batch03,frame029batch04,frame029batch05,frame029batch06,frame029batch07,Bool.and_self]

theorem frameOK029 : frameRankTest original useStop frame60=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches029


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
