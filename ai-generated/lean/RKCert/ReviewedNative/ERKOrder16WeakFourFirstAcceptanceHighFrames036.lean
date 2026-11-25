module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK072 : stripTest frame148=true := by decide +kernel

theorem spanOK072 : checkChain 1816 1808 [frame148.span]=true := by decide +kernel

private theorem guideAt072 : List.lookup frame148.span.1 guideTable=some guide072 := by
  decide +kernel

private theorem scoped072 : original.guide frame148.span.1 =
    (fun z => List.lookup (guideCode z) guide072) := by
  funext z
  change (List.lookup frame148.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide072
  simp only [guideAt072,Option.bind_some]

private abbrev frame072test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch00.stop,F)

private theorem frame072scope00_s000 : ((fits00.drop 0).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s004 : ((fits00.drop 4).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s008 : ((fits00.drop 8).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s012 : ((fits00.drop 12).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s016 : ((fits00.drop 16).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s020 : ((fits00.drop 20).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s024 : ((fits00.drop 24).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s028 : ((fits00.drop 28).take 4).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_s032 : ((fits00.drop 32).take 3).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00_end : (fits00.drop 35).all frame072test00=true := by
  decide +kernel

private theorem frame072scope00 : fits00.all frame072test00=true := by
  have h32 := stitchAt 32 3 frame072scope00_s032 frame072scope00_end
  have h28 := stitchAt 28 4 frame072scope00_s028 h32
  have h24 := stitchAt 24 4 frame072scope00_s024 h28
  have h20 := stitchAt 20 4 frame072scope00_s020 h24
  have h16 := stitchAt 16 4 frame072scope00_s016 h20
  have h12 := stitchAt 12 4 frame072scope00_s012 h16
  have h8 := stitchAt 8 4 frame072scope00_s008 h12
  have h4 := stitchAt 4 4 frame072scope00_s004 h8
  have h0 := stitchAt 0 4 frame072scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch00 : batch00.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope00

private abbrev frame072test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch01.stop,F)

private theorem frame072scope01_s000 : ((fits01.drop 0).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s004 : ((fits01.drop 4).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s008 : ((fits01.drop 8).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s012 : ((fits01.drop 12).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s016 : ((fits01.drop 16).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s020 : ((fits01.drop 20).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s024 : ((fits01.drop 24).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s028 : ((fits01.drop 28).take 4).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_s032 : ((fits01.drop 32).take 3).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01_end : (fits01.drop 35).all frame072test01=true := by
  decide +kernel

private theorem frame072scope01 : fits01.all frame072test01=true := by
  have h32 := stitchAt 32 3 frame072scope01_s032 frame072scope01_end
  have h28 := stitchAt 28 4 frame072scope01_s028 h32
  have h24 := stitchAt 24 4 frame072scope01_s024 h28
  have h20 := stitchAt 20 4 frame072scope01_s020 h24
  have h16 := stitchAt 16 4 frame072scope01_s016 h20
  have h12 := stitchAt 12 4 frame072scope01_s012 h16
  have h8 := stitchAt 8 4 frame072scope01_s008 h12
  have h4 := stitchAt 4 4 frame072scope01_s004 h8
  have h0 := stitchAt 0 4 frame072scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch01 : batch01.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope01

private abbrev frame072test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch02.stop,F)

private theorem frame072scope02_s000 : ((fits02.drop 0).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s004 : ((fits02.drop 4).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s008 : ((fits02.drop 8).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s012 : ((fits02.drop 12).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s016 : ((fits02.drop 16).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s020 : ((fits02.drop 20).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s024 : ((fits02.drop 24).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s028 : ((fits02.drop 28).take 4).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_s032 : ((fits02.drop 32).take 3).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02_end : (fits02.drop 35).all frame072test02=true := by
  decide +kernel

private theorem frame072scope02 : fits02.all frame072test02=true := by
  have h32 := stitchAt 32 3 frame072scope02_s032 frame072scope02_end
  have h28 := stitchAt 28 4 frame072scope02_s028 h32
  have h24 := stitchAt 24 4 frame072scope02_s024 h28
  have h20 := stitchAt 20 4 frame072scope02_s020 h24
  have h16 := stitchAt 16 4 frame072scope02_s016 h20
  have h12 := stitchAt 12 4 frame072scope02_s012 h16
  have h8 := stitchAt 8 4 frame072scope02_s008 h12
  have h4 := stitchAt 4 4 frame072scope02_s004 h8
  have h0 := stitchAt 0 4 frame072scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch02 : batch02.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope02

private abbrev frame072test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch03.stop,F)

private theorem frame072scope03_s000 : ((fits03.drop 0).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s004 : ((fits03.drop 4).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s008 : ((fits03.drop 8).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s012 : ((fits03.drop 12).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s016 : ((fits03.drop 16).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s020 : ((fits03.drop 20).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s024 : ((fits03.drop 24).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s028 : ((fits03.drop 28).take 4).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_s032 : ((fits03.drop 32).take 3).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03_end : (fits03.drop 35).all frame072test03=true := by
  decide +kernel

private theorem frame072scope03 : fits03.all frame072test03=true := by
  have h32 := stitchAt 32 3 frame072scope03_s032 frame072scope03_end
  have h28 := stitchAt 28 4 frame072scope03_s028 h32
  have h24 := stitchAt 24 4 frame072scope03_s024 h28
  have h20 := stitchAt 20 4 frame072scope03_s020 h24
  have h16 := stitchAt 16 4 frame072scope03_s016 h20
  have h12 := stitchAt 12 4 frame072scope03_s012 h16
  have h8 := stitchAt 8 4 frame072scope03_s008 h12
  have h4 := stitchAt 4 4 frame072scope03_s004 h8
  have h0 := stitchAt 0 4 frame072scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch03 : batch03.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope03

private abbrev frame072test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch04.stop,F)

private theorem frame072scope04_s000 : ((fits04.drop 0).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s004 : ((fits04.drop 4).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s008 : ((fits04.drop 8).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s012 : ((fits04.drop 12).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s016 : ((fits04.drop 16).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s020 : ((fits04.drop 20).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s024 : ((fits04.drop 24).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s028 : ((fits04.drop 28).take 4).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_s032 : ((fits04.drop 32).take 3).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04_end : (fits04.drop 35).all frame072test04=true := by
  decide +kernel

private theorem frame072scope04 : fits04.all frame072test04=true := by
  have h32 := stitchAt 32 3 frame072scope04_s032 frame072scope04_end
  have h28 := stitchAt 28 4 frame072scope04_s028 h32
  have h24 := stitchAt 24 4 frame072scope04_s024 h28
  have h20 := stitchAt 20 4 frame072scope04_s020 h24
  have h16 := stitchAt 16 4 frame072scope04_s016 h20
  have h12 := stitchAt 12 4 frame072scope04_s012 h16
  have h8 := stitchAt 8 4 frame072scope04_s008 h12
  have h4 := stitchAt 4 4 frame072scope04_s004 h8
  have h0 := stitchAt 0 4 frame072scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch04 : batch04.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope04

private abbrev frame072test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch05.stop,F)

private theorem frame072scope05_s000 : ((fits05.drop 0).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s004 : ((fits05.drop 4).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s008 : ((fits05.drop 8).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s012 : ((fits05.drop 12).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s016 : ((fits05.drop 16).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s020 : ((fits05.drop 20).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s024 : ((fits05.drop 24).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s028 : ((fits05.drop 28).take 4).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_s032 : ((fits05.drop 32).take 3).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05_end : (fits05.drop 35).all frame072test05=true := by
  decide +kernel

private theorem frame072scope05 : fits05.all frame072test05=true := by
  have h32 := stitchAt 32 3 frame072scope05_s032 frame072scope05_end
  have h28 := stitchAt 28 4 frame072scope05_s028 h32
  have h24 := stitchAt 24 4 frame072scope05_s024 h28
  have h20 := stitchAt 20 4 frame072scope05_s020 h24
  have h16 := stitchAt 16 4 frame072scope05_s016 h20
  have h12 := stitchAt 12 4 frame072scope05_s012 h16
  have h8 := stitchAt 8 4 frame072scope05_s008 h12
  have h4 := stitchAt 4 4 frame072scope05_s004 h8
  have h0 := stitchAt 0 4 frame072scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch05 : batch05.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope05

private abbrev frame072test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch06.stop,F)

private theorem frame072scope06_s000 : ((fits06.drop 0).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s004 : ((fits06.drop 4).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s008 : ((fits06.drop 8).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s012 : ((fits06.drop 12).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s016 : ((fits06.drop 16).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s020 : ((fits06.drop 20).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s024 : ((fits06.drop 24).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s028 : ((fits06.drop 28).take 4).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_s032 : ((fits06.drop 32).take 3).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06_end : (fits06.drop 35).all frame072test06=true := by
  decide +kernel

private theorem frame072scope06 : fits06.all frame072test06=true := by
  have h32 := stitchAt 32 3 frame072scope06_s032 frame072scope06_end
  have h28 := stitchAt 28 4 frame072scope06_s028 h32
  have h24 := stitchAt 24 4 frame072scope06_s024 h28
  have h20 := stitchAt 20 4 frame072scope06_s020 h24
  have h16 := stitchAt 16 4 frame072scope06_s016 h20
  have h12 := stitchAt 12 4 frame072scope06_s012 h16
  have h8 := stitchAt 8 4 frame072scope06_s008 h12
  have h4 := stitchAt 4 4 frame072scope06_s004 h8
  have h0 := stitchAt 0 4 frame072scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch06 : batch06.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope06

private abbrev frame072test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame148 (fun z => List.lookup (guideCode z) guide072)
    (batch07.stop,F)

private theorem frame072scope07_s000 : ((fits07.drop 0).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s004 : ((fits07.drop 4).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s008 : ((fits07.drop 8).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s012 : ((fits07.drop 12).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s016 : ((fits07.drop 16).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s020 : ((fits07.drop 20).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s024 : ((fits07.drop 24).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s028 : ((fits07.drop 28).take 4).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_s032 : ((fits07.drop 32).take 3).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07_end : (fits07.drop 35).all frame072test07=true := by
  decide +kernel

private theorem frame072scope07 : fits07.all frame072test07=true := by
  have h32 := stitchAt 32 3 frame072scope07_s032 frame072scope07_end
  have h28 := stitchAt 28 4 frame072scope07_s028 h32
  have h24 := stitchAt 24 4 frame072scope07_s024 h28
  have h20 := stitchAt 20 4 frame072scope07_s020 h24
  have h16 := stitchAt 16 4 frame072scope07_s016 h20
  have h12 := stitchAt 12 4 frame072scope07_s012 h16
  have h8 := stitchAt 8 4 frame072scope07_s008 h12
  have h4 := stitchAt 4 4 frame072scope07_s004 h8
  have h0 := stitchAt 0 4 frame072scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame072batch07 : batch07.pickTest original frame148=true :=
  FitBatch.pickTest_of_scoped scoped072 frame072scope07

private theorem frameBatches072 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame148)=true := by
  simp only [List.all_cons,List.all_nil,frame072batch00,frame072batch01,frame072batch02,frame072batch03,frame072batch04,frame072batch05,frame072batch06,frame072batch07,Bool.and_self]

theorem frameOK072 : frameRankTest original useStop frame148=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches072

theorem stripOK073 : stripTest frame149=true := by decide +kernel

theorem spanOK073 : checkChain 1824 1816 [frame149.span]=true := by decide +kernel

private theorem guideAt073 : List.lookup frame149.span.1 guideTable=some guide073 := by
  decide +kernel

private theorem scoped073 : original.guide frame149.span.1 =
    (fun z => List.lookup (guideCode z) guide073) := by
  funext z
  change (List.lookup frame149.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide073
  simp only [guideAt073,Option.bind_some]

private abbrev frame073test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch00.stop,F)

private theorem frame073scope00_s000 : ((fits00.drop 0).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s004 : ((fits00.drop 4).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s008 : ((fits00.drop 8).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s012 : ((fits00.drop 12).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s016 : ((fits00.drop 16).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s020 : ((fits00.drop 20).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s024 : ((fits00.drop 24).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s028 : ((fits00.drop 28).take 4).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_s032 : ((fits00.drop 32).take 3).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00_end : (fits00.drop 35).all frame073test00=true := by
  decide +kernel

private theorem frame073scope00 : fits00.all frame073test00=true := by
  have h32 := stitchAt 32 3 frame073scope00_s032 frame073scope00_end
  have h28 := stitchAt 28 4 frame073scope00_s028 h32
  have h24 := stitchAt 24 4 frame073scope00_s024 h28
  have h20 := stitchAt 20 4 frame073scope00_s020 h24
  have h16 := stitchAt 16 4 frame073scope00_s016 h20
  have h12 := stitchAt 12 4 frame073scope00_s012 h16
  have h8 := stitchAt 8 4 frame073scope00_s008 h12
  have h4 := stitchAt 4 4 frame073scope00_s004 h8
  have h0 := stitchAt 0 4 frame073scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch00 : batch00.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope00

private abbrev frame073test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch01.stop,F)

private theorem frame073scope01_s000 : ((fits01.drop 0).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s004 : ((fits01.drop 4).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s008 : ((fits01.drop 8).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s012 : ((fits01.drop 12).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s016 : ((fits01.drop 16).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s020 : ((fits01.drop 20).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s024 : ((fits01.drop 24).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s028 : ((fits01.drop 28).take 4).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_s032 : ((fits01.drop 32).take 3).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01_end : (fits01.drop 35).all frame073test01=true := by
  decide +kernel

private theorem frame073scope01 : fits01.all frame073test01=true := by
  have h32 := stitchAt 32 3 frame073scope01_s032 frame073scope01_end
  have h28 := stitchAt 28 4 frame073scope01_s028 h32
  have h24 := stitchAt 24 4 frame073scope01_s024 h28
  have h20 := stitchAt 20 4 frame073scope01_s020 h24
  have h16 := stitchAt 16 4 frame073scope01_s016 h20
  have h12 := stitchAt 12 4 frame073scope01_s012 h16
  have h8 := stitchAt 8 4 frame073scope01_s008 h12
  have h4 := stitchAt 4 4 frame073scope01_s004 h8
  have h0 := stitchAt 0 4 frame073scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch01 : batch01.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope01

private abbrev frame073test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch02.stop,F)

private theorem frame073scope02_s000 : ((fits02.drop 0).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s004 : ((fits02.drop 4).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s008 : ((fits02.drop 8).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s012 : ((fits02.drop 12).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s016 : ((fits02.drop 16).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s020 : ((fits02.drop 20).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s024 : ((fits02.drop 24).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s028 : ((fits02.drop 28).take 4).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_s032 : ((fits02.drop 32).take 3).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02_end : (fits02.drop 35).all frame073test02=true := by
  decide +kernel

private theorem frame073scope02 : fits02.all frame073test02=true := by
  have h32 := stitchAt 32 3 frame073scope02_s032 frame073scope02_end
  have h28 := stitchAt 28 4 frame073scope02_s028 h32
  have h24 := stitchAt 24 4 frame073scope02_s024 h28
  have h20 := stitchAt 20 4 frame073scope02_s020 h24
  have h16 := stitchAt 16 4 frame073scope02_s016 h20
  have h12 := stitchAt 12 4 frame073scope02_s012 h16
  have h8 := stitchAt 8 4 frame073scope02_s008 h12
  have h4 := stitchAt 4 4 frame073scope02_s004 h8
  have h0 := stitchAt 0 4 frame073scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch02 : batch02.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope02

private abbrev frame073test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch03.stop,F)

private theorem frame073scope03_s000 : ((fits03.drop 0).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s004 : ((fits03.drop 4).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s008 : ((fits03.drop 8).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s012 : ((fits03.drop 12).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s016 : ((fits03.drop 16).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s020 : ((fits03.drop 20).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s024 : ((fits03.drop 24).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s028 : ((fits03.drop 28).take 4).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_s032 : ((fits03.drop 32).take 3).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03_end : (fits03.drop 35).all frame073test03=true := by
  decide +kernel

private theorem frame073scope03 : fits03.all frame073test03=true := by
  have h32 := stitchAt 32 3 frame073scope03_s032 frame073scope03_end
  have h28 := stitchAt 28 4 frame073scope03_s028 h32
  have h24 := stitchAt 24 4 frame073scope03_s024 h28
  have h20 := stitchAt 20 4 frame073scope03_s020 h24
  have h16 := stitchAt 16 4 frame073scope03_s016 h20
  have h12 := stitchAt 12 4 frame073scope03_s012 h16
  have h8 := stitchAt 8 4 frame073scope03_s008 h12
  have h4 := stitchAt 4 4 frame073scope03_s004 h8
  have h0 := stitchAt 0 4 frame073scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch03 : batch03.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope03

private abbrev frame073test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch04.stop,F)

private theorem frame073scope04_s000 : ((fits04.drop 0).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s004 : ((fits04.drop 4).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s008 : ((fits04.drop 8).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s012 : ((fits04.drop 12).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s016 : ((fits04.drop 16).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s020 : ((fits04.drop 20).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s024 : ((fits04.drop 24).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s028 : ((fits04.drop 28).take 4).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_s032 : ((fits04.drop 32).take 3).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04_end : (fits04.drop 35).all frame073test04=true := by
  decide +kernel

private theorem frame073scope04 : fits04.all frame073test04=true := by
  have h32 := stitchAt 32 3 frame073scope04_s032 frame073scope04_end
  have h28 := stitchAt 28 4 frame073scope04_s028 h32
  have h24 := stitchAt 24 4 frame073scope04_s024 h28
  have h20 := stitchAt 20 4 frame073scope04_s020 h24
  have h16 := stitchAt 16 4 frame073scope04_s016 h20
  have h12 := stitchAt 12 4 frame073scope04_s012 h16
  have h8 := stitchAt 8 4 frame073scope04_s008 h12
  have h4 := stitchAt 4 4 frame073scope04_s004 h8
  have h0 := stitchAt 0 4 frame073scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch04 : batch04.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope04

private abbrev frame073test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch05.stop,F)

private theorem frame073scope05_s000 : ((fits05.drop 0).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s004 : ((fits05.drop 4).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s008 : ((fits05.drop 8).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s012 : ((fits05.drop 12).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s016 : ((fits05.drop 16).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s020 : ((fits05.drop 20).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s024 : ((fits05.drop 24).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s028 : ((fits05.drop 28).take 4).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_s032 : ((fits05.drop 32).take 3).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05_end : (fits05.drop 35).all frame073test05=true := by
  decide +kernel

private theorem frame073scope05 : fits05.all frame073test05=true := by
  have h32 := stitchAt 32 3 frame073scope05_s032 frame073scope05_end
  have h28 := stitchAt 28 4 frame073scope05_s028 h32
  have h24 := stitchAt 24 4 frame073scope05_s024 h28
  have h20 := stitchAt 20 4 frame073scope05_s020 h24
  have h16 := stitchAt 16 4 frame073scope05_s016 h20
  have h12 := stitchAt 12 4 frame073scope05_s012 h16
  have h8 := stitchAt 8 4 frame073scope05_s008 h12
  have h4 := stitchAt 4 4 frame073scope05_s004 h8
  have h0 := stitchAt 0 4 frame073scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch05 : batch05.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope05

private abbrev frame073test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch06.stop,F)

private theorem frame073scope06_s000 : ((fits06.drop 0).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s004 : ((fits06.drop 4).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s008 : ((fits06.drop 8).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s012 : ((fits06.drop 12).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s016 : ((fits06.drop 16).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s020 : ((fits06.drop 20).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s024 : ((fits06.drop 24).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s028 : ((fits06.drop 28).take 4).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_s032 : ((fits06.drop 32).take 3).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06_end : (fits06.drop 35).all frame073test06=true := by
  decide +kernel

private theorem frame073scope06 : fits06.all frame073test06=true := by
  have h32 := stitchAt 32 3 frame073scope06_s032 frame073scope06_end
  have h28 := stitchAt 28 4 frame073scope06_s028 h32
  have h24 := stitchAt 24 4 frame073scope06_s024 h28
  have h20 := stitchAt 20 4 frame073scope06_s020 h24
  have h16 := stitchAt 16 4 frame073scope06_s016 h20
  have h12 := stitchAt 12 4 frame073scope06_s012 h16
  have h8 := stitchAt 8 4 frame073scope06_s008 h12
  have h4 := stitchAt 4 4 frame073scope06_s004 h8
  have h0 := stitchAt 0 4 frame073scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch06 : batch06.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope06

private abbrev frame073test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame149 (fun z => List.lookup (guideCode z) guide073)
    (batch07.stop,F)

private theorem frame073scope07_s000 : ((fits07.drop 0).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s004 : ((fits07.drop 4).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s008 : ((fits07.drop 8).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s012 : ((fits07.drop 12).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s016 : ((fits07.drop 16).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s020 : ((fits07.drop 20).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s024 : ((fits07.drop 24).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s028 : ((fits07.drop 28).take 4).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_s032 : ((fits07.drop 32).take 3).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07_end : (fits07.drop 35).all frame073test07=true := by
  decide +kernel

private theorem frame073scope07 : fits07.all frame073test07=true := by
  have h32 := stitchAt 32 3 frame073scope07_s032 frame073scope07_end
  have h28 := stitchAt 28 4 frame073scope07_s028 h32
  have h24 := stitchAt 24 4 frame073scope07_s024 h28
  have h20 := stitchAt 20 4 frame073scope07_s020 h24
  have h16 := stitchAt 16 4 frame073scope07_s016 h20
  have h12 := stitchAt 12 4 frame073scope07_s012 h16
  have h8 := stitchAt 8 4 frame073scope07_s008 h12
  have h4 := stitchAt 4 4 frame073scope07_s004 h8
  have h0 := stitchAt 0 4 frame073scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame073batch07 : batch07.pickTest original frame149=true :=
  FitBatch.pickTest_of_scoped scoped073 frame073scope07

private theorem frameBatches073 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame149)=true := by
  simp only [List.all_cons,List.all_nil,frame073batch00,frame073batch01,frame073batch02,frame073batch03,frame073batch04,frame073batch05,frame073batch06,frame073batch07,Bool.and_self]

theorem frameOK073 : frameRankTest original useStop frame149=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches073


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
