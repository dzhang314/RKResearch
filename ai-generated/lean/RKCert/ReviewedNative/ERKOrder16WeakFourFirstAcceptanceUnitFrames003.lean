module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksUnit

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
open RKCert.ReviewedNative.WeakFourFirstOnly.DataUnit
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK006 : stripTest frame14=true := by decide +kernel

theorem spanOK006 : checkChain 960 896 [frame14.span]=true := by decide +kernel

private theorem guideAt006 : List.lookup frame14.span.1 guideTable=some guide006 := by
  decide +kernel

private theorem scoped006 : original.guide frame14.span.1 =
    (fun z => List.lookup (guideCode z) guide006) := by
  funext z
  change (List.lookup frame14.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide006
  simp only [guideAt006,Option.bind_some]

private abbrev frame006test00 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch00.stop,F)

private theorem frame006scope00_s000 : ((fits00.drop 0).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s004 : ((fits00.drop 4).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s008 : ((fits00.drop 8).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s012 : ((fits00.drop 12).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s016 : ((fits00.drop 16).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s020 : ((fits00.drop 20).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s024 : ((fits00.drop 24).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s028 : ((fits00.drop 28).take 4).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_s032 : ((fits00.drop 32).take 3).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00_end : (fits00.drop 35).all frame006test00=true := by
  decide +kernel

private theorem frame006scope00 : fits00.all frame006test00=true := by
  have h32 := stitchAt 32 3 frame006scope00_s032 frame006scope00_end
  have h28 := stitchAt 28 4 frame006scope00_s028 h32
  have h24 := stitchAt 24 4 frame006scope00_s024 h28
  have h20 := stitchAt 20 4 frame006scope00_s020 h24
  have h16 := stitchAt 16 4 frame006scope00_s016 h20
  have h12 := stitchAt 12 4 frame006scope00_s012 h16
  have h8 := stitchAt 8 4 frame006scope00_s008 h12
  have h4 := stitchAt 4 4 frame006scope00_s004 h8
  have h0 := stitchAt 0 4 frame006scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch00 : batch00.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope00

private abbrev frame006test01 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch01.stop,F)

private theorem frame006scope01_s000 : ((fits01.drop 0).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s004 : ((fits01.drop 4).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s008 : ((fits01.drop 8).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s012 : ((fits01.drop 12).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s016 : ((fits01.drop 16).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s020 : ((fits01.drop 20).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s024 : ((fits01.drop 24).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s028 : ((fits01.drop 28).take 4).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_s032 : ((fits01.drop 32).take 3).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01_end : (fits01.drop 35).all frame006test01=true := by
  decide +kernel

private theorem frame006scope01 : fits01.all frame006test01=true := by
  have h32 := stitchAt 32 3 frame006scope01_s032 frame006scope01_end
  have h28 := stitchAt 28 4 frame006scope01_s028 h32
  have h24 := stitchAt 24 4 frame006scope01_s024 h28
  have h20 := stitchAt 20 4 frame006scope01_s020 h24
  have h16 := stitchAt 16 4 frame006scope01_s016 h20
  have h12 := stitchAt 12 4 frame006scope01_s012 h16
  have h8 := stitchAt 8 4 frame006scope01_s008 h12
  have h4 := stitchAt 4 4 frame006scope01_s004 h8
  have h0 := stitchAt 0 4 frame006scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch01 : batch01.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope01

private abbrev frame006test02 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch02.stop,F)

private theorem frame006scope02_s000 : ((fits02.drop 0).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s004 : ((fits02.drop 4).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s008 : ((fits02.drop 8).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s012 : ((fits02.drop 12).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s016 : ((fits02.drop 16).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s020 : ((fits02.drop 20).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s024 : ((fits02.drop 24).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s028 : ((fits02.drop 28).take 4).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_s032 : ((fits02.drop 32).take 3).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02_end : (fits02.drop 35).all frame006test02=true := by
  decide +kernel

private theorem frame006scope02 : fits02.all frame006test02=true := by
  have h32 := stitchAt 32 3 frame006scope02_s032 frame006scope02_end
  have h28 := stitchAt 28 4 frame006scope02_s028 h32
  have h24 := stitchAt 24 4 frame006scope02_s024 h28
  have h20 := stitchAt 20 4 frame006scope02_s020 h24
  have h16 := stitchAt 16 4 frame006scope02_s016 h20
  have h12 := stitchAt 12 4 frame006scope02_s012 h16
  have h8 := stitchAt 8 4 frame006scope02_s008 h12
  have h4 := stitchAt 4 4 frame006scope02_s004 h8
  have h0 := stitchAt 0 4 frame006scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch02 : batch02.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope02

private abbrev frame006test03 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch03.stop,F)

private theorem frame006scope03_s000 : ((fits03.drop 0).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s004 : ((fits03.drop 4).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s008 : ((fits03.drop 8).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s012 : ((fits03.drop 12).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s016 : ((fits03.drop 16).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s020 : ((fits03.drop 20).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s024 : ((fits03.drop 24).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s028 : ((fits03.drop 28).take 4).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_s032 : ((fits03.drop 32).take 3).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03_end : (fits03.drop 35).all frame006test03=true := by
  decide +kernel

private theorem frame006scope03 : fits03.all frame006test03=true := by
  have h32 := stitchAt 32 3 frame006scope03_s032 frame006scope03_end
  have h28 := stitchAt 28 4 frame006scope03_s028 h32
  have h24 := stitchAt 24 4 frame006scope03_s024 h28
  have h20 := stitchAt 20 4 frame006scope03_s020 h24
  have h16 := stitchAt 16 4 frame006scope03_s016 h20
  have h12 := stitchAt 12 4 frame006scope03_s012 h16
  have h8 := stitchAt 8 4 frame006scope03_s008 h12
  have h4 := stitchAt 4 4 frame006scope03_s004 h8
  have h0 := stitchAt 0 4 frame006scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch03 : batch03.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope03

private abbrev frame006test04 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch04.stop,F)

private theorem frame006scope04_s000 : ((fits04.drop 0).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s004 : ((fits04.drop 4).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s008 : ((fits04.drop 8).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s012 : ((fits04.drop 12).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s016 : ((fits04.drop 16).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s020 : ((fits04.drop 20).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s024 : ((fits04.drop 24).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s028 : ((fits04.drop 28).take 4).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_s032 : ((fits04.drop 32).take 3).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04_end : (fits04.drop 35).all frame006test04=true := by
  decide +kernel

private theorem frame006scope04 : fits04.all frame006test04=true := by
  have h32 := stitchAt 32 3 frame006scope04_s032 frame006scope04_end
  have h28 := stitchAt 28 4 frame006scope04_s028 h32
  have h24 := stitchAt 24 4 frame006scope04_s024 h28
  have h20 := stitchAt 20 4 frame006scope04_s020 h24
  have h16 := stitchAt 16 4 frame006scope04_s016 h20
  have h12 := stitchAt 12 4 frame006scope04_s012 h16
  have h8 := stitchAt 8 4 frame006scope04_s008 h12
  have h4 := stitchAt 4 4 frame006scope04_s004 h8
  have h0 := stitchAt 0 4 frame006scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch04 : batch04.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope04

private abbrev frame006test05 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch05.stop,F)

private theorem frame006scope05_s000 : ((fits05.drop 0).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s004 : ((fits05.drop 4).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s008 : ((fits05.drop 8).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s012 : ((fits05.drop 12).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s016 : ((fits05.drop 16).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s020 : ((fits05.drop 20).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s024 : ((fits05.drop 24).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s028 : ((fits05.drop 28).take 4).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_s032 : ((fits05.drop 32).take 3).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05_end : (fits05.drop 35).all frame006test05=true := by
  decide +kernel

private theorem frame006scope05 : fits05.all frame006test05=true := by
  have h32 := stitchAt 32 3 frame006scope05_s032 frame006scope05_end
  have h28 := stitchAt 28 4 frame006scope05_s028 h32
  have h24 := stitchAt 24 4 frame006scope05_s024 h28
  have h20 := stitchAt 20 4 frame006scope05_s020 h24
  have h16 := stitchAt 16 4 frame006scope05_s016 h20
  have h12 := stitchAt 12 4 frame006scope05_s012 h16
  have h8 := stitchAt 8 4 frame006scope05_s008 h12
  have h4 := stitchAt 4 4 frame006scope05_s004 h8
  have h0 := stitchAt 0 4 frame006scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch05 : batch05.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope05

private abbrev frame006test06 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch06.stop,F)

private theorem frame006scope06_s000 : ((fits06.drop 0).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s004 : ((fits06.drop 4).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s008 : ((fits06.drop 8).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s012 : ((fits06.drop 12).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s016 : ((fits06.drop 16).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s020 : ((fits06.drop 20).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s024 : ((fits06.drop 24).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s028 : ((fits06.drop 28).take 4).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_s032 : ((fits06.drop 32).take 3).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06_end : (fits06.drop 35).all frame006test06=true := by
  decide +kernel

private theorem frame006scope06 : fits06.all frame006test06=true := by
  have h32 := stitchAt 32 3 frame006scope06_s032 frame006scope06_end
  have h28 := stitchAt 28 4 frame006scope06_s028 h32
  have h24 := stitchAt 24 4 frame006scope06_s024 h28
  have h20 := stitchAt 20 4 frame006scope06_s020 h24
  have h16 := stitchAt 16 4 frame006scope06_s016 h20
  have h12 := stitchAt 12 4 frame006scope06_s012 h16
  have h8 := stitchAt 8 4 frame006scope06_s008 h12
  have h4 := stitchAt 4 4 frame006scope06_s004 h8
  have h0 := stitchAt 0 4 frame006scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch06 : batch06.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope06

private abbrev frame006test07 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame14 (fun z => List.lookup (guideCode z) guide006)
    (batch07.stop,F)

private theorem frame006scope07_s000 : ((fits07.drop 0).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s004 : ((fits07.drop 4).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s008 : ((fits07.drop 8).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s012 : ((fits07.drop 12).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s016 : ((fits07.drop 16).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s020 : ((fits07.drop 20).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s024 : ((fits07.drop 24).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s028 : ((fits07.drop 28).take 4).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_s032 : ((fits07.drop 32).take 3).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07_end : (fits07.drop 35).all frame006test07=true := by
  decide +kernel

private theorem frame006scope07 : fits07.all frame006test07=true := by
  have h32 := stitchAt 32 3 frame006scope07_s032 frame006scope07_end
  have h28 := stitchAt 28 4 frame006scope07_s028 h32
  have h24 := stitchAt 24 4 frame006scope07_s024 h28
  have h20 := stitchAt 20 4 frame006scope07_s020 h24
  have h16 := stitchAt 16 4 frame006scope07_s016 h20
  have h12 := stitchAt 12 4 frame006scope07_s012 h16
  have h8 := stitchAt 8 4 frame006scope07_s008 h12
  have h4 := stitchAt 4 4 frame006scope07_s004 h8
  have h0 := stitchAt 0 4 frame006scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame006batch07 : batch07.pickTest original frame14=true :=
  FitBatch.pickTest_of_scoped scoped006 frame006scope07

private theorem frameBatches006 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame14)=true := by
  simp only [List.all_cons,List.all_nil,frame006batch00,frame006batch01,frame006batch02,frame006batch03,frame006batch04,frame006batch05,frame006batch06,frame006batch07,Bool.and_self]

theorem frameOK006 : frameRankTest original useStop frame14=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches006

theorem stripOK007 : stripTest frame15=true := by decide +kernel

theorem spanOK007 : checkChain 1024 960 [frame15.span]=true := by decide +kernel

private theorem guideAt007 : List.lookup frame15.span.1 guideTable=some guide007 := by
  decide +kernel

private theorem scoped007 : original.guide frame15.span.1 =
    (fun z => List.lookup (guideCode z) guide007) := by
  funext z
  change (List.lookup frame15.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide007
  simp only [guideAt007,Option.bind_some]

private abbrev frame007test00 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch00.stop,F)

private theorem frame007scope00_s000 : ((fits00.drop 0).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s004 : ((fits00.drop 4).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s008 : ((fits00.drop 8).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s012 : ((fits00.drop 12).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s016 : ((fits00.drop 16).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s020 : ((fits00.drop 20).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s024 : ((fits00.drop 24).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s028 : ((fits00.drop 28).take 4).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_s032 : ((fits00.drop 32).take 3).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00_end : (fits00.drop 35).all frame007test00=true := by
  decide +kernel

private theorem frame007scope00 : fits00.all frame007test00=true := by
  have h32 := stitchAt 32 3 frame007scope00_s032 frame007scope00_end
  have h28 := stitchAt 28 4 frame007scope00_s028 h32
  have h24 := stitchAt 24 4 frame007scope00_s024 h28
  have h20 := stitchAt 20 4 frame007scope00_s020 h24
  have h16 := stitchAt 16 4 frame007scope00_s016 h20
  have h12 := stitchAt 12 4 frame007scope00_s012 h16
  have h8 := stitchAt 8 4 frame007scope00_s008 h12
  have h4 := stitchAt 4 4 frame007scope00_s004 h8
  have h0 := stitchAt 0 4 frame007scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch00 : batch00.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope00

private abbrev frame007test01 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch01.stop,F)

private theorem frame007scope01_s000 : ((fits01.drop 0).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s004 : ((fits01.drop 4).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s008 : ((fits01.drop 8).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s012 : ((fits01.drop 12).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s016 : ((fits01.drop 16).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s020 : ((fits01.drop 20).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s024 : ((fits01.drop 24).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s028 : ((fits01.drop 28).take 4).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_s032 : ((fits01.drop 32).take 3).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01_end : (fits01.drop 35).all frame007test01=true := by
  decide +kernel

private theorem frame007scope01 : fits01.all frame007test01=true := by
  have h32 := stitchAt 32 3 frame007scope01_s032 frame007scope01_end
  have h28 := stitchAt 28 4 frame007scope01_s028 h32
  have h24 := stitchAt 24 4 frame007scope01_s024 h28
  have h20 := stitchAt 20 4 frame007scope01_s020 h24
  have h16 := stitchAt 16 4 frame007scope01_s016 h20
  have h12 := stitchAt 12 4 frame007scope01_s012 h16
  have h8 := stitchAt 8 4 frame007scope01_s008 h12
  have h4 := stitchAt 4 4 frame007scope01_s004 h8
  have h0 := stitchAt 0 4 frame007scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch01 : batch01.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope01

private abbrev frame007test02 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch02.stop,F)

private theorem frame007scope02_s000 : ((fits02.drop 0).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s004 : ((fits02.drop 4).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s008 : ((fits02.drop 8).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s012 : ((fits02.drop 12).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s016 : ((fits02.drop 16).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s020 : ((fits02.drop 20).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s024 : ((fits02.drop 24).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s028 : ((fits02.drop 28).take 4).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_s032 : ((fits02.drop 32).take 3).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02_end : (fits02.drop 35).all frame007test02=true := by
  decide +kernel

private theorem frame007scope02 : fits02.all frame007test02=true := by
  have h32 := stitchAt 32 3 frame007scope02_s032 frame007scope02_end
  have h28 := stitchAt 28 4 frame007scope02_s028 h32
  have h24 := stitchAt 24 4 frame007scope02_s024 h28
  have h20 := stitchAt 20 4 frame007scope02_s020 h24
  have h16 := stitchAt 16 4 frame007scope02_s016 h20
  have h12 := stitchAt 12 4 frame007scope02_s012 h16
  have h8 := stitchAt 8 4 frame007scope02_s008 h12
  have h4 := stitchAt 4 4 frame007scope02_s004 h8
  have h0 := stitchAt 0 4 frame007scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch02 : batch02.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope02

private abbrev frame007test03 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch03.stop,F)

private theorem frame007scope03_s000 : ((fits03.drop 0).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s004 : ((fits03.drop 4).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s008 : ((fits03.drop 8).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s012 : ((fits03.drop 12).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s016 : ((fits03.drop 16).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s020 : ((fits03.drop 20).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s024 : ((fits03.drop 24).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s028 : ((fits03.drop 28).take 4).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_s032 : ((fits03.drop 32).take 3).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03_end : (fits03.drop 35).all frame007test03=true := by
  decide +kernel

private theorem frame007scope03 : fits03.all frame007test03=true := by
  have h32 := stitchAt 32 3 frame007scope03_s032 frame007scope03_end
  have h28 := stitchAt 28 4 frame007scope03_s028 h32
  have h24 := stitchAt 24 4 frame007scope03_s024 h28
  have h20 := stitchAt 20 4 frame007scope03_s020 h24
  have h16 := stitchAt 16 4 frame007scope03_s016 h20
  have h12 := stitchAt 12 4 frame007scope03_s012 h16
  have h8 := stitchAt 8 4 frame007scope03_s008 h12
  have h4 := stitchAt 4 4 frame007scope03_s004 h8
  have h0 := stitchAt 0 4 frame007scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch03 : batch03.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope03

private abbrev frame007test04 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch04.stop,F)

private theorem frame007scope04_s000 : ((fits04.drop 0).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s004 : ((fits04.drop 4).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s008 : ((fits04.drop 8).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s012 : ((fits04.drop 12).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s016 : ((fits04.drop 16).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s020 : ((fits04.drop 20).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s024 : ((fits04.drop 24).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s028 : ((fits04.drop 28).take 4).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_s032 : ((fits04.drop 32).take 3).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04_end : (fits04.drop 35).all frame007test04=true := by
  decide +kernel

private theorem frame007scope04 : fits04.all frame007test04=true := by
  have h32 := stitchAt 32 3 frame007scope04_s032 frame007scope04_end
  have h28 := stitchAt 28 4 frame007scope04_s028 h32
  have h24 := stitchAt 24 4 frame007scope04_s024 h28
  have h20 := stitchAt 20 4 frame007scope04_s020 h24
  have h16 := stitchAt 16 4 frame007scope04_s016 h20
  have h12 := stitchAt 12 4 frame007scope04_s012 h16
  have h8 := stitchAt 8 4 frame007scope04_s008 h12
  have h4 := stitchAt 4 4 frame007scope04_s004 h8
  have h0 := stitchAt 0 4 frame007scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch04 : batch04.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope04

private abbrev frame007test05 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch05.stop,F)

private theorem frame007scope05_s000 : ((fits05.drop 0).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s004 : ((fits05.drop 4).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s008 : ((fits05.drop 8).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s012 : ((fits05.drop 12).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s016 : ((fits05.drop 16).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s020 : ((fits05.drop 20).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s024 : ((fits05.drop 24).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s028 : ((fits05.drop 28).take 4).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_s032 : ((fits05.drop 32).take 3).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05_end : (fits05.drop 35).all frame007test05=true := by
  decide +kernel

private theorem frame007scope05 : fits05.all frame007test05=true := by
  have h32 := stitchAt 32 3 frame007scope05_s032 frame007scope05_end
  have h28 := stitchAt 28 4 frame007scope05_s028 h32
  have h24 := stitchAt 24 4 frame007scope05_s024 h28
  have h20 := stitchAt 20 4 frame007scope05_s020 h24
  have h16 := stitchAt 16 4 frame007scope05_s016 h20
  have h12 := stitchAt 12 4 frame007scope05_s012 h16
  have h8 := stitchAt 8 4 frame007scope05_s008 h12
  have h4 := stitchAt 4 4 frame007scope05_s004 h8
  have h0 := stitchAt 0 4 frame007scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch05 : batch05.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope05

private abbrev frame007test06 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch06.stop,F)

private theorem frame007scope06_s000 : ((fits06.drop 0).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s004 : ((fits06.drop 4).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s008 : ((fits06.drop 8).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s012 : ((fits06.drop 12).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s016 : ((fits06.drop 16).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s020 : ((fits06.drop 20).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s024 : ((fits06.drop 24).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s028 : ((fits06.drop 28).take 4).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_s032 : ((fits06.drop 32).take 3).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06_end : (fits06.drop 35).all frame007test06=true := by
  decide +kernel

private theorem frame007scope06 : fits06.all frame007test06=true := by
  have h32 := stitchAt 32 3 frame007scope06_s032 frame007scope06_end
  have h28 := stitchAt 28 4 frame007scope06_s028 h32
  have h24 := stitchAt 24 4 frame007scope06_s024 h28
  have h20 := stitchAt 20 4 frame007scope06_s020 h24
  have h16 := stitchAt 16 4 frame007scope06_s016 h20
  have h12 := stitchAt 12 4 frame007scope06_s012 h16
  have h8 := stitchAt 8 4 frame007scope06_s008 h12
  have h4 := stitchAt 4 4 frame007scope06_s004 h8
  have h0 := stitchAt 0 4 frame007scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch06 : batch06.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope06

private abbrev frame007test07 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame15 (fun z => List.lookup (guideCode z) guide007)
    (batch07.stop,F)

private theorem frame007scope07_s000 : ((fits07.drop 0).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s004 : ((fits07.drop 4).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s008 : ((fits07.drop 8).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s012 : ((fits07.drop 12).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s016 : ((fits07.drop 16).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s020 : ((fits07.drop 20).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s024 : ((fits07.drop 24).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s028 : ((fits07.drop 28).take 4).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_s032 : ((fits07.drop 32).take 3).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07_end : (fits07.drop 35).all frame007test07=true := by
  decide +kernel

private theorem frame007scope07 : fits07.all frame007test07=true := by
  have h32 := stitchAt 32 3 frame007scope07_s032 frame007scope07_end
  have h28 := stitchAt 28 4 frame007scope07_s028 h32
  have h24 := stitchAt 24 4 frame007scope07_s024 h28
  have h20 := stitchAt 20 4 frame007scope07_s020 h24
  have h16 := stitchAt 16 4 frame007scope07_s016 h20
  have h12 := stitchAt 12 4 frame007scope07_s012 h16
  have h8 := stitchAt 8 4 frame007scope07_s008 h12
  have h4 := stitchAt 4 4 frame007scope07_s004 h8
  have h0 := stitchAt 0 4 frame007scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame007batch07 : batch07.pickTest original frame15=true :=
  FitBatch.pickTest_of_scoped scoped007 frame007scope07

private theorem frameBatches007 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame15)=true := by
  simp only [List.all_cons,List.all_nil,frame007batch00,frame007batch01,frame007batch02,frame007batch03,frame007batch04,frame007batch05,frame007batch06,frame007batch07,Bool.and_self]

theorem frameOK007 : frameRankTest original useStop frame15=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches007


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
