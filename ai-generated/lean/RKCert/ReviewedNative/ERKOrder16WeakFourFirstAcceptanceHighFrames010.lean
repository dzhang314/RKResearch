module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK020 : stripTest frame45=true := by decide +kernel

theorem spanOK020 : checkChain 1552 1544 [frame45.span]=true := by decide +kernel

private theorem guideAt020 : List.lookup frame45.span.1 guideTable=some guide020 := by
  decide +kernel

private theorem scoped020 : original.guide frame45.span.1 =
    (fun z => List.lookup (guideCode z) guide020) := by
  funext z
  change (List.lookup frame45.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide020
  simp only [guideAt020,Option.bind_some]

private abbrev frame020test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch00.stop,F)

private theorem frame020scope00_s000 : ((fits00.drop 0).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s004 : ((fits00.drop 4).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s008 : ((fits00.drop 8).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s012 : ((fits00.drop 12).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s016 : ((fits00.drop 16).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s020 : ((fits00.drop 20).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s024 : ((fits00.drop 24).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s028 : ((fits00.drop 28).take 4).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_s032 : ((fits00.drop 32).take 3).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00_end : (fits00.drop 35).all frame020test00=true := by
  decide +kernel

private theorem frame020scope00 : fits00.all frame020test00=true := by
  have h32 := stitchAt 32 3 frame020scope00_s032 frame020scope00_end
  have h28 := stitchAt 28 4 frame020scope00_s028 h32
  have h24 := stitchAt 24 4 frame020scope00_s024 h28
  have h20 := stitchAt 20 4 frame020scope00_s020 h24
  have h16 := stitchAt 16 4 frame020scope00_s016 h20
  have h12 := stitchAt 12 4 frame020scope00_s012 h16
  have h8 := stitchAt 8 4 frame020scope00_s008 h12
  have h4 := stitchAt 4 4 frame020scope00_s004 h8
  have h0 := stitchAt 0 4 frame020scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch00 : batch00.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope00

private abbrev frame020test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch01.stop,F)

private theorem frame020scope01_s000 : ((fits01.drop 0).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s004 : ((fits01.drop 4).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s008 : ((fits01.drop 8).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s012 : ((fits01.drop 12).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s016 : ((fits01.drop 16).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s020 : ((fits01.drop 20).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s024 : ((fits01.drop 24).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s028 : ((fits01.drop 28).take 4).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_s032 : ((fits01.drop 32).take 3).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01_end : (fits01.drop 35).all frame020test01=true := by
  decide +kernel

private theorem frame020scope01 : fits01.all frame020test01=true := by
  have h32 := stitchAt 32 3 frame020scope01_s032 frame020scope01_end
  have h28 := stitchAt 28 4 frame020scope01_s028 h32
  have h24 := stitchAt 24 4 frame020scope01_s024 h28
  have h20 := stitchAt 20 4 frame020scope01_s020 h24
  have h16 := stitchAt 16 4 frame020scope01_s016 h20
  have h12 := stitchAt 12 4 frame020scope01_s012 h16
  have h8 := stitchAt 8 4 frame020scope01_s008 h12
  have h4 := stitchAt 4 4 frame020scope01_s004 h8
  have h0 := stitchAt 0 4 frame020scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch01 : batch01.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope01

private abbrev frame020test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch02.stop,F)

private theorem frame020scope02_s000 : ((fits02.drop 0).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s004 : ((fits02.drop 4).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s008 : ((fits02.drop 8).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s012 : ((fits02.drop 12).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s016 : ((fits02.drop 16).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s020 : ((fits02.drop 20).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s024 : ((fits02.drop 24).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s028 : ((fits02.drop 28).take 4).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_s032 : ((fits02.drop 32).take 3).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02_end : (fits02.drop 35).all frame020test02=true := by
  decide +kernel

private theorem frame020scope02 : fits02.all frame020test02=true := by
  have h32 := stitchAt 32 3 frame020scope02_s032 frame020scope02_end
  have h28 := stitchAt 28 4 frame020scope02_s028 h32
  have h24 := stitchAt 24 4 frame020scope02_s024 h28
  have h20 := stitchAt 20 4 frame020scope02_s020 h24
  have h16 := stitchAt 16 4 frame020scope02_s016 h20
  have h12 := stitchAt 12 4 frame020scope02_s012 h16
  have h8 := stitchAt 8 4 frame020scope02_s008 h12
  have h4 := stitchAt 4 4 frame020scope02_s004 h8
  have h0 := stitchAt 0 4 frame020scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch02 : batch02.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope02

private abbrev frame020test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch03.stop,F)

private theorem frame020scope03_s000 : ((fits03.drop 0).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s004 : ((fits03.drop 4).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s008 : ((fits03.drop 8).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s012 : ((fits03.drop 12).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s016 : ((fits03.drop 16).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s020 : ((fits03.drop 20).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s024 : ((fits03.drop 24).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s028 : ((fits03.drop 28).take 4).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_s032 : ((fits03.drop 32).take 3).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03_end : (fits03.drop 35).all frame020test03=true := by
  decide +kernel

private theorem frame020scope03 : fits03.all frame020test03=true := by
  have h32 := stitchAt 32 3 frame020scope03_s032 frame020scope03_end
  have h28 := stitchAt 28 4 frame020scope03_s028 h32
  have h24 := stitchAt 24 4 frame020scope03_s024 h28
  have h20 := stitchAt 20 4 frame020scope03_s020 h24
  have h16 := stitchAt 16 4 frame020scope03_s016 h20
  have h12 := stitchAt 12 4 frame020scope03_s012 h16
  have h8 := stitchAt 8 4 frame020scope03_s008 h12
  have h4 := stitchAt 4 4 frame020scope03_s004 h8
  have h0 := stitchAt 0 4 frame020scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch03 : batch03.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope03

private abbrev frame020test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch04.stop,F)

private theorem frame020scope04_s000 : ((fits04.drop 0).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s004 : ((fits04.drop 4).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s008 : ((fits04.drop 8).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s012 : ((fits04.drop 12).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s016 : ((fits04.drop 16).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s020 : ((fits04.drop 20).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s024 : ((fits04.drop 24).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s028 : ((fits04.drop 28).take 4).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_s032 : ((fits04.drop 32).take 3).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04_end : (fits04.drop 35).all frame020test04=true := by
  decide +kernel

private theorem frame020scope04 : fits04.all frame020test04=true := by
  have h32 := stitchAt 32 3 frame020scope04_s032 frame020scope04_end
  have h28 := stitchAt 28 4 frame020scope04_s028 h32
  have h24 := stitchAt 24 4 frame020scope04_s024 h28
  have h20 := stitchAt 20 4 frame020scope04_s020 h24
  have h16 := stitchAt 16 4 frame020scope04_s016 h20
  have h12 := stitchAt 12 4 frame020scope04_s012 h16
  have h8 := stitchAt 8 4 frame020scope04_s008 h12
  have h4 := stitchAt 4 4 frame020scope04_s004 h8
  have h0 := stitchAt 0 4 frame020scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch04 : batch04.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope04

private abbrev frame020test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch05.stop,F)

private theorem frame020scope05_s000 : ((fits05.drop 0).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s004 : ((fits05.drop 4).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s008 : ((fits05.drop 8).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s012 : ((fits05.drop 12).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s016 : ((fits05.drop 16).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s020 : ((fits05.drop 20).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s024 : ((fits05.drop 24).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s028 : ((fits05.drop 28).take 4).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_s032 : ((fits05.drop 32).take 3).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05_end : (fits05.drop 35).all frame020test05=true := by
  decide +kernel

private theorem frame020scope05 : fits05.all frame020test05=true := by
  have h32 := stitchAt 32 3 frame020scope05_s032 frame020scope05_end
  have h28 := stitchAt 28 4 frame020scope05_s028 h32
  have h24 := stitchAt 24 4 frame020scope05_s024 h28
  have h20 := stitchAt 20 4 frame020scope05_s020 h24
  have h16 := stitchAt 16 4 frame020scope05_s016 h20
  have h12 := stitchAt 12 4 frame020scope05_s012 h16
  have h8 := stitchAt 8 4 frame020scope05_s008 h12
  have h4 := stitchAt 4 4 frame020scope05_s004 h8
  have h0 := stitchAt 0 4 frame020scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch05 : batch05.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope05

private abbrev frame020test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch06.stop,F)

private theorem frame020scope06_s000 : ((fits06.drop 0).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s004 : ((fits06.drop 4).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s008 : ((fits06.drop 8).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s012 : ((fits06.drop 12).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s016 : ((fits06.drop 16).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s020 : ((fits06.drop 20).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s024 : ((fits06.drop 24).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s028 : ((fits06.drop 28).take 4).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_s032 : ((fits06.drop 32).take 3).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06_end : (fits06.drop 35).all frame020test06=true := by
  decide +kernel

private theorem frame020scope06 : fits06.all frame020test06=true := by
  have h32 := stitchAt 32 3 frame020scope06_s032 frame020scope06_end
  have h28 := stitchAt 28 4 frame020scope06_s028 h32
  have h24 := stitchAt 24 4 frame020scope06_s024 h28
  have h20 := stitchAt 20 4 frame020scope06_s020 h24
  have h16 := stitchAt 16 4 frame020scope06_s016 h20
  have h12 := stitchAt 12 4 frame020scope06_s012 h16
  have h8 := stitchAt 8 4 frame020scope06_s008 h12
  have h4 := stitchAt 4 4 frame020scope06_s004 h8
  have h0 := stitchAt 0 4 frame020scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch06 : batch06.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope06

private abbrev frame020test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame45 (fun z => List.lookup (guideCode z) guide020)
    (batch07.stop,F)

private theorem frame020scope07_s000 : ((fits07.drop 0).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s004 : ((fits07.drop 4).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s008 : ((fits07.drop 8).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s012 : ((fits07.drop 12).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s016 : ((fits07.drop 16).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s020 : ((fits07.drop 20).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s024 : ((fits07.drop 24).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s028 : ((fits07.drop 28).take 4).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_s032 : ((fits07.drop 32).take 3).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07_end : (fits07.drop 35).all frame020test07=true := by
  decide +kernel

private theorem frame020scope07 : fits07.all frame020test07=true := by
  have h32 := stitchAt 32 3 frame020scope07_s032 frame020scope07_end
  have h28 := stitchAt 28 4 frame020scope07_s028 h32
  have h24 := stitchAt 24 4 frame020scope07_s024 h28
  have h20 := stitchAt 20 4 frame020scope07_s020 h24
  have h16 := stitchAt 16 4 frame020scope07_s016 h20
  have h12 := stitchAt 12 4 frame020scope07_s012 h16
  have h8 := stitchAt 8 4 frame020scope07_s008 h12
  have h4 := stitchAt 4 4 frame020scope07_s004 h8
  have h0 := stitchAt 0 4 frame020scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame020batch07 : batch07.pickTest original frame45=true :=
  FitBatch.pickTest_of_scoped scoped020 frame020scope07

private theorem frameBatches020 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame45)=true := by
  simp only [List.all_cons,List.all_nil,frame020batch00,frame020batch01,frame020batch02,frame020batch03,frame020batch04,frame020batch05,frame020batch06,frame020batch07,Bool.and_self]

theorem frameOK020 : frameRankTest original useStop frame45=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches020

theorem stripOK021 : stripTest frame46=true := by decide +kernel

theorem spanOK021 : checkChain 1568 1552 [frame46.span]=true := by decide +kernel

private theorem guideAt021 : List.lookup frame46.span.1 guideTable=some guide021 := by
  decide +kernel

private theorem scoped021 : original.guide frame46.span.1 =
    (fun z => List.lookup (guideCode z) guide021) := by
  funext z
  change (List.lookup frame46.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide021
  simp only [guideAt021,Option.bind_some]

private abbrev frame021test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch00.stop,F)

private theorem frame021scope00_s000 : ((fits00.drop 0).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s004 : ((fits00.drop 4).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s008 : ((fits00.drop 8).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s012 : ((fits00.drop 12).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s016 : ((fits00.drop 16).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s020 : ((fits00.drop 20).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s024 : ((fits00.drop 24).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s028 : ((fits00.drop 28).take 4).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_s032 : ((fits00.drop 32).take 3).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00_end : (fits00.drop 35).all frame021test00=true := by
  decide +kernel

private theorem frame021scope00 : fits00.all frame021test00=true := by
  have h32 := stitchAt 32 3 frame021scope00_s032 frame021scope00_end
  have h28 := stitchAt 28 4 frame021scope00_s028 h32
  have h24 := stitchAt 24 4 frame021scope00_s024 h28
  have h20 := stitchAt 20 4 frame021scope00_s020 h24
  have h16 := stitchAt 16 4 frame021scope00_s016 h20
  have h12 := stitchAt 12 4 frame021scope00_s012 h16
  have h8 := stitchAt 8 4 frame021scope00_s008 h12
  have h4 := stitchAt 4 4 frame021scope00_s004 h8
  have h0 := stitchAt 0 4 frame021scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch00 : batch00.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope00

private abbrev frame021test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch01.stop,F)

private theorem frame021scope01_s000 : ((fits01.drop 0).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s004 : ((fits01.drop 4).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s008 : ((fits01.drop 8).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s012 : ((fits01.drop 12).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s016 : ((fits01.drop 16).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s020 : ((fits01.drop 20).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s024 : ((fits01.drop 24).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s028 : ((fits01.drop 28).take 4).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_s032 : ((fits01.drop 32).take 3).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01_end : (fits01.drop 35).all frame021test01=true := by
  decide +kernel

private theorem frame021scope01 : fits01.all frame021test01=true := by
  have h32 := stitchAt 32 3 frame021scope01_s032 frame021scope01_end
  have h28 := stitchAt 28 4 frame021scope01_s028 h32
  have h24 := stitchAt 24 4 frame021scope01_s024 h28
  have h20 := stitchAt 20 4 frame021scope01_s020 h24
  have h16 := stitchAt 16 4 frame021scope01_s016 h20
  have h12 := stitchAt 12 4 frame021scope01_s012 h16
  have h8 := stitchAt 8 4 frame021scope01_s008 h12
  have h4 := stitchAt 4 4 frame021scope01_s004 h8
  have h0 := stitchAt 0 4 frame021scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch01 : batch01.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope01

private abbrev frame021test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch02.stop,F)

private theorem frame021scope02_s000 : ((fits02.drop 0).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s004 : ((fits02.drop 4).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s008 : ((fits02.drop 8).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s012 : ((fits02.drop 12).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s016 : ((fits02.drop 16).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s020 : ((fits02.drop 20).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s024 : ((fits02.drop 24).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s028 : ((fits02.drop 28).take 4).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_s032 : ((fits02.drop 32).take 3).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02_end : (fits02.drop 35).all frame021test02=true := by
  decide +kernel

private theorem frame021scope02 : fits02.all frame021test02=true := by
  have h32 := stitchAt 32 3 frame021scope02_s032 frame021scope02_end
  have h28 := stitchAt 28 4 frame021scope02_s028 h32
  have h24 := stitchAt 24 4 frame021scope02_s024 h28
  have h20 := stitchAt 20 4 frame021scope02_s020 h24
  have h16 := stitchAt 16 4 frame021scope02_s016 h20
  have h12 := stitchAt 12 4 frame021scope02_s012 h16
  have h8 := stitchAt 8 4 frame021scope02_s008 h12
  have h4 := stitchAt 4 4 frame021scope02_s004 h8
  have h0 := stitchAt 0 4 frame021scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch02 : batch02.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope02

private abbrev frame021test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch03.stop,F)

private theorem frame021scope03_s000 : ((fits03.drop 0).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s004 : ((fits03.drop 4).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s008 : ((fits03.drop 8).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s012 : ((fits03.drop 12).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s016 : ((fits03.drop 16).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s020 : ((fits03.drop 20).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s024 : ((fits03.drop 24).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s028 : ((fits03.drop 28).take 4).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_s032 : ((fits03.drop 32).take 3).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03_end : (fits03.drop 35).all frame021test03=true := by
  decide +kernel

private theorem frame021scope03 : fits03.all frame021test03=true := by
  have h32 := stitchAt 32 3 frame021scope03_s032 frame021scope03_end
  have h28 := stitchAt 28 4 frame021scope03_s028 h32
  have h24 := stitchAt 24 4 frame021scope03_s024 h28
  have h20 := stitchAt 20 4 frame021scope03_s020 h24
  have h16 := stitchAt 16 4 frame021scope03_s016 h20
  have h12 := stitchAt 12 4 frame021scope03_s012 h16
  have h8 := stitchAt 8 4 frame021scope03_s008 h12
  have h4 := stitchAt 4 4 frame021scope03_s004 h8
  have h0 := stitchAt 0 4 frame021scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch03 : batch03.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope03

private abbrev frame021test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch04.stop,F)

private theorem frame021scope04_s000 : ((fits04.drop 0).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s004 : ((fits04.drop 4).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s008 : ((fits04.drop 8).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s012 : ((fits04.drop 12).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s016 : ((fits04.drop 16).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s020 : ((fits04.drop 20).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s024 : ((fits04.drop 24).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s028 : ((fits04.drop 28).take 4).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_s032 : ((fits04.drop 32).take 3).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04_end : (fits04.drop 35).all frame021test04=true := by
  decide +kernel

private theorem frame021scope04 : fits04.all frame021test04=true := by
  have h32 := stitchAt 32 3 frame021scope04_s032 frame021scope04_end
  have h28 := stitchAt 28 4 frame021scope04_s028 h32
  have h24 := stitchAt 24 4 frame021scope04_s024 h28
  have h20 := stitchAt 20 4 frame021scope04_s020 h24
  have h16 := stitchAt 16 4 frame021scope04_s016 h20
  have h12 := stitchAt 12 4 frame021scope04_s012 h16
  have h8 := stitchAt 8 4 frame021scope04_s008 h12
  have h4 := stitchAt 4 4 frame021scope04_s004 h8
  have h0 := stitchAt 0 4 frame021scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch04 : batch04.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope04

private abbrev frame021test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch05.stop,F)

private theorem frame021scope05_s000 : ((fits05.drop 0).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s004 : ((fits05.drop 4).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s008 : ((fits05.drop 8).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s012 : ((fits05.drop 12).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s016 : ((fits05.drop 16).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s020 : ((fits05.drop 20).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s024 : ((fits05.drop 24).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s028 : ((fits05.drop 28).take 4).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_s032 : ((fits05.drop 32).take 3).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05_end : (fits05.drop 35).all frame021test05=true := by
  decide +kernel

private theorem frame021scope05 : fits05.all frame021test05=true := by
  have h32 := stitchAt 32 3 frame021scope05_s032 frame021scope05_end
  have h28 := stitchAt 28 4 frame021scope05_s028 h32
  have h24 := stitchAt 24 4 frame021scope05_s024 h28
  have h20 := stitchAt 20 4 frame021scope05_s020 h24
  have h16 := stitchAt 16 4 frame021scope05_s016 h20
  have h12 := stitchAt 12 4 frame021scope05_s012 h16
  have h8 := stitchAt 8 4 frame021scope05_s008 h12
  have h4 := stitchAt 4 4 frame021scope05_s004 h8
  have h0 := stitchAt 0 4 frame021scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch05 : batch05.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope05

private abbrev frame021test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch06.stop,F)

private theorem frame021scope06_s000 : ((fits06.drop 0).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s004 : ((fits06.drop 4).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s008 : ((fits06.drop 8).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s012 : ((fits06.drop 12).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s016 : ((fits06.drop 16).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s020 : ((fits06.drop 20).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s024 : ((fits06.drop 24).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s028 : ((fits06.drop 28).take 4).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_s032 : ((fits06.drop 32).take 3).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06_end : (fits06.drop 35).all frame021test06=true := by
  decide +kernel

private theorem frame021scope06 : fits06.all frame021test06=true := by
  have h32 := stitchAt 32 3 frame021scope06_s032 frame021scope06_end
  have h28 := stitchAt 28 4 frame021scope06_s028 h32
  have h24 := stitchAt 24 4 frame021scope06_s024 h28
  have h20 := stitchAt 20 4 frame021scope06_s020 h24
  have h16 := stitchAt 16 4 frame021scope06_s016 h20
  have h12 := stitchAt 12 4 frame021scope06_s012 h16
  have h8 := stitchAt 8 4 frame021scope06_s008 h12
  have h4 := stitchAt 4 4 frame021scope06_s004 h8
  have h0 := stitchAt 0 4 frame021scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch06 : batch06.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope06

private abbrev frame021test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame46 (fun z => List.lookup (guideCode z) guide021)
    (batch07.stop,F)

private theorem frame021scope07_s000 : ((fits07.drop 0).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s004 : ((fits07.drop 4).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s008 : ((fits07.drop 8).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s012 : ((fits07.drop 12).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s016 : ((fits07.drop 16).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s020 : ((fits07.drop 20).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s024 : ((fits07.drop 24).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s028 : ((fits07.drop 28).take 4).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_s032 : ((fits07.drop 32).take 3).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07_end : (fits07.drop 35).all frame021test07=true := by
  decide +kernel

private theorem frame021scope07 : fits07.all frame021test07=true := by
  have h32 := stitchAt 32 3 frame021scope07_s032 frame021scope07_end
  have h28 := stitchAt 28 4 frame021scope07_s028 h32
  have h24 := stitchAt 24 4 frame021scope07_s024 h28
  have h20 := stitchAt 20 4 frame021scope07_s020 h24
  have h16 := stitchAt 16 4 frame021scope07_s016 h20
  have h12 := stitchAt 12 4 frame021scope07_s012 h16
  have h8 := stitchAt 8 4 frame021scope07_s008 h12
  have h4 := stitchAt 4 4 frame021scope07_s004 h8
  have h0 := stitchAt 0 4 frame021scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame021batch07 : batch07.pickTest original frame46=true :=
  FitBatch.pickTest_of_scoped scoped021 frame021scope07

private theorem frameBatches021 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame46)=true := by
  simp only [List.all_cons,List.all_nil,frame021batch00,frame021batch01,frame021batch02,frame021batch03,frame021batch04,frame021batch05,frame021batch06,frame021batch07,Bool.and_self]

theorem frameOK021 : frameRankTest original useStop frame46=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches021


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
