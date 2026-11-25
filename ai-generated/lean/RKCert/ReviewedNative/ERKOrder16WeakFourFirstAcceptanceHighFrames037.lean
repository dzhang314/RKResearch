module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK074 : stripTest frame152=true := by decide +kernel

theorem spanOK074 : checkChain 1832 1824 [frame152.span]=true := by decide +kernel

private theorem guideAt074 : List.lookup frame152.span.1 guideTable=some guide074 := by
  decide +kernel

private theorem scoped074 : original.guide frame152.span.1 =
    (fun z => List.lookup (guideCode z) guide074) := by
  funext z
  change (List.lookup frame152.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide074
  simp only [guideAt074,Option.bind_some]

private abbrev frame074test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch00.stop,F)

private theorem frame074scope00_s000 : ((fits00.drop 0).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s004 : ((fits00.drop 4).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s008 : ((fits00.drop 8).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s012 : ((fits00.drop 12).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s016 : ((fits00.drop 16).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s020 : ((fits00.drop 20).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s024 : ((fits00.drop 24).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s028 : ((fits00.drop 28).take 4).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_s032 : ((fits00.drop 32).take 3).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00_end : (fits00.drop 35).all frame074test00=true := by
  decide +kernel

private theorem frame074scope00 : fits00.all frame074test00=true := by
  have h32 := stitchAt 32 3 frame074scope00_s032 frame074scope00_end
  have h28 := stitchAt 28 4 frame074scope00_s028 h32
  have h24 := stitchAt 24 4 frame074scope00_s024 h28
  have h20 := stitchAt 20 4 frame074scope00_s020 h24
  have h16 := stitchAt 16 4 frame074scope00_s016 h20
  have h12 := stitchAt 12 4 frame074scope00_s012 h16
  have h8 := stitchAt 8 4 frame074scope00_s008 h12
  have h4 := stitchAt 4 4 frame074scope00_s004 h8
  have h0 := stitchAt 0 4 frame074scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch00 : batch00.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope00

private abbrev frame074test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch01.stop,F)

private theorem frame074scope01_s000 : ((fits01.drop 0).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s004 : ((fits01.drop 4).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s008 : ((fits01.drop 8).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s012 : ((fits01.drop 12).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s016 : ((fits01.drop 16).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s020 : ((fits01.drop 20).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s024 : ((fits01.drop 24).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s028 : ((fits01.drop 28).take 4).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_s032 : ((fits01.drop 32).take 3).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01_end : (fits01.drop 35).all frame074test01=true := by
  decide +kernel

private theorem frame074scope01 : fits01.all frame074test01=true := by
  have h32 := stitchAt 32 3 frame074scope01_s032 frame074scope01_end
  have h28 := stitchAt 28 4 frame074scope01_s028 h32
  have h24 := stitchAt 24 4 frame074scope01_s024 h28
  have h20 := stitchAt 20 4 frame074scope01_s020 h24
  have h16 := stitchAt 16 4 frame074scope01_s016 h20
  have h12 := stitchAt 12 4 frame074scope01_s012 h16
  have h8 := stitchAt 8 4 frame074scope01_s008 h12
  have h4 := stitchAt 4 4 frame074scope01_s004 h8
  have h0 := stitchAt 0 4 frame074scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch01 : batch01.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope01

private abbrev frame074test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch02.stop,F)

private theorem frame074scope02_s000 : ((fits02.drop 0).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s004 : ((fits02.drop 4).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s008 : ((fits02.drop 8).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s012 : ((fits02.drop 12).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s016 : ((fits02.drop 16).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s020 : ((fits02.drop 20).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s024 : ((fits02.drop 24).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s028 : ((fits02.drop 28).take 4).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_s032 : ((fits02.drop 32).take 3).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02_end : (fits02.drop 35).all frame074test02=true := by
  decide +kernel

private theorem frame074scope02 : fits02.all frame074test02=true := by
  have h32 := stitchAt 32 3 frame074scope02_s032 frame074scope02_end
  have h28 := stitchAt 28 4 frame074scope02_s028 h32
  have h24 := stitchAt 24 4 frame074scope02_s024 h28
  have h20 := stitchAt 20 4 frame074scope02_s020 h24
  have h16 := stitchAt 16 4 frame074scope02_s016 h20
  have h12 := stitchAt 12 4 frame074scope02_s012 h16
  have h8 := stitchAt 8 4 frame074scope02_s008 h12
  have h4 := stitchAt 4 4 frame074scope02_s004 h8
  have h0 := stitchAt 0 4 frame074scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch02 : batch02.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope02

private abbrev frame074test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch03.stop,F)

private theorem frame074scope03_s000 : ((fits03.drop 0).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s004 : ((fits03.drop 4).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s008 : ((fits03.drop 8).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s012 : ((fits03.drop 12).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s016 : ((fits03.drop 16).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s020 : ((fits03.drop 20).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s024 : ((fits03.drop 24).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s028 : ((fits03.drop 28).take 4).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_s032 : ((fits03.drop 32).take 3).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03_end : (fits03.drop 35).all frame074test03=true := by
  decide +kernel

private theorem frame074scope03 : fits03.all frame074test03=true := by
  have h32 := stitchAt 32 3 frame074scope03_s032 frame074scope03_end
  have h28 := stitchAt 28 4 frame074scope03_s028 h32
  have h24 := stitchAt 24 4 frame074scope03_s024 h28
  have h20 := stitchAt 20 4 frame074scope03_s020 h24
  have h16 := stitchAt 16 4 frame074scope03_s016 h20
  have h12 := stitchAt 12 4 frame074scope03_s012 h16
  have h8 := stitchAt 8 4 frame074scope03_s008 h12
  have h4 := stitchAt 4 4 frame074scope03_s004 h8
  have h0 := stitchAt 0 4 frame074scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch03 : batch03.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope03

private abbrev frame074test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch04.stop,F)

private theorem frame074scope04_s000 : ((fits04.drop 0).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s004 : ((fits04.drop 4).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s008 : ((fits04.drop 8).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s012 : ((fits04.drop 12).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s016 : ((fits04.drop 16).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s020 : ((fits04.drop 20).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s024 : ((fits04.drop 24).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s028 : ((fits04.drop 28).take 4).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_s032 : ((fits04.drop 32).take 3).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04_end : (fits04.drop 35).all frame074test04=true := by
  decide +kernel

private theorem frame074scope04 : fits04.all frame074test04=true := by
  have h32 := stitchAt 32 3 frame074scope04_s032 frame074scope04_end
  have h28 := stitchAt 28 4 frame074scope04_s028 h32
  have h24 := stitchAt 24 4 frame074scope04_s024 h28
  have h20 := stitchAt 20 4 frame074scope04_s020 h24
  have h16 := stitchAt 16 4 frame074scope04_s016 h20
  have h12 := stitchAt 12 4 frame074scope04_s012 h16
  have h8 := stitchAt 8 4 frame074scope04_s008 h12
  have h4 := stitchAt 4 4 frame074scope04_s004 h8
  have h0 := stitchAt 0 4 frame074scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch04 : batch04.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope04

private abbrev frame074test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch05.stop,F)

private theorem frame074scope05_s000 : ((fits05.drop 0).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s004 : ((fits05.drop 4).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s008 : ((fits05.drop 8).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s012 : ((fits05.drop 12).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s016 : ((fits05.drop 16).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s020 : ((fits05.drop 20).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s024 : ((fits05.drop 24).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s028 : ((fits05.drop 28).take 4).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_s032 : ((fits05.drop 32).take 3).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05_end : (fits05.drop 35).all frame074test05=true := by
  decide +kernel

private theorem frame074scope05 : fits05.all frame074test05=true := by
  have h32 := stitchAt 32 3 frame074scope05_s032 frame074scope05_end
  have h28 := stitchAt 28 4 frame074scope05_s028 h32
  have h24 := stitchAt 24 4 frame074scope05_s024 h28
  have h20 := stitchAt 20 4 frame074scope05_s020 h24
  have h16 := stitchAt 16 4 frame074scope05_s016 h20
  have h12 := stitchAt 12 4 frame074scope05_s012 h16
  have h8 := stitchAt 8 4 frame074scope05_s008 h12
  have h4 := stitchAt 4 4 frame074scope05_s004 h8
  have h0 := stitchAt 0 4 frame074scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch05 : batch05.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope05

private abbrev frame074test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch06.stop,F)

private theorem frame074scope06_s000 : ((fits06.drop 0).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s004 : ((fits06.drop 4).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s008 : ((fits06.drop 8).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s012 : ((fits06.drop 12).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s016 : ((fits06.drop 16).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s020 : ((fits06.drop 20).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s024 : ((fits06.drop 24).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s028 : ((fits06.drop 28).take 4).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_s032 : ((fits06.drop 32).take 3).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06_end : (fits06.drop 35).all frame074test06=true := by
  decide +kernel

private theorem frame074scope06 : fits06.all frame074test06=true := by
  have h32 := stitchAt 32 3 frame074scope06_s032 frame074scope06_end
  have h28 := stitchAt 28 4 frame074scope06_s028 h32
  have h24 := stitchAt 24 4 frame074scope06_s024 h28
  have h20 := stitchAt 20 4 frame074scope06_s020 h24
  have h16 := stitchAt 16 4 frame074scope06_s016 h20
  have h12 := stitchAt 12 4 frame074scope06_s012 h16
  have h8 := stitchAt 8 4 frame074scope06_s008 h12
  have h4 := stitchAt 4 4 frame074scope06_s004 h8
  have h0 := stitchAt 0 4 frame074scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch06 : batch06.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope06

private abbrev frame074test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame152 (fun z => List.lookup (guideCode z) guide074)
    (batch07.stop,F)

private theorem frame074scope07_s000 : ((fits07.drop 0).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s004 : ((fits07.drop 4).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s008 : ((fits07.drop 8).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s012 : ((fits07.drop 12).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s016 : ((fits07.drop 16).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s020 : ((fits07.drop 20).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s024 : ((fits07.drop 24).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s028 : ((fits07.drop 28).take 4).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_s032 : ((fits07.drop 32).take 3).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07_end : (fits07.drop 35).all frame074test07=true := by
  decide +kernel

private theorem frame074scope07 : fits07.all frame074test07=true := by
  have h32 := stitchAt 32 3 frame074scope07_s032 frame074scope07_end
  have h28 := stitchAt 28 4 frame074scope07_s028 h32
  have h24 := stitchAt 24 4 frame074scope07_s024 h28
  have h20 := stitchAt 20 4 frame074scope07_s020 h24
  have h16 := stitchAt 16 4 frame074scope07_s016 h20
  have h12 := stitchAt 12 4 frame074scope07_s012 h16
  have h8 := stitchAt 8 4 frame074scope07_s008 h12
  have h4 := stitchAt 4 4 frame074scope07_s004 h8
  have h0 := stitchAt 0 4 frame074scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame074batch07 : batch07.pickTest original frame152=true :=
  FitBatch.pickTest_of_scoped scoped074 frame074scope07

private theorem frameBatches074 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame152)=true := by
  simp only [List.all_cons,List.all_nil,frame074batch00,frame074batch01,frame074batch02,frame074batch03,frame074batch04,frame074batch05,frame074batch06,frame074batch07,Bool.and_self]

theorem frameOK074 : frameRankTest original useStop frame152=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches074

theorem stripOK075 : stripTest frame153=true := by decide +kernel

theorem spanOK075 : checkChain 1840 1832 [frame153.span]=true := by decide +kernel

private theorem guideAt075 : List.lookup frame153.span.1 guideTable=some guide075 := by
  decide +kernel

private theorem scoped075 : original.guide frame153.span.1 =
    (fun z => List.lookup (guideCode z) guide075) := by
  funext z
  change (List.lookup frame153.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide075
  simp only [guideAt075,Option.bind_some]

private abbrev frame075test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch00.stop,F)

private theorem frame075scope00_s000 : ((fits00.drop 0).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s004 : ((fits00.drop 4).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s008 : ((fits00.drop 8).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s012 : ((fits00.drop 12).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s016 : ((fits00.drop 16).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s020 : ((fits00.drop 20).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s024 : ((fits00.drop 24).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s028 : ((fits00.drop 28).take 4).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_s032 : ((fits00.drop 32).take 3).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00_end : (fits00.drop 35).all frame075test00=true := by
  decide +kernel

private theorem frame075scope00 : fits00.all frame075test00=true := by
  have h32 := stitchAt 32 3 frame075scope00_s032 frame075scope00_end
  have h28 := stitchAt 28 4 frame075scope00_s028 h32
  have h24 := stitchAt 24 4 frame075scope00_s024 h28
  have h20 := stitchAt 20 4 frame075scope00_s020 h24
  have h16 := stitchAt 16 4 frame075scope00_s016 h20
  have h12 := stitchAt 12 4 frame075scope00_s012 h16
  have h8 := stitchAt 8 4 frame075scope00_s008 h12
  have h4 := stitchAt 4 4 frame075scope00_s004 h8
  have h0 := stitchAt 0 4 frame075scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch00 : batch00.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope00

private abbrev frame075test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch01.stop,F)

private theorem frame075scope01_s000 : ((fits01.drop 0).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s004 : ((fits01.drop 4).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s008 : ((fits01.drop 8).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s012 : ((fits01.drop 12).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s016 : ((fits01.drop 16).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s020 : ((fits01.drop 20).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s024 : ((fits01.drop 24).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s028 : ((fits01.drop 28).take 4).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_s032 : ((fits01.drop 32).take 3).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01_end : (fits01.drop 35).all frame075test01=true := by
  decide +kernel

private theorem frame075scope01 : fits01.all frame075test01=true := by
  have h32 := stitchAt 32 3 frame075scope01_s032 frame075scope01_end
  have h28 := stitchAt 28 4 frame075scope01_s028 h32
  have h24 := stitchAt 24 4 frame075scope01_s024 h28
  have h20 := stitchAt 20 4 frame075scope01_s020 h24
  have h16 := stitchAt 16 4 frame075scope01_s016 h20
  have h12 := stitchAt 12 4 frame075scope01_s012 h16
  have h8 := stitchAt 8 4 frame075scope01_s008 h12
  have h4 := stitchAt 4 4 frame075scope01_s004 h8
  have h0 := stitchAt 0 4 frame075scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch01 : batch01.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope01

private abbrev frame075test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch02.stop,F)

private theorem frame075scope02_s000 : ((fits02.drop 0).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s004 : ((fits02.drop 4).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s008 : ((fits02.drop 8).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s012 : ((fits02.drop 12).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s016 : ((fits02.drop 16).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s020 : ((fits02.drop 20).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s024 : ((fits02.drop 24).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s028 : ((fits02.drop 28).take 4).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_s032 : ((fits02.drop 32).take 3).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02_end : (fits02.drop 35).all frame075test02=true := by
  decide +kernel

private theorem frame075scope02 : fits02.all frame075test02=true := by
  have h32 := stitchAt 32 3 frame075scope02_s032 frame075scope02_end
  have h28 := stitchAt 28 4 frame075scope02_s028 h32
  have h24 := stitchAt 24 4 frame075scope02_s024 h28
  have h20 := stitchAt 20 4 frame075scope02_s020 h24
  have h16 := stitchAt 16 4 frame075scope02_s016 h20
  have h12 := stitchAt 12 4 frame075scope02_s012 h16
  have h8 := stitchAt 8 4 frame075scope02_s008 h12
  have h4 := stitchAt 4 4 frame075scope02_s004 h8
  have h0 := stitchAt 0 4 frame075scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch02 : batch02.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope02

private abbrev frame075test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch03.stop,F)

private theorem frame075scope03_s000 : ((fits03.drop 0).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s004 : ((fits03.drop 4).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s008 : ((fits03.drop 8).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s012 : ((fits03.drop 12).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s016 : ((fits03.drop 16).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s020 : ((fits03.drop 20).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s024 : ((fits03.drop 24).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s028 : ((fits03.drop 28).take 4).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_s032 : ((fits03.drop 32).take 3).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03_end : (fits03.drop 35).all frame075test03=true := by
  decide +kernel

private theorem frame075scope03 : fits03.all frame075test03=true := by
  have h32 := stitchAt 32 3 frame075scope03_s032 frame075scope03_end
  have h28 := stitchAt 28 4 frame075scope03_s028 h32
  have h24 := stitchAt 24 4 frame075scope03_s024 h28
  have h20 := stitchAt 20 4 frame075scope03_s020 h24
  have h16 := stitchAt 16 4 frame075scope03_s016 h20
  have h12 := stitchAt 12 4 frame075scope03_s012 h16
  have h8 := stitchAt 8 4 frame075scope03_s008 h12
  have h4 := stitchAt 4 4 frame075scope03_s004 h8
  have h0 := stitchAt 0 4 frame075scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch03 : batch03.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope03

private abbrev frame075test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch04.stop,F)

private theorem frame075scope04_s000 : ((fits04.drop 0).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s004 : ((fits04.drop 4).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s008 : ((fits04.drop 8).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s012 : ((fits04.drop 12).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s016 : ((fits04.drop 16).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s020 : ((fits04.drop 20).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s024 : ((fits04.drop 24).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s028 : ((fits04.drop 28).take 4).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_s032 : ((fits04.drop 32).take 3).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04_end : (fits04.drop 35).all frame075test04=true := by
  decide +kernel

private theorem frame075scope04 : fits04.all frame075test04=true := by
  have h32 := stitchAt 32 3 frame075scope04_s032 frame075scope04_end
  have h28 := stitchAt 28 4 frame075scope04_s028 h32
  have h24 := stitchAt 24 4 frame075scope04_s024 h28
  have h20 := stitchAt 20 4 frame075scope04_s020 h24
  have h16 := stitchAt 16 4 frame075scope04_s016 h20
  have h12 := stitchAt 12 4 frame075scope04_s012 h16
  have h8 := stitchAt 8 4 frame075scope04_s008 h12
  have h4 := stitchAt 4 4 frame075scope04_s004 h8
  have h0 := stitchAt 0 4 frame075scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch04 : batch04.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope04

private abbrev frame075test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch05.stop,F)

private theorem frame075scope05_s000 : ((fits05.drop 0).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s004 : ((fits05.drop 4).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s008 : ((fits05.drop 8).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s012 : ((fits05.drop 12).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s016 : ((fits05.drop 16).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s020 : ((fits05.drop 20).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s024 : ((fits05.drop 24).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s028 : ((fits05.drop 28).take 4).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_s032 : ((fits05.drop 32).take 3).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05_end : (fits05.drop 35).all frame075test05=true := by
  decide +kernel

private theorem frame075scope05 : fits05.all frame075test05=true := by
  have h32 := stitchAt 32 3 frame075scope05_s032 frame075scope05_end
  have h28 := stitchAt 28 4 frame075scope05_s028 h32
  have h24 := stitchAt 24 4 frame075scope05_s024 h28
  have h20 := stitchAt 20 4 frame075scope05_s020 h24
  have h16 := stitchAt 16 4 frame075scope05_s016 h20
  have h12 := stitchAt 12 4 frame075scope05_s012 h16
  have h8 := stitchAt 8 4 frame075scope05_s008 h12
  have h4 := stitchAt 4 4 frame075scope05_s004 h8
  have h0 := stitchAt 0 4 frame075scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch05 : batch05.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope05

private abbrev frame075test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch06.stop,F)

private theorem frame075scope06_s000 : ((fits06.drop 0).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s004 : ((fits06.drop 4).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s008 : ((fits06.drop 8).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s012 : ((fits06.drop 12).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s016 : ((fits06.drop 16).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s020 : ((fits06.drop 20).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s024 : ((fits06.drop 24).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s028 : ((fits06.drop 28).take 4).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_s032 : ((fits06.drop 32).take 3).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06_end : (fits06.drop 35).all frame075test06=true := by
  decide +kernel

private theorem frame075scope06 : fits06.all frame075test06=true := by
  have h32 := stitchAt 32 3 frame075scope06_s032 frame075scope06_end
  have h28 := stitchAt 28 4 frame075scope06_s028 h32
  have h24 := stitchAt 24 4 frame075scope06_s024 h28
  have h20 := stitchAt 20 4 frame075scope06_s020 h24
  have h16 := stitchAt 16 4 frame075scope06_s016 h20
  have h12 := stitchAt 12 4 frame075scope06_s012 h16
  have h8 := stitchAt 8 4 frame075scope06_s008 h12
  have h4 := stitchAt 4 4 frame075scope06_s004 h8
  have h0 := stitchAt 0 4 frame075scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch06 : batch06.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope06

private abbrev frame075test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame153 (fun z => List.lookup (guideCode z) guide075)
    (batch07.stop,F)

private theorem frame075scope07_s000 : ((fits07.drop 0).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s004 : ((fits07.drop 4).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s008 : ((fits07.drop 8).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s012 : ((fits07.drop 12).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s016 : ((fits07.drop 16).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s020 : ((fits07.drop 20).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s024 : ((fits07.drop 24).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s028 : ((fits07.drop 28).take 4).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_s032 : ((fits07.drop 32).take 3).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07_end : (fits07.drop 35).all frame075test07=true := by
  decide +kernel

private theorem frame075scope07 : fits07.all frame075test07=true := by
  have h32 := stitchAt 32 3 frame075scope07_s032 frame075scope07_end
  have h28 := stitchAt 28 4 frame075scope07_s028 h32
  have h24 := stitchAt 24 4 frame075scope07_s024 h28
  have h20 := stitchAt 20 4 frame075scope07_s020 h24
  have h16 := stitchAt 16 4 frame075scope07_s016 h20
  have h12 := stitchAt 12 4 frame075scope07_s012 h16
  have h8 := stitchAt 8 4 frame075scope07_s008 h12
  have h4 := stitchAt 4 4 frame075scope07_s004 h8
  have h0 := stitchAt 0 4 frame075scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame075batch07 : batch07.pickTest original frame153=true :=
  FitBatch.pickTest_of_scoped scoped075 frame075scope07

private theorem frameBatches075 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame153)=true := by
  simp only [List.all_cons,List.all_nil,frame075batch00,frame075batch01,frame075batch02,frame075batch03,frame075batch04,frame075batch05,frame075batch06,frame075batch07,Bool.and_self]

theorem frameOK075 : frameRankTest original useStop frame153=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches075


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
