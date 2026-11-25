module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK050 : stripTest frame102=true := by decide +kernel

theorem spanOK050 : checkChain 1760 1759 [frame102.span]=true := by decide +kernel

private theorem guideAt050 : List.lookup frame102.span.1 guideTable=some guide050 := by
  decide +kernel

private theorem scoped050 : original.guide frame102.span.1 =
    (fun z => List.lookup (guideCode z) guide050) := by
  funext z
  change (List.lookup frame102.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide050
  simp only [guideAt050,Option.bind_some]

private abbrev frame050test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch00.stop,F)

private theorem frame050scope00_s000 : ((fits00.drop 0).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s004 : ((fits00.drop 4).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s008 : ((fits00.drop 8).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s012 : ((fits00.drop 12).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s016 : ((fits00.drop 16).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s020 : ((fits00.drop 20).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s024 : ((fits00.drop 24).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s028 : ((fits00.drop 28).take 4).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_s032 : ((fits00.drop 32).take 3).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00_end : (fits00.drop 35).all frame050test00=true := by
  decide +kernel

private theorem frame050scope00 : fits00.all frame050test00=true := by
  have h32 := stitchAt 32 3 frame050scope00_s032 frame050scope00_end
  have h28 := stitchAt 28 4 frame050scope00_s028 h32
  have h24 := stitchAt 24 4 frame050scope00_s024 h28
  have h20 := stitchAt 20 4 frame050scope00_s020 h24
  have h16 := stitchAt 16 4 frame050scope00_s016 h20
  have h12 := stitchAt 12 4 frame050scope00_s012 h16
  have h8 := stitchAt 8 4 frame050scope00_s008 h12
  have h4 := stitchAt 4 4 frame050scope00_s004 h8
  have h0 := stitchAt 0 4 frame050scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch00 : batch00.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope00

private abbrev frame050test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch01.stop,F)

private theorem frame050scope01_s000 : ((fits01.drop 0).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s004 : ((fits01.drop 4).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s008 : ((fits01.drop 8).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s012 : ((fits01.drop 12).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s016 : ((fits01.drop 16).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s020 : ((fits01.drop 20).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s024 : ((fits01.drop 24).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s028 : ((fits01.drop 28).take 4).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_s032 : ((fits01.drop 32).take 3).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01_end : (fits01.drop 35).all frame050test01=true := by
  decide +kernel

private theorem frame050scope01 : fits01.all frame050test01=true := by
  have h32 := stitchAt 32 3 frame050scope01_s032 frame050scope01_end
  have h28 := stitchAt 28 4 frame050scope01_s028 h32
  have h24 := stitchAt 24 4 frame050scope01_s024 h28
  have h20 := stitchAt 20 4 frame050scope01_s020 h24
  have h16 := stitchAt 16 4 frame050scope01_s016 h20
  have h12 := stitchAt 12 4 frame050scope01_s012 h16
  have h8 := stitchAt 8 4 frame050scope01_s008 h12
  have h4 := stitchAt 4 4 frame050scope01_s004 h8
  have h0 := stitchAt 0 4 frame050scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch01 : batch01.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope01

private abbrev frame050test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch02.stop,F)

private theorem frame050scope02_s000 : ((fits02.drop 0).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s004 : ((fits02.drop 4).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s008 : ((fits02.drop 8).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s012 : ((fits02.drop 12).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s016 : ((fits02.drop 16).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s020 : ((fits02.drop 20).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s024 : ((fits02.drop 24).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s028 : ((fits02.drop 28).take 4).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_s032 : ((fits02.drop 32).take 3).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02_end : (fits02.drop 35).all frame050test02=true := by
  decide +kernel

private theorem frame050scope02 : fits02.all frame050test02=true := by
  have h32 := stitchAt 32 3 frame050scope02_s032 frame050scope02_end
  have h28 := stitchAt 28 4 frame050scope02_s028 h32
  have h24 := stitchAt 24 4 frame050scope02_s024 h28
  have h20 := stitchAt 20 4 frame050scope02_s020 h24
  have h16 := stitchAt 16 4 frame050scope02_s016 h20
  have h12 := stitchAt 12 4 frame050scope02_s012 h16
  have h8 := stitchAt 8 4 frame050scope02_s008 h12
  have h4 := stitchAt 4 4 frame050scope02_s004 h8
  have h0 := stitchAt 0 4 frame050scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch02 : batch02.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope02

private abbrev frame050test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch03.stop,F)

private theorem frame050scope03_s000 : ((fits03.drop 0).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s004 : ((fits03.drop 4).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s008 : ((fits03.drop 8).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s012 : ((fits03.drop 12).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s016 : ((fits03.drop 16).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s020 : ((fits03.drop 20).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s024 : ((fits03.drop 24).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s028 : ((fits03.drop 28).take 4).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_s032 : ((fits03.drop 32).take 3).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03_end : (fits03.drop 35).all frame050test03=true := by
  decide +kernel

private theorem frame050scope03 : fits03.all frame050test03=true := by
  have h32 := stitchAt 32 3 frame050scope03_s032 frame050scope03_end
  have h28 := stitchAt 28 4 frame050scope03_s028 h32
  have h24 := stitchAt 24 4 frame050scope03_s024 h28
  have h20 := stitchAt 20 4 frame050scope03_s020 h24
  have h16 := stitchAt 16 4 frame050scope03_s016 h20
  have h12 := stitchAt 12 4 frame050scope03_s012 h16
  have h8 := stitchAt 8 4 frame050scope03_s008 h12
  have h4 := stitchAt 4 4 frame050scope03_s004 h8
  have h0 := stitchAt 0 4 frame050scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch03 : batch03.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope03

private abbrev frame050test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch04.stop,F)

private theorem frame050scope04_s000 : ((fits04.drop 0).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s004 : ((fits04.drop 4).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s008 : ((fits04.drop 8).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s012 : ((fits04.drop 12).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s016 : ((fits04.drop 16).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s020 : ((fits04.drop 20).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s024 : ((fits04.drop 24).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s028 : ((fits04.drop 28).take 4).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_s032 : ((fits04.drop 32).take 3).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04_end : (fits04.drop 35).all frame050test04=true := by
  decide +kernel

private theorem frame050scope04 : fits04.all frame050test04=true := by
  have h32 := stitchAt 32 3 frame050scope04_s032 frame050scope04_end
  have h28 := stitchAt 28 4 frame050scope04_s028 h32
  have h24 := stitchAt 24 4 frame050scope04_s024 h28
  have h20 := stitchAt 20 4 frame050scope04_s020 h24
  have h16 := stitchAt 16 4 frame050scope04_s016 h20
  have h12 := stitchAt 12 4 frame050scope04_s012 h16
  have h8 := stitchAt 8 4 frame050scope04_s008 h12
  have h4 := stitchAt 4 4 frame050scope04_s004 h8
  have h0 := stitchAt 0 4 frame050scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch04 : batch04.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope04

private abbrev frame050test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch05.stop,F)

private theorem frame050scope05_s000 : ((fits05.drop 0).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s004 : ((fits05.drop 4).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s008 : ((fits05.drop 8).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s012 : ((fits05.drop 12).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s016 : ((fits05.drop 16).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s020 : ((fits05.drop 20).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s024 : ((fits05.drop 24).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s028 : ((fits05.drop 28).take 4).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_s032 : ((fits05.drop 32).take 3).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05_end : (fits05.drop 35).all frame050test05=true := by
  decide +kernel

private theorem frame050scope05 : fits05.all frame050test05=true := by
  have h32 := stitchAt 32 3 frame050scope05_s032 frame050scope05_end
  have h28 := stitchAt 28 4 frame050scope05_s028 h32
  have h24 := stitchAt 24 4 frame050scope05_s024 h28
  have h20 := stitchAt 20 4 frame050scope05_s020 h24
  have h16 := stitchAt 16 4 frame050scope05_s016 h20
  have h12 := stitchAt 12 4 frame050scope05_s012 h16
  have h8 := stitchAt 8 4 frame050scope05_s008 h12
  have h4 := stitchAt 4 4 frame050scope05_s004 h8
  have h0 := stitchAt 0 4 frame050scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch05 : batch05.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope05

private abbrev frame050test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch06.stop,F)

private theorem frame050scope06_s000 : ((fits06.drop 0).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s004 : ((fits06.drop 4).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s008 : ((fits06.drop 8).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s012 : ((fits06.drop 12).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s016 : ((fits06.drop 16).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s020 : ((fits06.drop 20).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s024 : ((fits06.drop 24).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s028 : ((fits06.drop 28).take 4).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_s032 : ((fits06.drop 32).take 3).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06_end : (fits06.drop 35).all frame050test06=true := by
  decide +kernel

private theorem frame050scope06 : fits06.all frame050test06=true := by
  have h32 := stitchAt 32 3 frame050scope06_s032 frame050scope06_end
  have h28 := stitchAt 28 4 frame050scope06_s028 h32
  have h24 := stitchAt 24 4 frame050scope06_s024 h28
  have h20 := stitchAt 20 4 frame050scope06_s020 h24
  have h16 := stitchAt 16 4 frame050scope06_s016 h20
  have h12 := stitchAt 12 4 frame050scope06_s012 h16
  have h8 := stitchAt 8 4 frame050scope06_s008 h12
  have h4 := stitchAt 4 4 frame050scope06_s004 h8
  have h0 := stitchAt 0 4 frame050scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch06 : batch06.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope06

private abbrev frame050test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame102 (fun z => List.lookup (guideCode z) guide050)
    (batch07.stop,F)

private theorem frame050scope07_s000 : ((fits07.drop 0).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s004 : ((fits07.drop 4).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s008 : ((fits07.drop 8).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s012 : ((fits07.drop 12).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s016 : ((fits07.drop 16).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s020 : ((fits07.drop 20).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s024 : ((fits07.drop 24).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s028 : ((fits07.drop 28).take 4).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_s032 : ((fits07.drop 32).take 3).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07_end : (fits07.drop 35).all frame050test07=true := by
  decide +kernel

private theorem frame050scope07 : fits07.all frame050test07=true := by
  have h32 := stitchAt 32 3 frame050scope07_s032 frame050scope07_end
  have h28 := stitchAt 28 4 frame050scope07_s028 h32
  have h24 := stitchAt 24 4 frame050scope07_s024 h28
  have h20 := stitchAt 20 4 frame050scope07_s020 h24
  have h16 := stitchAt 16 4 frame050scope07_s016 h20
  have h12 := stitchAt 12 4 frame050scope07_s012 h16
  have h8 := stitchAt 8 4 frame050scope07_s008 h12
  have h4 := stitchAt 4 4 frame050scope07_s004 h8
  have h0 := stitchAt 0 4 frame050scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame050batch07 : batch07.pickTest original frame102=true :=
  FitBatch.pickTest_of_scoped scoped050 frame050scope07

private theorem frameBatches050 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame102)=true := by
  simp only [List.all_cons,List.all_nil,frame050batch00,frame050batch01,frame050batch02,frame050batch03,frame050batch04,frame050batch05,frame050batch06,frame050batch07,Bool.and_self]

theorem frameOK050 : frameRankTest original useStop frame102=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches050

theorem stripOK051 : stripTest frame108=true := by decide +kernel

theorem spanOK051 : checkChain 1761 1760 [frame108.span]=true := by decide +kernel

private theorem guideAt051 : List.lookup frame108.span.1 guideTable=some guide051 := by
  decide +kernel

private theorem scoped051 : original.guide frame108.span.1 =
    (fun z => List.lookup (guideCode z) guide051) := by
  funext z
  change (List.lookup frame108.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide051
  simp only [guideAt051,Option.bind_some]

private abbrev frame051test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch00.stop,F)

private theorem frame051scope00_s000 : ((fits00.drop 0).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s004 : ((fits00.drop 4).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s008 : ((fits00.drop 8).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s012 : ((fits00.drop 12).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s016 : ((fits00.drop 16).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s020 : ((fits00.drop 20).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s024 : ((fits00.drop 24).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s028 : ((fits00.drop 28).take 4).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_s032 : ((fits00.drop 32).take 3).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00_end : (fits00.drop 35).all frame051test00=true := by
  decide +kernel

private theorem frame051scope00 : fits00.all frame051test00=true := by
  have h32 := stitchAt 32 3 frame051scope00_s032 frame051scope00_end
  have h28 := stitchAt 28 4 frame051scope00_s028 h32
  have h24 := stitchAt 24 4 frame051scope00_s024 h28
  have h20 := stitchAt 20 4 frame051scope00_s020 h24
  have h16 := stitchAt 16 4 frame051scope00_s016 h20
  have h12 := stitchAt 12 4 frame051scope00_s012 h16
  have h8 := stitchAt 8 4 frame051scope00_s008 h12
  have h4 := stitchAt 4 4 frame051scope00_s004 h8
  have h0 := stitchAt 0 4 frame051scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch00 : batch00.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope00

private abbrev frame051test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch01.stop,F)

private theorem frame051scope01_s000 : ((fits01.drop 0).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s004 : ((fits01.drop 4).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s008 : ((fits01.drop 8).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s012 : ((fits01.drop 12).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s016 : ((fits01.drop 16).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s020 : ((fits01.drop 20).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s024 : ((fits01.drop 24).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s028 : ((fits01.drop 28).take 4).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_s032 : ((fits01.drop 32).take 3).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01_end : (fits01.drop 35).all frame051test01=true := by
  decide +kernel

private theorem frame051scope01 : fits01.all frame051test01=true := by
  have h32 := stitchAt 32 3 frame051scope01_s032 frame051scope01_end
  have h28 := stitchAt 28 4 frame051scope01_s028 h32
  have h24 := stitchAt 24 4 frame051scope01_s024 h28
  have h20 := stitchAt 20 4 frame051scope01_s020 h24
  have h16 := stitchAt 16 4 frame051scope01_s016 h20
  have h12 := stitchAt 12 4 frame051scope01_s012 h16
  have h8 := stitchAt 8 4 frame051scope01_s008 h12
  have h4 := stitchAt 4 4 frame051scope01_s004 h8
  have h0 := stitchAt 0 4 frame051scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch01 : batch01.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope01

private abbrev frame051test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch02.stop,F)

private theorem frame051scope02_s000 : ((fits02.drop 0).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s004 : ((fits02.drop 4).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s008 : ((fits02.drop 8).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s012 : ((fits02.drop 12).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s016 : ((fits02.drop 16).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s020 : ((fits02.drop 20).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s024 : ((fits02.drop 24).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s028 : ((fits02.drop 28).take 4).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_s032 : ((fits02.drop 32).take 3).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02_end : (fits02.drop 35).all frame051test02=true := by
  decide +kernel

private theorem frame051scope02 : fits02.all frame051test02=true := by
  have h32 := stitchAt 32 3 frame051scope02_s032 frame051scope02_end
  have h28 := stitchAt 28 4 frame051scope02_s028 h32
  have h24 := stitchAt 24 4 frame051scope02_s024 h28
  have h20 := stitchAt 20 4 frame051scope02_s020 h24
  have h16 := stitchAt 16 4 frame051scope02_s016 h20
  have h12 := stitchAt 12 4 frame051scope02_s012 h16
  have h8 := stitchAt 8 4 frame051scope02_s008 h12
  have h4 := stitchAt 4 4 frame051scope02_s004 h8
  have h0 := stitchAt 0 4 frame051scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch02 : batch02.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope02

private abbrev frame051test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch03.stop,F)

private theorem frame051scope03_s000 : ((fits03.drop 0).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s004 : ((fits03.drop 4).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s008 : ((fits03.drop 8).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s012 : ((fits03.drop 12).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s016 : ((fits03.drop 16).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s020 : ((fits03.drop 20).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s024 : ((fits03.drop 24).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s028 : ((fits03.drop 28).take 4).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_s032 : ((fits03.drop 32).take 3).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03_end : (fits03.drop 35).all frame051test03=true := by
  decide +kernel

private theorem frame051scope03 : fits03.all frame051test03=true := by
  have h32 := stitchAt 32 3 frame051scope03_s032 frame051scope03_end
  have h28 := stitchAt 28 4 frame051scope03_s028 h32
  have h24 := stitchAt 24 4 frame051scope03_s024 h28
  have h20 := stitchAt 20 4 frame051scope03_s020 h24
  have h16 := stitchAt 16 4 frame051scope03_s016 h20
  have h12 := stitchAt 12 4 frame051scope03_s012 h16
  have h8 := stitchAt 8 4 frame051scope03_s008 h12
  have h4 := stitchAt 4 4 frame051scope03_s004 h8
  have h0 := stitchAt 0 4 frame051scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch03 : batch03.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope03

private abbrev frame051test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch04.stop,F)

private theorem frame051scope04_s000 : ((fits04.drop 0).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s004 : ((fits04.drop 4).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s008 : ((fits04.drop 8).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s012 : ((fits04.drop 12).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s016 : ((fits04.drop 16).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s020 : ((fits04.drop 20).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s024 : ((fits04.drop 24).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s028 : ((fits04.drop 28).take 4).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_s032 : ((fits04.drop 32).take 3).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04_end : (fits04.drop 35).all frame051test04=true := by
  decide +kernel

private theorem frame051scope04 : fits04.all frame051test04=true := by
  have h32 := stitchAt 32 3 frame051scope04_s032 frame051scope04_end
  have h28 := stitchAt 28 4 frame051scope04_s028 h32
  have h24 := stitchAt 24 4 frame051scope04_s024 h28
  have h20 := stitchAt 20 4 frame051scope04_s020 h24
  have h16 := stitchAt 16 4 frame051scope04_s016 h20
  have h12 := stitchAt 12 4 frame051scope04_s012 h16
  have h8 := stitchAt 8 4 frame051scope04_s008 h12
  have h4 := stitchAt 4 4 frame051scope04_s004 h8
  have h0 := stitchAt 0 4 frame051scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch04 : batch04.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope04

private abbrev frame051test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch05.stop,F)

private theorem frame051scope05_s000 : ((fits05.drop 0).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s004 : ((fits05.drop 4).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s008 : ((fits05.drop 8).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s012 : ((fits05.drop 12).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s016 : ((fits05.drop 16).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s020 : ((fits05.drop 20).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s024 : ((fits05.drop 24).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s028 : ((fits05.drop 28).take 4).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_s032 : ((fits05.drop 32).take 3).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05_end : (fits05.drop 35).all frame051test05=true := by
  decide +kernel

private theorem frame051scope05 : fits05.all frame051test05=true := by
  have h32 := stitchAt 32 3 frame051scope05_s032 frame051scope05_end
  have h28 := stitchAt 28 4 frame051scope05_s028 h32
  have h24 := stitchAt 24 4 frame051scope05_s024 h28
  have h20 := stitchAt 20 4 frame051scope05_s020 h24
  have h16 := stitchAt 16 4 frame051scope05_s016 h20
  have h12 := stitchAt 12 4 frame051scope05_s012 h16
  have h8 := stitchAt 8 4 frame051scope05_s008 h12
  have h4 := stitchAt 4 4 frame051scope05_s004 h8
  have h0 := stitchAt 0 4 frame051scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch05 : batch05.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope05

private abbrev frame051test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch06.stop,F)

private theorem frame051scope06_s000 : ((fits06.drop 0).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s004 : ((fits06.drop 4).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s008 : ((fits06.drop 8).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s012 : ((fits06.drop 12).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s016 : ((fits06.drop 16).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s020 : ((fits06.drop 20).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s024 : ((fits06.drop 24).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s028 : ((fits06.drop 28).take 4).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_s032 : ((fits06.drop 32).take 3).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06_end : (fits06.drop 35).all frame051test06=true := by
  decide +kernel

private theorem frame051scope06 : fits06.all frame051test06=true := by
  have h32 := stitchAt 32 3 frame051scope06_s032 frame051scope06_end
  have h28 := stitchAt 28 4 frame051scope06_s028 h32
  have h24 := stitchAt 24 4 frame051scope06_s024 h28
  have h20 := stitchAt 20 4 frame051scope06_s020 h24
  have h16 := stitchAt 16 4 frame051scope06_s016 h20
  have h12 := stitchAt 12 4 frame051scope06_s012 h16
  have h8 := stitchAt 8 4 frame051scope06_s008 h12
  have h4 := stitchAt 4 4 frame051scope06_s004 h8
  have h0 := stitchAt 0 4 frame051scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch06 : batch06.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope06

private abbrev frame051test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame108 (fun z => List.lookup (guideCode z) guide051)
    (batch07.stop,F)

private theorem frame051scope07_s000 : ((fits07.drop 0).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s004 : ((fits07.drop 4).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s008 : ((fits07.drop 8).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s012 : ((fits07.drop 12).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s016 : ((fits07.drop 16).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s020 : ((fits07.drop 20).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s024 : ((fits07.drop 24).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s028 : ((fits07.drop 28).take 4).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_s032 : ((fits07.drop 32).take 3).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07_end : (fits07.drop 35).all frame051test07=true := by
  decide +kernel

private theorem frame051scope07 : fits07.all frame051test07=true := by
  have h32 := stitchAt 32 3 frame051scope07_s032 frame051scope07_end
  have h28 := stitchAt 28 4 frame051scope07_s028 h32
  have h24 := stitchAt 24 4 frame051scope07_s024 h28
  have h20 := stitchAt 20 4 frame051scope07_s020 h24
  have h16 := stitchAt 16 4 frame051scope07_s016 h20
  have h12 := stitchAt 12 4 frame051scope07_s012 h16
  have h8 := stitchAt 8 4 frame051scope07_s008 h12
  have h4 := stitchAt 4 4 frame051scope07_s004 h8
  have h0 := stitchAt 0 4 frame051scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame051batch07 : batch07.pickTest original frame108=true :=
  FitBatch.pickTest_of_scoped scoped051 frame051scope07

private theorem frameBatches051 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame108)=true := by
  simp only [List.all_cons,List.all_nil,frame051batch00,frame051batch01,frame051batch02,frame051batch03,frame051batch04,frame051batch05,frame051batch06,frame051batch07,Bool.and_self]

theorem frameOK051 : frameRankTest original useStop frame108=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches051


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
