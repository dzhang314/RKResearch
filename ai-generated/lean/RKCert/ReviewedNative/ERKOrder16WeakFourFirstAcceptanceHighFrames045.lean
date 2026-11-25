module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK090 : stripTest frame181=true := by decide +kernel

theorem spanOK090 : checkChain 2032 2016 [frame181.span]=true := by decide +kernel

private theorem guideAt090 : List.lookup frame181.span.1 guideTable=some guide090 := by
  decide +kernel

private theorem scoped090 : original.guide frame181.span.1 =
    (fun z => List.lookup (guideCode z) guide090) := by
  funext z
  change (List.lookup frame181.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide090
  simp only [guideAt090,Option.bind_some]

private abbrev frame090test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch00.stop,F)

private theorem frame090scope00_s000 : ((fits00.drop 0).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s004 : ((fits00.drop 4).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s008 : ((fits00.drop 8).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s012 : ((fits00.drop 12).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s016 : ((fits00.drop 16).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s020 : ((fits00.drop 20).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s024 : ((fits00.drop 24).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s028 : ((fits00.drop 28).take 4).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_s032 : ((fits00.drop 32).take 3).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00_end : (fits00.drop 35).all frame090test00=true := by
  decide +kernel

private theorem frame090scope00 : fits00.all frame090test00=true := by
  have h32 := stitchAt 32 3 frame090scope00_s032 frame090scope00_end
  have h28 := stitchAt 28 4 frame090scope00_s028 h32
  have h24 := stitchAt 24 4 frame090scope00_s024 h28
  have h20 := stitchAt 20 4 frame090scope00_s020 h24
  have h16 := stitchAt 16 4 frame090scope00_s016 h20
  have h12 := stitchAt 12 4 frame090scope00_s012 h16
  have h8 := stitchAt 8 4 frame090scope00_s008 h12
  have h4 := stitchAt 4 4 frame090scope00_s004 h8
  have h0 := stitchAt 0 4 frame090scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch00 : batch00.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope00

private abbrev frame090test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch01.stop,F)

private theorem frame090scope01_s000 : ((fits01.drop 0).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s004 : ((fits01.drop 4).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s008 : ((fits01.drop 8).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s012 : ((fits01.drop 12).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s016 : ((fits01.drop 16).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s020 : ((fits01.drop 20).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s024 : ((fits01.drop 24).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s028 : ((fits01.drop 28).take 4).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_s032 : ((fits01.drop 32).take 3).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01_end : (fits01.drop 35).all frame090test01=true := by
  decide +kernel

private theorem frame090scope01 : fits01.all frame090test01=true := by
  have h32 := stitchAt 32 3 frame090scope01_s032 frame090scope01_end
  have h28 := stitchAt 28 4 frame090scope01_s028 h32
  have h24 := stitchAt 24 4 frame090scope01_s024 h28
  have h20 := stitchAt 20 4 frame090scope01_s020 h24
  have h16 := stitchAt 16 4 frame090scope01_s016 h20
  have h12 := stitchAt 12 4 frame090scope01_s012 h16
  have h8 := stitchAt 8 4 frame090scope01_s008 h12
  have h4 := stitchAt 4 4 frame090scope01_s004 h8
  have h0 := stitchAt 0 4 frame090scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch01 : batch01.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope01

private abbrev frame090test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch02.stop,F)

private theorem frame090scope02_s000 : ((fits02.drop 0).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s004 : ((fits02.drop 4).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s008 : ((fits02.drop 8).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s012 : ((fits02.drop 12).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s016 : ((fits02.drop 16).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s020 : ((fits02.drop 20).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s024 : ((fits02.drop 24).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s028 : ((fits02.drop 28).take 4).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_s032 : ((fits02.drop 32).take 3).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02_end : (fits02.drop 35).all frame090test02=true := by
  decide +kernel

private theorem frame090scope02 : fits02.all frame090test02=true := by
  have h32 := stitchAt 32 3 frame090scope02_s032 frame090scope02_end
  have h28 := stitchAt 28 4 frame090scope02_s028 h32
  have h24 := stitchAt 24 4 frame090scope02_s024 h28
  have h20 := stitchAt 20 4 frame090scope02_s020 h24
  have h16 := stitchAt 16 4 frame090scope02_s016 h20
  have h12 := stitchAt 12 4 frame090scope02_s012 h16
  have h8 := stitchAt 8 4 frame090scope02_s008 h12
  have h4 := stitchAt 4 4 frame090scope02_s004 h8
  have h0 := stitchAt 0 4 frame090scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch02 : batch02.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope02

private abbrev frame090test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch03.stop,F)

private theorem frame090scope03_s000 : ((fits03.drop 0).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s004 : ((fits03.drop 4).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s008 : ((fits03.drop 8).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s012 : ((fits03.drop 12).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s016 : ((fits03.drop 16).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s020 : ((fits03.drop 20).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s024 : ((fits03.drop 24).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s028 : ((fits03.drop 28).take 4).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_s032 : ((fits03.drop 32).take 3).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03_end : (fits03.drop 35).all frame090test03=true := by
  decide +kernel

private theorem frame090scope03 : fits03.all frame090test03=true := by
  have h32 := stitchAt 32 3 frame090scope03_s032 frame090scope03_end
  have h28 := stitchAt 28 4 frame090scope03_s028 h32
  have h24 := stitchAt 24 4 frame090scope03_s024 h28
  have h20 := stitchAt 20 4 frame090scope03_s020 h24
  have h16 := stitchAt 16 4 frame090scope03_s016 h20
  have h12 := stitchAt 12 4 frame090scope03_s012 h16
  have h8 := stitchAt 8 4 frame090scope03_s008 h12
  have h4 := stitchAt 4 4 frame090scope03_s004 h8
  have h0 := stitchAt 0 4 frame090scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch03 : batch03.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope03

private abbrev frame090test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch04.stop,F)

private theorem frame090scope04_s000 : ((fits04.drop 0).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s004 : ((fits04.drop 4).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s008 : ((fits04.drop 8).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s012 : ((fits04.drop 12).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s016 : ((fits04.drop 16).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s020 : ((fits04.drop 20).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s024 : ((fits04.drop 24).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s028 : ((fits04.drop 28).take 4).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_s032 : ((fits04.drop 32).take 3).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04_end : (fits04.drop 35).all frame090test04=true := by
  decide +kernel

private theorem frame090scope04 : fits04.all frame090test04=true := by
  have h32 := stitchAt 32 3 frame090scope04_s032 frame090scope04_end
  have h28 := stitchAt 28 4 frame090scope04_s028 h32
  have h24 := stitchAt 24 4 frame090scope04_s024 h28
  have h20 := stitchAt 20 4 frame090scope04_s020 h24
  have h16 := stitchAt 16 4 frame090scope04_s016 h20
  have h12 := stitchAt 12 4 frame090scope04_s012 h16
  have h8 := stitchAt 8 4 frame090scope04_s008 h12
  have h4 := stitchAt 4 4 frame090scope04_s004 h8
  have h0 := stitchAt 0 4 frame090scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch04 : batch04.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope04

private abbrev frame090test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch05.stop,F)

private theorem frame090scope05_s000 : ((fits05.drop 0).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s004 : ((fits05.drop 4).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s008 : ((fits05.drop 8).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s012 : ((fits05.drop 12).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s016 : ((fits05.drop 16).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s020 : ((fits05.drop 20).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s024 : ((fits05.drop 24).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s028 : ((fits05.drop 28).take 4).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_s032 : ((fits05.drop 32).take 3).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05_end : (fits05.drop 35).all frame090test05=true := by
  decide +kernel

private theorem frame090scope05 : fits05.all frame090test05=true := by
  have h32 := stitchAt 32 3 frame090scope05_s032 frame090scope05_end
  have h28 := stitchAt 28 4 frame090scope05_s028 h32
  have h24 := stitchAt 24 4 frame090scope05_s024 h28
  have h20 := stitchAt 20 4 frame090scope05_s020 h24
  have h16 := stitchAt 16 4 frame090scope05_s016 h20
  have h12 := stitchAt 12 4 frame090scope05_s012 h16
  have h8 := stitchAt 8 4 frame090scope05_s008 h12
  have h4 := stitchAt 4 4 frame090scope05_s004 h8
  have h0 := stitchAt 0 4 frame090scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch05 : batch05.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope05

private abbrev frame090test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch06.stop,F)

private theorem frame090scope06_s000 : ((fits06.drop 0).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s004 : ((fits06.drop 4).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s008 : ((fits06.drop 8).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s012 : ((fits06.drop 12).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s016 : ((fits06.drop 16).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s020 : ((fits06.drop 20).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s024 : ((fits06.drop 24).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s028 : ((fits06.drop 28).take 4).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_s032 : ((fits06.drop 32).take 3).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06_end : (fits06.drop 35).all frame090test06=true := by
  decide +kernel

private theorem frame090scope06 : fits06.all frame090test06=true := by
  have h32 := stitchAt 32 3 frame090scope06_s032 frame090scope06_end
  have h28 := stitchAt 28 4 frame090scope06_s028 h32
  have h24 := stitchAt 24 4 frame090scope06_s024 h28
  have h20 := stitchAt 20 4 frame090scope06_s020 h24
  have h16 := stitchAt 16 4 frame090scope06_s016 h20
  have h12 := stitchAt 12 4 frame090scope06_s012 h16
  have h8 := stitchAt 8 4 frame090scope06_s008 h12
  have h4 := stitchAt 4 4 frame090scope06_s004 h8
  have h0 := stitchAt 0 4 frame090scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch06 : batch06.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope06

private abbrev frame090test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame181 (fun z => List.lookup (guideCode z) guide090)
    (batch07.stop,F)

private theorem frame090scope07_s000 : ((fits07.drop 0).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s004 : ((fits07.drop 4).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s008 : ((fits07.drop 8).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s012 : ((fits07.drop 12).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s016 : ((fits07.drop 16).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s020 : ((fits07.drop 20).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s024 : ((fits07.drop 24).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s028 : ((fits07.drop 28).take 4).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_s032 : ((fits07.drop 32).take 3).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07_end : (fits07.drop 35).all frame090test07=true := by
  decide +kernel

private theorem frame090scope07 : fits07.all frame090test07=true := by
  have h32 := stitchAt 32 3 frame090scope07_s032 frame090scope07_end
  have h28 := stitchAt 28 4 frame090scope07_s028 h32
  have h24 := stitchAt 24 4 frame090scope07_s024 h28
  have h20 := stitchAt 20 4 frame090scope07_s020 h24
  have h16 := stitchAt 16 4 frame090scope07_s016 h20
  have h12 := stitchAt 12 4 frame090scope07_s012 h16
  have h8 := stitchAt 8 4 frame090scope07_s008 h12
  have h4 := stitchAt 4 4 frame090scope07_s004 h8
  have h0 := stitchAt 0 4 frame090scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame090batch07 : batch07.pickTest original frame181=true :=
  FitBatch.pickTest_of_scoped scoped090 frame090scope07

private theorem frameBatches090 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame181)=true := by
  simp only [List.all_cons,List.all_nil,frame090batch00,frame090batch01,frame090batch02,frame090batch03,frame090batch04,frame090batch05,frame090batch06,frame090batch07,Bool.and_self]

theorem frameOK090 : frameRankTest original useStop frame181=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches090

theorem stripOK091 : stripTest frame182=true := by decide +kernel

theorem spanOK091 : checkChain 2048 2032 [frame182.span]=true := by decide +kernel

private theorem guideAt091 : List.lookup frame182.span.1 guideTable=some guide091 := by
  decide +kernel

private theorem scoped091 : original.guide frame182.span.1 =
    (fun z => List.lookup (guideCode z) guide091) := by
  funext z
  change (List.lookup frame182.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide091
  simp only [guideAt091,Option.bind_some]

private abbrev frame091test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch00.stop,F)

private theorem frame091scope00_s000 : ((fits00.drop 0).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s004 : ((fits00.drop 4).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s008 : ((fits00.drop 8).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s012 : ((fits00.drop 12).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s016 : ((fits00.drop 16).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s020 : ((fits00.drop 20).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s024 : ((fits00.drop 24).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s028 : ((fits00.drop 28).take 4).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_s032 : ((fits00.drop 32).take 3).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00_end : (fits00.drop 35).all frame091test00=true := by
  decide +kernel

private theorem frame091scope00 : fits00.all frame091test00=true := by
  have h32 := stitchAt 32 3 frame091scope00_s032 frame091scope00_end
  have h28 := stitchAt 28 4 frame091scope00_s028 h32
  have h24 := stitchAt 24 4 frame091scope00_s024 h28
  have h20 := stitchAt 20 4 frame091scope00_s020 h24
  have h16 := stitchAt 16 4 frame091scope00_s016 h20
  have h12 := stitchAt 12 4 frame091scope00_s012 h16
  have h8 := stitchAt 8 4 frame091scope00_s008 h12
  have h4 := stitchAt 4 4 frame091scope00_s004 h8
  have h0 := stitchAt 0 4 frame091scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch00 : batch00.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope00

private abbrev frame091test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch01.stop,F)

private theorem frame091scope01_s000 : ((fits01.drop 0).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s004 : ((fits01.drop 4).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s008 : ((fits01.drop 8).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s012 : ((fits01.drop 12).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s016 : ((fits01.drop 16).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s020 : ((fits01.drop 20).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s024 : ((fits01.drop 24).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s028 : ((fits01.drop 28).take 4).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_s032 : ((fits01.drop 32).take 3).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01_end : (fits01.drop 35).all frame091test01=true := by
  decide +kernel

private theorem frame091scope01 : fits01.all frame091test01=true := by
  have h32 := stitchAt 32 3 frame091scope01_s032 frame091scope01_end
  have h28 := stitchAt 28 4 frame091scope01_s028 h32
  have h24 := stitchAt 24 4 frame091scope01_s024 h28
  have h20 := stitchAt 20 4 frame091scope01_s020 h24
  have h16 := stitchAt 16 4 frame091scope01_s016 h20
  have h12 := stitchAt 12 4 frame091scope01_s012 h16
  have h8 := stitchAt 8 4 frame091scope01_s008 h12
  have h4 := stitchAt 4 4 frame091scope01_s004 h8
  have h0 := stitchAt 0 4 frame091scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch01 : batch01.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope01

private abbrev frame091test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch02.stop,F)

private theorem frame091scope02_s000 : ((fits02.drop 0).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s004 : ((fits02.drop 4).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s008 : ((fits02.drop 8).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s012 : ((fits02.drop 12).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s016 : ((fits02.drop 16).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s020 : ((fits02.drop 20).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s024 : ((fits02.drop 24).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s028 : ((fits02.drop 28).take 4).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_s032 : ((fits02.drop 32).take 3).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02_end : (fits02.drop 35).all frame091test02=true := by
  decide +kernel

private theorem frame091scope02 : fits02.all frame091test02=true := by
  have h32 := stitchAt 32 3 frame091scope02_s032 frame091scope02_end
  have h28 := stitchAt 28 4 frame091scope02_s028 h32
  have h24 := stitchAt 24 4 frame091scope02_s024 h28
  have h20 := stitchAt 20 4 frame091scope02_s020 h24
  have h16 := stitchAt 16 4 frame091scope02_s016 h20
  have h12 := stitchAt 12 4 frame091scope02_s012 h16
  have h8 := stitchAt 8 4 frame091scope02_s008 h12
  have h4 := stitchAt 4 4 frame091scope02_s004 h8
  have h0 := stitchAt 0 4 frame091scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch02 : batch02.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope02

private abbrev frame091test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch03.stop,F)

private theorem frame091scope03_s000 : ((fits03.drop 0).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s004 : ((fits03.drop 4).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s008 : ((fits03.drop 8).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s012 : ((fits03.drop 12).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s016 : ((fits03.drop 16).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s020 : ((fits03.drop 20).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s024 : ((fits03.drop 24).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s028 : ((fits03.drop 28).take 4).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_s032 : ((fits03.drop 32).take 3).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03_end : (fits03.drop 35).all frame091test03=true := by
  decide +kernel

private theorem frame091scope03 : fits03.all frame091test03=true := by
  have h32 := stitchAt 32 3 frame091scope03_s032 frame091scope03_end
  have h28 := stitchAt 28 4 frame091scope03_s028 h32
  have h24 := stitchAt 24 4 frame091scope03_s024 h28
  have h20 := stitchAt 20 4 frame091scope03_s020 h24
  have h16 := stitchAt 16 4 frame091scope03_s016 h20
  have h12 := stitchAt 12 4 frame091scope03_s012 h16
  have h8 := stitchAt 8 4 frame091scope03_s008 h12
  have h4 := stitchAt 4 4 frame091scope03_s004 h8
  have h0 := stitchAt 0 4 frame091scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch03 : batch03.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope03

private abbrev frame091test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch04.stop,F)

private theorem frame091scope04_s000 : ((fits04.drop 0).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s004 : ((fits04.drop 4).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s008 : ((fits04.drop 8).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s012 : ((fits04.drop 12).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s016 : ((fits04.drop 16).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s020 : ((fits04.drop 20).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s024 : ((fits04.drop 24).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s028 : ((fits04.drop 28).take 4).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_s032 : ((fits04.drop 32).take 3).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04_end : (fits04.drop 35).all frame091test04=true := by
  decide +kernel

private theorem frame091scope04 : fits04.all frame091test04=true := by
  have h32 := stitchAt 32 3 frame091scope04_s032 frame091scope04_end
  have h28 := stitchAt 28 4 frame091scope04_s028 h32
  have h24 := stitchAt 24 4 frame091scope04_s024 h28
  have h20 := stitchAt 20 4 frame091scope04_s020 h24
  have h16 := stitchAt 16 4 frame091scope04_s016 h20
  have h12 := stitchAt 12 4 frame091scope04_s012 h16
  have h8 := stitchAt 8 4 frame091scope04_s008 h12
  have h4 := stitchAt 4 4 frame091scope04_s004 h8
  have h0 := stitchAt 0 4 frame091scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch04 : batch04.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope04

private abbrev frame091test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch05.stop,F)

private theorem frame091scope05_s000 : ((fits05.drop 0).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s004 : ((fits05.drop 4).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s008 : ((fits05.drop 8).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s012 : ((fits05.drop 12).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s016 : ((fits05.drop 16).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s020 : ((fits05.drop 20).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s024 : ((fits05.drop 24).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s028 : ((fits05.drop 28).take 4).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_s032 : ((fits05.drop 32).take 3).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05_end : (fits05.drop 35).all frame091test05=true := by
  decide +kernel

private theorem frame091scope05 : fits05.all frame091test05=true := by
  have h32 := stitchAt 32 3 frame091scope05_s032 frame091scope05_end
  have h28 := stitchAt 28 4 frame091scope05_s028 h32
  have h24 := stitchAt 24 4 frame091scope05_s024 h28
  have h20 := stitchAt 20 4 frame091scope05_s020 h24
  have h16 := stitchAt 16 4 frame091scope05_s016 h20
  have h12 := stitchAt 12 4 frame091scope05_s012 h16
  have h8 := stitchAt 8 4 frame091scope05_s008 h12
  have h4 := stitchAt 4 4 frame091scope05_s004 h8
  have h0 := stitchAt 0 4 frame091scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch05 : batch05.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope05

private abbrev frame091test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch06.stop,F)

private theorem frame091scope06_s000 : ((fits06.drop 0).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s004 : ((fits06.drop 4).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s008 : ((fits06.drop 8).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s012 : ((fits06.drop 12).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s016 : ((fits06.drop 16).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s020 : ((fits06.drop 20).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s024 : ((fits06.drop 24).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s028 : ((fits06.drop 28).take 4).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_s032 : ((fits06.drop 32).take 3).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06_end : (fits06.drop 35).all frame091test06=true := by
  decide +kernel

private theorem frame091scope06 : fits06.all frame091test06=true := by
  have h32 := stitchAt 32 3 frame091scope06_s032 frame091scope06_end
  have h28 := stitchAt 28 4 frame091scope06_s028 h32
  have h24 := stitchAt 24 4 frame091scope06_s024 h28
  have h20 := stitchAt 20 4 frame091scope06_s020 h24
  have h16 := stitchAt 16 4 frame091scope06_s016 h20
  have h12 := stitchAt 12 4 frame091scope06_s012 h16
  have h8 := stitchAt 8 4 frame091scope06_s008 h12
  have h4 := stitchAt 4 4 frame091scope06_s004 h8
  have h0 := stitchAt 0 4 frame091scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch06 : batch06.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope06

private abbrev frame091test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame182 (fun z => List.lookup (guideCode z) guide091)
    (batch07.stop,F)

private theorem frame091scope07_s000 : ((fits07.drop 0).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s004 : ((fits07.drop 4).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s008 : ((fits07.drop 8).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s012 : ((fits07.drop 12).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s016 : ((fits07.drop 16).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s020 : ((fits07.drop 20).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s024 : ((fits07.drop 24).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s028 : ((fits07.drop 28).take 4).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_s032 : ((fits07.drop 32).take 3).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07_end : (fits07.drop 35).all frame091test07=true := by
  decide +kernel

private theorem frame091scope07 : fits07.all frame091test07=true := by
  have h32 := stitchAt 32 3 frame091scope07_s032 frame091scope07_end
  have h28 := stitchAt 28 4 frame091scope07_s028 h32
  have h24 := stitchAt 24 4 frame091scope07_s024 h28
  have h20 := stitchAt 20 4 frame091scope07_s020 h24
  have h16 := stitchAt 16 4 frame091scope07_s016 h20
  have h12 := stitchAt 12 4 frame091scope07_s012 h16
  have h8 := stitchAt 8 4 frame091scope07_s008 h12
  have h4 := stitchAt 4 4 frame091scope07_s004 h8
  have h0 := stitchAt 0 4 frame091scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame091batch07 : batch07.pickTest original frame182=true :=
  FitBatch.pickTest_of_scoped scoped091 frame091scope07

private theorem frameBatches091 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame182)=true := by
  simp only [List.all_cons,List.all_nil,frame091batch00,frame091batch01,frame091batch02,frame091batch03,frame091batch04,frame091batch05,frame091batch06,frame091batch07,Bool.and_self]

theorem frameOK091 : frameRankTest original useStop frame182=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches091


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
