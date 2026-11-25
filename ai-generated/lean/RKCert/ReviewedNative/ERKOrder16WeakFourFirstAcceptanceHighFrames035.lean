module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK070 : stripTest frame145=true := by decide +kernel

theorem spanOK070 : checkChain 1804 1800 [frame145.span]=true := by decide +kernel

private theorem guideAt070 : List.lookup frame145.span.1 guideTable=some guide070 := by
  decide +kernel

private theorem scoped070 : original.guide frame145.span.1 =
    (fun z => List.lookup (guideCode z) guide070) := by
  funext z
  change (List.lookup frame145.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide070
  simp only [guideAt070,Option.bind_some]

private abbrev frame070test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch00.stop,F)

private theorem frame070scope00_s000 : ((fits00.drop 0).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s004 : ((fits00.drop 4).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s008 : ((fits00.drop 8).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s012 : ((fits00.drop 12).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s016 : ((fits00.drop 16).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s020 : ((fits00.drop 20).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s024 : ((fits00.drop 24).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s028 : ((fits00.drop 28).take 4).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_s032 : ((fits00.drop 32).take 3).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00_end : (fits00.drop 35).all frame070test00=true := by
  decide +kernel

private theorem frame070scope00 : fits00.all frame070test00=true := by
  have h32 := stitchAt 32 3 frame070scope00_s032 frame070scope00_end
  have h28 := stitchAt 28 4 frame070scope00_s028 h32
  have h24 := stitchAt 24 4 frame070scope00_s024 h28
  have h20 := stitchAt 20 4 frame070scope00_s020 h24
  have h16 := stitchAt 16 4 frame070scope00_s016 h20
  have h12 := stitchAt 12 4 frame070scope00_s012 h16
  have h8 := stitchAt 8 4 frame070scope00_s008 h12
  have h4 := stitchAt 4 4 frame070scope00_s004 h8
  have h0 := stitchAt 0 4 frame070scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch00 : batch00.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope00

private abbrev frame070test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch01.stop,F)

private theorem frame070scope01_s000 : ((fits01.drop 0).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s004 : ((fits01.drop 4).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s008 : ((fits01.drop 8).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s012 : ((fits01.drop 12).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s016 : ((fits01.drop 16).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s020 : ((fits01.drop 20).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s024 : ((fits01.drop 24).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s028 : ((fits01.drop 28).take 4).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_s032 : ((fits01.drop 32).take 3).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01_end : (fits01.drop 35).all frame070test01=true := by
  decide +kernel

private theorem frame070scope01 : fits01.all frame070test01=true := by
  have h32 := stitchAt 32 3 frame070scope01_s032 frame070scope01_end
  have h28 := stitchAt 28 4 frame070scope01_s028 h32
  have h24 := stitchAt 24 4 frame070scope01_s024 h28
  have h20 := stitchAt 20 4 frame070scope01_s020 h24
  have h16 := stitchAt 16 4 frame070scope01_s016 h20
  have h12 := stitchAt 12 4 frame070scope01_s012 h16
  have h8 := stitchAt 8 4 frame070scope01_s008 h12
  have h4 := stitchAt 4 4 frame070scope01_s004 h8
  have h0 := stitchAt 0 4 frame070scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch01 : batch01.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope01

private abbrev frame070test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch02.stop,F)

private theorem frame070scope02_s000 : ((fits02.drop 0).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s004 : ((fits02.drop 4).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s008 : ((fits02.drop 8).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s012 : ((fits02.drop 12).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s016 : ((fits02.drop 16).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s020 : ((fits02.drop 20).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s024 : ((fits02.drop 24).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s028 : ((fits02.drop 28).take 4).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_s032 : ((fits02.drop 32).take 3).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02_end : (fits02.drop 35).all frame070test02=true := by
  decide +kernel

private theorem frame070scope02 : fits02.all frame070test02=true := by
  have h32 := stitchAt 32 3 frame070scope02_s032 frame070scope02_end
  have h28 := stitchAt 28 4 frame070scope02_s028 h32
  have h24 := stitchAt 24 4 frame070scope02_s024 h28
  have h20 := stitchAt 20 4 frame070scope02_s020 h24
  have h16 := stitchAt 16 4 frame070scope02_s016 h20
  have h12 := stitchAt 12 4 frame070scope02_s012 h16
  have h8 := stitchAt 8 4 frame070scope02_s008 h12
  have h4 := stitchAt 4 4 frame070scope02_s004 h8
  have h0 := stitchAt 0 4 frame070scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch02 : batch02.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope02

private abbrev frame070test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch03.stop,F)

private theorem frame070scope03_s000 : ((fits03.drop 0).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s004 : ((fits03.drop 4).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s008 : ((fits03.drop 8).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s012 : ((fits03.drop 12).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s016 : ((fits03.drop 16).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s020 : ((fits03.drop 20).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s024 : ((fits03.drop 24).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s028 : ((fits03.drop 28).take 4).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_s032 : ((fits03.drop 32).take 3).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03_end : (fits03.drop 35).all frame070test03=true := by
  decide +kernel

private theorem frame070scope03 : fits03.all frame070test03=true := by
  have h32 := stitchAt 32 3 frame070scope03_s032 frame070scope03_end
  have h28 := stitchAt 28 4 frame070scope03_s028 h32
  have h24 := stitchAt 24 4 frame070scope03_s024 h28
  have h20 := stitchAt 20 4 frame070scope03_s020 h24
  have h16 := stitchAt 16 4 frame070scope03_s016 h20
  have h12 := stitchAt 12 4 frame070scope03_s012 h16
  have h8 := stitchAt 8 4 frame070scope03_s008 h12
  have h4 := stitchAt 4 4 frame070scope03_s004 h8
  have h0 := stitchAt 0 4 frame070scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch03 : batch03.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope03

private abbrev frame070test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch04.stop,F)

private theorem frame070scope04_s000 : ((fits04.drop 0).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s004 : ((fits04.drop 4).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s008 : ((fits04.drop 8).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s012 : ((fits04.drop 12).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s016 : ((fits04.drop 16).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s020 : ((fits04.drop 20).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s024 : ((fits04.drop 24).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s028 : ((fits04.drop 28).take 4).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_s032 : ((fits04.drop 32).take 3).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04_end : (fits04.drop 35).all frame070test04=true := by
  decide +kernel

private theorem frame070scope04 : fits04.all frame070test04=true := by
  have h32 := stitchAt 32 3 frame070scope04_s032 frame070scope04_end
  have h28 := stitchAt 28 4 frame070scope04_s028 h32
  have h24 := stitchAt 24 4 frame070scope04_s024 h28
  have h20 := stitchAt 20 4 frame070scope04_s020 h24
  have h16 := stitchAt 16 4 frame070scope04_s016 h20
  have h12 := stitchAt 12 4 frame070scope04_s012 h16
  have h8 := stitchAt 8 4 frame070scope04_s008 h12
  have h4 := stitchAt 4 4 frame070scope04_s004 h8
  have h0 := stitchAt 0 4 frame070scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch04 : batch04.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope04

private abbrev frame070test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch05.stop,F)

private theorem frame070scope05_s000 : ((fits05.drop 0).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s004 : ((fits05.drop 4).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s008 : ((fits05.drop 8).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s012 : ((fits05.drop 12).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s016 : ((fits05.drop 16).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s020 : ((fits05.drop 20).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s024 : ((fits05.drop 24).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s028 : ((fits05.drop 28).take 4).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_s032 : ((fits05.drop 32).take 3).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05_end : (fits05.drop 35).all frame070test05=true := by
  decide +kernel

private theorem frame070scope05 : fits05.all frame070test05=true := by
  have h32 := stitchAt 32 3 frame070scope05_s032 frame070scope05_end
  have h28 := stitchAt 28 4 frame070scope05_s028 h32
  have h24 := stitchAt 24 4 frame070scope05_s024 h28
  have h20 := stitchAt 20 4 frame070scope05_s020 h24
  have h16 := stitchAt 16 4 frame070scope05_s016 h20
  have h12 := stitchAt 12 4 frame070scope05_s012 h16
  have h8 := stitchAt 8 4 frame070scope05_s008 h12
  have h4 := stitchAt 4 4 frame070scope05_s004 h8
  have h0 := stitchAt 0 4 frame070scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch05 : batch05.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope05

private abbrev frame070test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch06.stop,F)

private theorem frame070scope06_s000 : ((fits06.drop 0).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s004 : ((fits06.drop 4).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s008 : ((fits06.drop 8).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s012 : ((fits06.drop 12).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s016 : ((fits06.drop 16).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s020 : ((fits06.drop 20).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s024 : ((fits06.drop 24).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s028 : ((fits06.drop 28).take 4).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_s032 : ((fits06.drop 32).take 3).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06_end : (fits06.drop 35).all frame070test06=true := by
  decide +kernel

private theorem frame070scope06 : fits06.all frame070test06=true := by
  have h32 := stitchAt 32 3 frame070scope06_s032 frame070scope06_end
  have h28 := stitchAt 28 4 frame070scope06_s028 h32
  have h24 := stitchAt 24 4 frame070scope06_s024 h28
  have h20 := stitchAt 20 4 frame070scope06_s020 h24
  have h16 := stitchAt 16 4 frame070scope06_s016 h20
  have h12 := stitchAt 12 4 frame070scope06_s012 h16
  have h8 := stitchAt 8 4 frame070scope06_s008 h12
  have h4 := stitchAt 4 4 frame070scope06_s004 h8
  have h0 := stitchAt 0 4 frame070scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch06 : batch06.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope06

private abbrev frame070test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame145 (fun z => List.lookup (guideCode z) guide070)
    (batch07.stop,F)

private theorem frame070scope07_s000 : ((fits07.drop 0).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s004 : ((fits07.drop 4).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s008 : ((fits07.drop 8).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s012 : ((fits07.drop 12).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s016 : ((fits07.drop 16).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s020 : ((fits07.drop 20).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s024 : ((fits07.drop 24).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s028 : ((fits07.drop 28).take 4).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_s032 : ((fits07.drop 32).take 3).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07_end : (fits07.drop 35).all frame070test07=true := by
  decide +kernel

private theorem frame070scope07 : fits07.all frame070test07=true := by
  have h32 := stitchAt 32 3 frame070scope07_s032 frame070scope07_end
  have h28 := stitchAt 28 4 frame070scope07_s028 h32
  have h24 := stitchAt 24 4 frame070scope07_s024 h28
  have h20 := stitchAt 20 4 frame070scope07_s020 h24
  have h16 := stitchAt 16 4 frame070scope07_s016 h20
  have h12 := stitchAt 12 4 frame070scope07_s012 h16
  have h8 := stitchAt 8 4 frame070scope07_s008 h12
  have h4 := stitchAt 4 4 frame070scope07_s004 h8
  have h0 := stitchAt 0 4 frame070scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame070batch07 : batch07.pickTest original frame145=true :=
  FitBatch.pickTest_of_scoped scoped070 frame070scope07

private theorem frameBatches070 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame145)=true := by
  simp only [List.all_cons,List.all_nil,frame070batch00,frame070batch01,frame070batch02,frame070batch03,frame070batch04,frame070batch05,frame070batch06,frame070batch07,Bool.and_self]

theorem frameOK070 : frameRankTest original useStop frame145=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches070

theorem stripOK071 : stripTest frame146=true := by decide +kernel

theorem spanOK071 : checkChain 1808 1804 [frame146.span]=true := by decide +kernel

private theorem guideAt071 : List.lookup frame146.span.1 guideTable=some guide071 := by
  decide +kernel

private theorem scoped071 : original.guide frame146.span.1 =
    (fun z => List.lookup (guideCode z) guide071) := by
  funext z
  change (List.lookup frame146.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide071
  simp only [guideAt071,Option.bind_some]

private abbrev frame071test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch00.stop,F)

private theorem frame071scope00_s000 : ((fits00.drop 0).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s004 : ((fits00.drop 4).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s008 : ((fits00.drop 8).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s012 : ((fits00.drop 12).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s016 : ((fits00.drop 16).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s020 : ((fits00.drop 20).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s024 : ((fits00.drop 24).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s028 : ((fits00.drop 28).take 4).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_s032 : ((fits00.drop 32).take 3).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00_end : (fits00.drop 35).all frame071test00=true := by
  decide +kernel

private theorem frame071scope00 : fits00.all frame071test00=true := by
  have h32 := stitchAt 32 3 frame071scope00_s032 frame071scope00_end
  have h28 := stitchAt 28 4 frame071scope00_s028 h32
  have h24 := stitchAt 24 4 frame071scope00_s024 h28
  have h20 := stitchAt 20 4 frame071scope00_s020 h24
  have h16 := stitchAt 16 4 frame071scope00_s016 h20
  have h12 := stitchAt 12 4 frame071scope00_s012 h16
  have h8 := stitchAt 8 4 frame071scope00_s008 h12
  have h4 := stitchAt 4 4 frame071scope00_s004 h8
  have h0 := stitchAt 0 4 frame071scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch00 : batch00.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope00

private abbrev frame071test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch01.stop,F)

private theorem frame071scope01_s000 : ((fits01.drop 0).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s004 : ((fits01.drop 4).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s008 : ((fits01.drop 8).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s012 : ((fits01.drop 12).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s016 : ((fits01.drop 16).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s020 : ((fits01.drop 20).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s024 : ((fits01.drop 24).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s028 : ((fits01.drop 28).take 4).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_s032 : ((fits01.drop 32).take 3).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01_end : (fits01.drop 35).all frame071test01=true := by
  decide +kernel

private theorem frame071scope01 : fits01.all frame071test01=true := by
  have h32 := stitchAt 32 3 frame071scope01_s032 frame071scope01_end
  have h28 := stitchAt 28 4 frame071scope01_s028 h32
  have h24 := stitchAt 24 4 frame071scope01_s024 h28
  have h20 := stitchAt 20 4 frame071scope01_s020 h24
  have h16 := stitchAt 16 4 frame071scope01_s016 h20
  have h12 := stitchAt 12 4 frame071scope01_s012 h16
  have h8 := stitchAt 8 4 frame071scope01_s008 h12
  have h4 := stitchAt 4 4 frame071scope01_s004 h8
  have h0 := stitchAt 0 4 frame071scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch01 : batch01.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope01

private abbrev frame071test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch02.stop,F)

private theorem frame071scope02_s000 : ((fits02.drop 0).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s004 : ((fits02.drop 4).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s008 : ((fits02.drop 8).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s012 : ((fits02.drop 12).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s016 : ((fits02.drop 16).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s020 : ((fits02.drop 20).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s024 : ((fits02.drop 24).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s028 : ((fits02.drop 28).take 4).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_s032 : ((fits02.drop 32).take 3).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02_end : (fits02.drop 35).all frame071test02=true := by
  decide +kernel

private theorem frame071scope02 : fits02.all frame071test02=true := by
  have h32 := stitchAt 32 3 frame071scope02_s032 frame071scope02_end
  have h28 := stitchAt 28 4 frame071scope02_s028 h32
  have h24 := stitchAt 24 4 frame071scope02_s024 h28
  have h20 := stitchAt 20 4 frame071scope02_s020 h24
  have h16 := stitchAt 16 4 frame071scope02_s016 h20
  have h12 := stitchAt 12 4 frame071scope02_s012 h16
  have h8 := stitchAt 8 4 frame071scope02_s008 h12
  have h4 := stitchAt 4 4 frame071scope02_s004 h8
  have h0 := stitchAt 0 4 frame071scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch02 : batch02.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope02

private abbrev frame071test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch03.stop,F)

private theorem frame071scope03_s000 : ((fits03.drop 0).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s004 : ((fits03.drop 4).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s008 : ((fits03.drop 8).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s012 : ((fits03.drop 12).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s016 : ((fits03.drop 16).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s020 : ((fits03.drop 20).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s024 : ((fits03.drop 24).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s028 : ((fits03.drop 28).take 4).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_s032 : ((fits03.drop 32).take 3).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03_end : (fits03.drop 35).all frame071test03=true := by
  decide +kernel

private theorem frame071scope03 : fits03.all frame071test03=true := by
  have h32 := stitchAt 32 3 frame071scope03_s032 frame071scope03_end
  have h28 := stitchAt 28 4 frame071scope03_s028 h32
  have h24 := stitchAt 24 4 frame071scope03_s024 h28
  have h20 := stitchAt 20 4 frame071scope03_s020 h24
  have h16 := stitchAt 16 4 frame071scope03_s016 h20
  have h12 := stitchAt 12 4 frame071scope03_s012 h16
  have h8 := stitchAt 8 4 frame071scope03_s008 h12
  have h4 := stitchAt 4 4 frame071scope03_s004 h8
  have h0 := stitchAt 0 4 frame071scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch03 : batch03.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope03

private abbrev frame071test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch04.stop,F)

private theorem frame071scope04_s000 : ((fits04.drop 0).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s004 : ((fits04.drop 4).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s008 : ((fits04.drop 8).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s012 : ((fits04.drop 12).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s016 : ((fits04.drop 16).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s020 : ((fits04.drop 20).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s024 : ((fits04.drop 24).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s028 : ((fits04.drop 28).take 4).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_s032 : ((fits04.drop 32).take 3).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04_end : (fits04.drop 35).all frame071test04=true := by
  decide +kernel

private theorem frame071scope04 : fits04.all frame071test04=true := by
  have h32 := stitchAt 32 3 frame071scope04_s032 frame071scope04_end
  have h28 := stitchAt 28 4 frame071scope04_s028 h32
  have h24 := stitchAt 24 4 frame071scope04_s024 h28
  have h20 := stitchAt 20 4 frame071scope04_s020 h24
  have h16 := stitchAt 16 4 frame071scope04_s016 h20
  have h12 := stitchAt 12 4 frame071scope04_s012 h16
  have h8 := stitchAt 8 4 frame071scope04_s008 h12
  have h4 := stitchAt 4 4 frame071scope04_s004 h8
  have h0 := stitchAt 0 4 frame071scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch04 : batch04.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope04

private abbrev frame071test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch05.stop,F)

private theorem frame071scope05_s000 : ((fits05.drop 0).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s004 : ((fits05.drop 4).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s008 : ((fits05.drop 8).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s012 : ((fits05.drop 12).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s016 : ((fits05.drop 16).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s020 : ((fits05.drop 20).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s024 : ((fits05.drop 24).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s028 : ((fits05.drop 28).take 4).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_s032 : ((fits05.drop 32).take 3).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05_end : (fits05.drop 35).all frame071test05=true := by
  decide +kernel

private theorem frame071scope05 : fits05.all frame071test05=true := by
  have h32 := stitchAt 32 3 frame071scope05_s032 frame071scope05_end
  have h28 := stitchAt 28 4 frame071scope05_s028 h32
  have h24 := stitchAt 24 4 frame071scope05_s024 h28
  have h20 := stitchAt 20 4 frame071scope05_s020 h24
  have h16 := stitchAt 16 4 frame071scope05_s016 h20
  have h12 := stitchAt 12 4 frame071scope05_s012 h16
  have h8 := stitchAt 8 4 frame071scope05_s008 h12
  have h4 := stitchAt 4 4 frame071scope05_s004 h8
  have h0 := stitchAt 0 4 frame071scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch05 : batch05.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope05

private abbrev frame071test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch06.stop,F)

private theorem frame071scope06_s000 : ((fits06.drop 0).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s004 : ((fits06.drop 4).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s008 : ((fits06.drop 8).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s012 : ((fits06.drop 12).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s016 : ((fits06.drop 16).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s020 : ((fits06.drop 20).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s024 : ((fits06.drop 24).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s028 : ((fits06.drop 28).take 4).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_s032 : ((fits06.drop 32).take 3).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06_end : (fits06.drop 35).all frame071test06=true := by
  decide +kernel

private theorem frame071scope06 : fits06.all frame071test06=true := by
  have h32 := stitchAt 32 3 frame071scope06_s032 frame071scope06_end
  have h28 := stitchAt 28 4 frame071scope06_s028 h32
  have h24 := stitchAt 24 4 frame071scope06_s024 h28
  have h20 := stitchAt 20 4 frame071scope06_s020 h24
  have h16 := stitchAt 16 4 frame071scope06_s016 h20
  have h12 := stitchAt 12 4 frame071scope06_s012 h16
  have h8 := stitchAt 8 4 frame071scope06_s008 h12
  have h4 := stitchAt 4 4 frame071scope06_s004 h8
  have h0 := stitchAt 0 4 frame071scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch06 : batch06.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope06

private abbrev frame071test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame146 (fun z => List.lookup (guideCode z) guide071)
    (batch07.stop,F)

private theorem frame071scope07_s000 : ((fits07.drop 0).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s004 : ((fits07.drop 4).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s008 : ((fits07.drop 8).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s012 : ((fits07.drop 12).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s016 : ((fits07.drop 16).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s020 : ((fits07.drop 20).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s024 : ((fits07.drop 24).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s028 : ((fits07.drop 28).take 4).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_s032 : ((fits07.drop 32).take 3).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07_end : (fits07.drop 35).all frame071test07=true := by
  decide +kernel

private theorem frame071scope07 : fits07.all frame071test07=true := by
  have h32 := stitchAt 32 3 frame071scope07_s032 frame071scope07_end
  have h28 := stitchAt 28 4 frame071scope07_s028 h32
  have h24 := stitchAt 24 4 frame071scope07_s024 h28
  have h20 := stitchAt 20 4 frame071scope07_s020 h24
  have h16 := stitchAt 16 4 frame071scope07_s016 h20
  have h12 := stitchAt 12 4 frame071scope07_s012 h16
  have h8 := stitchAt 8 4 frame071scope07_s008 h12
  have h4 := stitchAt 4 4 frame071scope07_s004 h8
  have h0 := stitchAt 0 4 frame071scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame071batch07 : batch07.pickTest original frame146=true :=
  FitBatch.pickTest_of_scoped scoped071 frame071scope07

private theorem frameBatches071 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame146)=true := by
  simp only [List.all_cons,List.all_nil,frame071batch00,frame071batch01,frame071batch02,frame071batch03,frame071batch04,frame071batch05,frame071batch06,frame071batch07,Bool.and_self]

theorem frameOK071 : frameRankTest original useStop frame146=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches071


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
