module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK076 : stripTest frame155=true := by decide +kernel

theorem spanOK076 : checkChain 1848 1840 [frame155.span]=true := by decide +kernel

private theorem guideAt076 : List.lookup frame155.span.1 guideTable=some guide076 := by
  decide +kernel

private theorem scoped076 : original.guide frame155.span.1 =
    (fun z => List.lookup (guideCode z) guide076) := by
  funext z
  change (List.lookup frame155.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide076
  simp only [guideAt076,Option.bind_some]

private abbrev frame076test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch00.stop,F)

private theorem frame076scope00_s000 : ((fits00.drop 0).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s004 : ((fits00.drop 4).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s008 : ((fits00.drop 8).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s012 : ((fits00.drop 12).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s016 : ((fits00.drop 16).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s020 : ((fits00.drop 20).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s024 : ((fits00.drop 24).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s028 : ((fits00.drop 28).take 4).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_s032 : ((fits00.drop 32).take 3).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00_end : (fits00.drop 35).all frame076test00=true := by
  decide +kernel

private theorem frame076scope00 : fits00.all frame076test00=true := by
  have h32 := stitchAt 32 3 frame076scope00_s032 frame076scope00_end
  have h28 := stitchAt 28 4 frame076scope00_s028 h32
  have h24 := stitchAt 24 4 frame076scope00_s024 h28
  have h20 := stitchAt 20 4 frame076scope00_s020 h24
  have h16 := stitchAt 16 4 frame076scope00_s016 h20
  have h12 := stitchAt 12 4 frame076scope00_s012 h16
  have h8 := stitchAt 8 4 frame076scope00_s008 h12
  have h4 := stitchAt 4 4 frame076scope00_s004 h8
  have h0 := stitchAt 0 4 frame076scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch00 : batch00.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope00

private abbrev frame076test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch01.stop,F)

private theorem frame076scope01_s000 : ((fits01.drop 0).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s004 : ((fits01.drop 4).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s008 : ((fits01.drop 8).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s012 : ((fits01.drop 12).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s016 : ((fits01.drop 16).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s020 : ((fits01.drop 20).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s024 : ((fits01.drop 24).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s028 : ((fits01.drop 28).take 4).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_s032 : ((fits01.drop 32).take 3).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01_end : (fits01.drop 35).all frame076test01=true := by
  decide +kernel

private theorem frame076scope01 : fits01.all frame076test01=true := by
  have h32 := stitchAt 32 3 frame076scope01_s032 frame076scope01_end
  have h28 := stitchAt 28 4 frame076scope01_s028 h32
  have h24 := stitchAt 24 4 frame076scope01_s024 h28
  have h20 := stitchAt 20 4 frame076scope01_s020 h24
  have h16 := stitchAt 16 4 frame076scope01_s016 h20
  have h12 := stitchAt 12 4 frame076scope01_s012 h16
  have h8 := stitchAt 8 4 frame076scope01_s008 h12
  have h4 := stitchAt 4 4 frame076scope01_s004 h8
  have h0 := stitchAt 0 4 frame076scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch01 : batch01.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope01

private abbrev frame076test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch02.stop,F)

private theorem frame076scope02_s000 : ((fits02.drop 0).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s004 : ((fits02.drop 4).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s008 : ((fits02.drop 8).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s012 : ((fits02.drop 12).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s016 : ((fits02.drop 16).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s020 : ((fits02.drop 20).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s024 : ((fits02.drop 24).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s028 : ((fits02.drop 28).take 4).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_s032 : ((fits02.drop 32).take 3).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02_end : (fits02.drop 35).all frame076test02=true := by
  decide +kernel

private theorem frame076scope02 : fits02.all frame076test02=true := by
  have h32 := stitchAt 32 3 frame076scope02_s032 frame076scope02_end
  have h28 := stitchAt 28 4 frame076scope02_s028 h32
  have h24 := stitchAt 24 4 frame076scope02_s024 h28
  have h20 := stitchAt 20 4 frame076scope02_s020 h24
  have h16 := stitchAt 16 4 frame076scope02_s016 h20
  have h12 := stitchAt 12 4 frame076scope02_s012 h16
  have h8 := stitchAt 8 4 frame076scope02_s008 h12
  have h4 := stitchAt 4 4 frame076scope02_s004 h8
  have h0 := stitchAt 0 4 frame076scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch02 : batch02.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope02

private abbrev frame076test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch03.stop,F)

private theorem frame076scope03_s000 : ((fits03.drop 0).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s004 : ((fits03.drop 4).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s008 : ((fits03.drop 8).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s012 : ((fits03.drop 12).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s016 : ((fits03.drop 16).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s020 : ((fits03.drop 20).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s024 : ((fits03.drop 24).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s028 : ((fits03.drop 28).take 4).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_s032 : ((fits03.drop 32).take 3).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03_end : (fits03.drop 35).all frame076test03=true := by
  decide +kernel

private theorem frame076scope03 : fits03.all frame076test03=true := by
  have h32 := stitchAt 32 3 frame076scope03_s032 frame076scope03_end
  have h28 := stitchAt 28 4 frame076scope03_s028 h32
  have h24 := stitchAt 24 4 frame076scope03_s024 h28
  have h20 := stitchAt 20 4 frame076scope03_s020 h24
  have h16 := stitchAt 16 4 frame076scope03_s016 h20
  have h12 := stitchAt 12 4 frame076scope03_s012 h16
  have h8 := stitchAt 8 4 frame076scope03_s008 h12
  have h4 := stitchAt 4 4 frame076scope03_s004 h8
  have h0 := stitchAt 0 4 frame076scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch03 : batch03.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope03

private abbrev frame076test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch04.stop,F)

private theorem frame076scope04_s000 : ((fits04.drop 0).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s004 : ((fits04.drop 4).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s008 : ((fits04.drop 8).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s012 : ((fits04.drop 12).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s016 : ((fits04.drop 16).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s020 : ((fits04.drop 20).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s024 : ((fits04.drop 24).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s028 : ((fits04.drop 28).take 4).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_s032 : ((fits04.drop 32).take 3).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04_end : (fits04.drop 35).all frame076test04=true := by
  decide +kernel

private theorem frame076scope04 : fits04.all frame076test04=true := by
  have h32 := stitchAt 32 3 frame076scope04_s032 frame076scope04_end
  have h28 := stitchAt 28 4 frame076scope04_s028 h32
  have h24 := stitchAt 24 4 frame076scope04_s024 h28
  have h20 := stitchAt 20 4 frame076scope04_s020 h24
  have h16 := stitchAt 16 4 frame076scope04_s016 h20
  have h12 := stitchAt 12 4 frame076scope04_s012 h16
  have h8 := stitchAt 8 4 frame076scope04_s008 h12
  have h4 := stitchAt 4 4 frame076scope04_s004 h8
  have h0 := stitchAt 0 4 frame076scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch04 : batch04.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope04

private abbrev frame076test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch05.stop,F)

private theorem frame076scope05_s000 : ((fits05.drop 0).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s004 : ((fits05.drop 4).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s008 : ((fits05.drop 8).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s012 : ((fits05.drop 12).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s016 : ((fits05.drop 16).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s020 : ((fits05.drop 20).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s024 : ((fits05.drop 24).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s028 : ((fits05.drop 28).take 4).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_s032 : ((fits05.drop 32).take 3).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05_end : (fits05.drop 35).all frame076test05=true := by
  decide +kernel

private theorem frame076scope05 : fits05.all frame076test05=true := by
  have h32 := stitchAt 32 3 frame076scope05_s032 frame076scope05_end
  have h28 := stitchAt 28 4 frame076scope05_s028 h32
  have h24 := stitchAt 24 4 frame076scope05_s024 h28
  have h20 := stitchAt 20 4 frame076scope05_s020 h24
  have h16 := stitchAt 16 4 frame076scope05_s016 h20
  have h12 := stitchAt 12 4 frame076scope05_s012 h16
  have h8 := stitchAt 8 4 frame076scope05_s008 h12
  have h4 := stitchAt 4 4 frame076scope05_s004 h8
  have h0 := stitchAt 0 4 frame076scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch05 : batch05.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope05

private abbrev frame076test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch06.stop,F)

private theorem frame076scope06_s000 : ((fits06.drop 0).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s004 : ((fits06.drop 4).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s008 : ((fits06.drop 8).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s012 : ((fits06.drop 12).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s016 : ((fits06.drop 16).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s020 : ((fits06.drop 20).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s024 : ((fits06.drop 24).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s028 : ((fits06.drop 28).take 4).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_s032 : ((fits06.drop 32).take 3).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06_end : (fits06.drop 35).all frame076test06=true := by
  decide +kernel

private theorem frame076scope06 : fits06.all frame076test06=true := by
  have h32 := stitchAt 32 3 frame076scope06_s032 frame076scope06_end
  have h28 := stitchAt 28 4 frame076scope06_s028 h32
  have h24 := stitchAt 24 4 frame076scope06_s024 h28
  have h20 := stitchAt 20 4 frame076scope06_s020 h24
  have h16 := stitchAt 16 4 frame076scope06_s016 h20
  have h12 := stitchAt 12 4 frame076scope06_s012 h16
  have h8 := stitchAt 8 4 frame076scope06_s008 h12
  have h4 := stitchAt 4 4 frame076scope06_s004 h8
  have h0 := stitchAt 0 4 frame076scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch06 : batch06.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope06

private abbrev frame076test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame155 (fun z => List.lookup (guideCode z) guide076)
    (batch07.stop,F)

private theorem frame076scope07_s000 : ((fits07.drop 0).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s004 : ((fits07.drop 4).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s008 : ((fits07.drop 8).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s012 : ((fits07.drop 12).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s016 : ((fits07.drop 16).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s020 : ((fits07.drop 20).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s024 : ((fits07.drop 24).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s028 : ((fits07.drop 28).take 4).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_s032 : ((fits07.drop 32).take 3).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07_end : (fits07.drop 35).all frame076test07=true := by
  decide +kernel

private theorem frame076scope07 : fits07.all frame076test07=true := by
  have h32 := stitchAt 32 3 frame076scope07_s032 frame076scope07_end
  have h28 := stitchAt 28 4 frame076scope07_s028 h32
  have h24 := stitchAt 24 4 frame076scope07_s024 h28
  have h20 := stitchAt 20 4 frame076scope07_s020 h24
  have h16 := stitchAt 16 4 frame076scope07_s016 h20
  have h12 := stitchAt 12 4 frame076scope07_s012 h16
  have h8 := stitchAt 8 4 frame076scope07_s008 h12
  have h4 := stitchAt 4 4 frame076scope07_s004 h8
  have h0 := stitchAt 0 4 frame076scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame076batch07 : batch07.pickTest original frame155=true :=
  FitBatch.pickTest_of_scoped scoped076 frame076scope07

private theorem frameBatches076 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame155)=true := by
  simp only [List.all_cons,List.all_nil,frame076batch00,frame076batch01,frame076batch02,frame076batch03,frame076batch04,frame076batch05,frame076batch06,frame076batch07,Bool.and_self]

theorem frameOK076 : frameRankTest original useStop frame155=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches076

theorem stripOK077 : stripTest frame156=true := by decide +kernel

theorem spanOK077 : checkChain 1856 1848 [frame156.span]=true := by decide +kernel

private theorem guideAt077 : List.lookup frame156.span.1 guideTable=some guide077 := by
  decide +kernel

private theorem scoped077 : original.guide frame156.span.1 =
    (fun z => List.lookup (guideCode z) guide077) := by
  funext z
  change (List.lookup frame156.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide077
  simp only [guideAt077,Option.bind_some]

private abbrev frame077test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch00.stop,F)

private theorem frame077scope00_s000 : ((fits00.drop 0).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s004 : ((fits00.drop 4).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s008 : ((fits00.drop 8).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s012 : ((fits00.drop 12).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s016 : ((fits00.drop 16).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s020 : ((fits00.drop 20).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s024 : ((fits00.drop 24).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s028 : ((fits00.drop 28).take 4).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_s032 : ((fits00.drop 32).take 3).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00_end : (fits00.drop 35).all frame077test00=true := by
  decide +kernel

private theorem frame077scope00 : fits00.all frame077test00=true := by
  have h32 := stitchAt 32 3 frame077scope00_s032 frame077scope00_end
  have h28 := stitchAt 28 4 frame077scope00_s028 h32
  have h24 := stitchAt 24 4 frame077scope00_s024 h28
  have h20 := stitchAt 20 4 frame077scope00_s020 h24
  have h16 := stitchAt 16 4 frame077scope00_s016 h20
  have h12 := stitchAt 12 4 frame077scope00_s012 h16
  have h8 := stitchAt 8 4 frame077scope00_s008 h12
  have h4 := stitchAt 4 4 frame077scope00_s004 h8
  have h0 := stitchAt 0 4 frame077scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch00 : batch00.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope00

private abbrev frame077test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch01.stop,F)

private theorem frame077scope01_s000 : ((fits01.drop 0).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s004 : ((fits01.drop 4).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s008 : ((fits01.drop 8).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s012 : ((fits01.drop 12).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s016 : ((fits01.drop 16).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s020 : ((fits01.drop 20).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s024 : ((fits01.drop 24).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s028 : ((fits01.drop 28).take 4).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_s032 : ((fits01.drop 32).take 3).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01_end : (fits01.drop 35).all frame077test01=true := by
  decide +kernel

private theorem frame077scope01 : fits01.all frame077test01=true := by
  have h32 := stitchAt 32 3 frame077scope01_s032 frame077scope01_end
  have h28 := stitchAt 28 4 frame077scope01_s028 h32
  have h24 := stitchAt 24 4 frame077scope01_s024 h28
  have h20 := stitchAt 20 4 frame077scope01_s020 h24
  have h16 := stitchAt 16 4 frame077scope01_s016 h20
  have h12 := stitchAt 12 4 frame077scope01_s012 h16
  have h8 := stitchAt 8 4 frame077scope01_s008 h12
  have h4 := stitchAt 4 4 frame077scope01_s004 h8
  have h0 := stitchAt 0 4 frame077scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch01 : batch01.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope01

private abbrev frame077test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch02.stop,F)

private theorem frame077scope02_s000 : ((fits02.drop 0).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s004 : ((fits02.drop 4).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s008 : ((fits02.drop 8).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s012 : ((fits02.drop 12).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s016 : ((fits02.drop 16).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s020 : ((fits02.drop 20).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s024 : ((fits02.drop 24).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s028 : ((fits02.drop 28).take 4).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_s032 : ((fits02.drop 32).take 3).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02_end : (fits02.drop 35).all frame077test02=true := by
  decide +kernel

private theorem frame077scope02 : fits02.all frame077test02=true := by
  have h32 := stitchAt 32 3 frame077scope02_s032 frame077scope02_end
  have h28 := stitchAt 28 4 frame077scope02_s028 h32
  have h24 := stitchAt 24 4 frame077scope02_s024 h28
  have h20 := stitchAt 20 4 frame077scope02_s020 h24
  have h16 := stitchAt 16 4 frame077scope02_s016 h20
  have h12 := stitchAt 12 4 frame077scope02_s012 h16
  have h8 := stitchAt 8 4 frame077scope02_s008 h12
  have h4 := stitchAt 4 4 frame077scope02_s004 h8
  have h0 := stitchAt 0 4 frame077scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch02 : batch02.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope02

private abbrev frame077test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch03.stop,F)

private theorem frame077scope03_s000 : ((fits03.drop 0).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s004 : ((fits03.drop 4).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s008 : ((fits03.drop 8).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s012 : ((fits03.drop 12).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s016 : ((fits03.drop 16).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s020 : ((fits03.drop 20).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s024 : ((fits03.drop 24).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s028 : ((fits03.drop 28).take 4).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_s032 : ((fits03.drop 32).take 3).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03_end : (fits03.drop 35).all frame077test03=true := by
  decide +kernel

private theorem frame077scope03 : fits03.all frame077test03=true := by
  have h32 := stitchAt 32 3 frame077scope03_s032 frame077scope03_end
  have h28 := stitchAt 28 4 frame077scope03_s028 h32
  have h24 := stitchAt 24 4 frame077scope03_s024 h28
  have h20 := stitchAt 20 4 frame077scope03_s020 h24
  have h16 := stitchAt 16 4 frame077scope03_s016 h20
  have h12 := stitchAt 12 4 frame077scope03_s012 h16
  have h8 := stitchAt 8 4 frame077scope03_s008 h12
  have h4 := stitchAt 4 4 frame077scope03_s004 h8
  have h0 := stitchAt 0 4 frame077scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch03 : batch03.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope03

private abbrev frame077test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch04.stop,F)

private theorem frame077scope04_s000 : ((fits04.drop 0).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s004 : ((fits04.drop 4).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s008 : ((fits04.drop 8).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s012 : ((fits04.drop 12).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s016 : ((fits04.drop 16).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s020 : ((fits04.drop 20).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s024 : ((fits04.drop 24).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s028 : ((fits04.drop 28).take 4).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_s032 : ((fits04.drop 32).take 3).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04_end : (fits04.drop 35).all frame077test04=true := by
  decide +kernel

private theorem frame077scope04 : fits04.all frame077test04=true := by
  have h32 := stitchAt 32 3 frame077scope04_s032 frame077scope04_end
  have h28 := stitchAt 28 4 frame077scope04_s028 h32
  have h24 := stitchAt 24 4 frame077scope04_s024 h28
  have h20 := stitchAt 20 4 frame077scope04_s020 h24
  have h16 := stitchAt 16 4 frame077scope04_s016 h20
  have h12 := stitchAt 12 4 frame077scope04_s012 h16
  have h8 := stitchAt 8 4 frame077scope04_s008 h12
  have h4 := stitchAt 4 4 frame077scope04_s004 h8
  have h0 := stitchAt 0 4 frame077scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch04 : batch04.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope04

private abbrev frame077test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch05.stop,F)

private theorem frame077scope05_s000 : ((fits05.drop 0).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s004 : ((fits05.drop 4).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s008 : ((fits05.drop 8).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s012 : ((fits05.drop 12).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s016 : ((fits05.drop 16).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s020 : ((fits05.drop 20).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s024 : ((fits05.drop 24).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s028 : ((fits05.drop 28).take 4).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_s032 : ((fits05.drop 32).take 3).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05_end : (fits05.drop 35).all frame077test05=true := by
  decide +kernel

private theorem frame077scope05 : fits05.all frame077test05=true := by
  have h32 := stitchAt 32 3 frame077scope05_s032 frame077scope05_end
  have h28 := stitchAt 28 4 frame077scope05_s028 h32
  have h24 := stitchAt 24 4 frame077scope05_s024 h28
  have h20 := stitchAt 20 4 frame077scope05_s020 h24
  have h16 := stitchAt 16 4 frame077scope05_s016 h20
  have h12 := stitchAt 12 4 frame077scope05_s012 h16
  have h8 := stitchAt 8 4 frame077scope05_s008 h12
  have h4 := stitchAt 4 4 frame077scope05_s004 h8
  have h0 := stitchAt 0 4 frame077scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch05 : batch05.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope05

private abbrev frame077test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch06.stop,F)

private theorem frame077scope06_s000 : ((fits06.drop 0).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s004 : ((fits06.drop 4).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s008 : ((fits06.drop 8).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s012 : ((fits06.drop 12).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s016 : ((fits06.drop 16).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s020 : ((fits06.drop 20).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s024 : ((fits06.drop 24).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s028 : ((fits06.drop 28).take 4).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_s032 : ((fits06.drop 32).take 3).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06_end : (fits06.drop 35).all frame077test06=true := by
  decide +kernel

private theorem frame077scope06 : fits06.all frame077test06=true := by
  have h32 := stitchAt 32 3 frame077scope06_s032 frame077scope06_end
  have h28 := stitchAt 28 4 frame077scope06_s028 h32
  have h24 := stitchAt 24 4 frame077scope06_s024 h28
  have h20 := stitchAt 20 4 frame077scope06_s020 h24
  have h16 := stitchAt 16 4 frame077scope06_s016 h20
  have h12 := stitchAt 12 4 frame077scope06_s012 h16
  have h8 := stitchAt 8 4 frame077scope06_s008 h12
  have h4 := stitchAt 4 4 frame077scope06_s004 h8
  have h0 := stitchAt 0 4 frame077scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch06 : batch06.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope06

private abbrev frame077test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame156 (fun z => List.lookup (guideCode z) guide077)
    (batch07.stop,F)

private theorem frame077scope07_s000 : ((fits07.drop 0).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s004 : ((fits07.drop 4).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s008 : ((fits07.drop 8).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s012 : ((fits07.drop 12).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s016 : ((fits07.drop 16).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s020 : ((fits07.drop 20).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s024 : ((fits07.drop 24).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s028 : ((fits07.drop 28).take 4).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_s032 : ((fits07.drop 32).take 3).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07_end : (fits07.drop 35).all frame077test07=true := by
  decide +kernel

private theorem frame077scope07 : fits07.all frame077test07=true := by
  have h32 := stitchAt 32 3 frame077scope07_s032 frame077scope07_end
  have h28 := stitchAt 28 4 frame077scope07_s028 h32
  have h24 := stitchAt 24 4 frame077scope07_s024 h28
  have h20 := stitchAt 20 4 frame077scope07_s020 h24
  have h16 := stitchAt 16 4 frame077scope07_s016 h20
  have h12 := stitchAt 12 4 frame077scope07_s012 h16
  have h8 := stitchAt 8 4 frame077scope07_s008 h12
  have h4 := stitchAt 4 4 frame077scope07_s004 h8
  have h0 := stitchAt 0 4 frame077scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame077batch07 : batch07.pickTest original frame156=true :=
  FitBatch.pickTest_of_scoped scoped077 frame077scope07

private theorem frameBatches077 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame156)=true := by
  simp only [List.all_cons,List.all_nil,frame077batch00,frame077batch01,frame077batch02,frame077batch03,frame077batch04,frame077batch05,frame077batch06,frame077batch07,Bool.and_self]

theorem frameOK077 : frameRankTest original useStop frame156=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches077


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
