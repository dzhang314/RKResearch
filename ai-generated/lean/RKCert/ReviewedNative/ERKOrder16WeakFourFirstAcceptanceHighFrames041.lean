module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK082 : stripTest frame166=true := by decide +kernel

theorem spanOK082 : checkChain 1904 1888 [frame166.span]=true := by decide +kernel

private theorem guideAt082 : List.lookup frame166.span.1 guideTable=some guide082 := by
  decide +kernel

private theorem scoped082 : original.guide frame166.span.1 =
    (fun z => List.lookup (guideCode z) guide082) := by
  funext z
  change (List.lookup frame166.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide082
  simp only [guideAt082,Option.bind_some]

private abbrev frame082test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch00.stop,F)

private theorem frame082scope00_s000 : ((fits00.drop 0).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s004 : ((fits00.drop 4).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s008 : ((fits00.drop 8).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s012 : ((fits00.drop 12).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s016 : ((fits00.drop 16).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s020 : ((fits00.drop 20).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s024 : ((fits00.drop 24).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s028 : ((fits00.drop 28).take 4).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_s032 : ((fits00.drop 32).take 3).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00_end : (fits00.drop 35).all frame082test00=true := by
  decide +kernel

private theorem frame082scope00 : fits00.all frame082test00=true := by
  have h32 := stitchAt 32 3 frame082scope00_s032 frame082scope00_end
  have h28 := stitchAt 28 4 frame082scope00_s028 h32
  have h24 := stitchAt 24 4 frame082scope00_s024 h28
  have h20 := stitchAt 20 4 frame082scope00_s020 h24
  have h16 := stitchAt 16 4 frame082scope00_s016 h20
  have h12 := stitchAt 12 4 frame082scope00_s012 h16
  have h8 := stitchAt 8 4 frame082scope00_s008 h12
  have h4 := stitchAt 4 4 frame082scope00_s004 h8
  have h0 := stitchAt 0 4 frame082scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch00 : batch00.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope00

private abbrev frame082test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch01.stop,F)

private theorem frame082scope01_s000 : ((fits01.drop 0).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s004 : ((fits01.drop 4).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s008 : ((fits01.drop 8).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s012 : ((fits01.drop 12).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s016 : ((fits01.drop 16).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s020 : ((fits01.drop 20).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s024 : ((fits01.drop 24).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s028 : ((fits01.drop 28).take 4).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_s032 : ((fits01.drop 32).take 3).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01_end : (fits01.drop 35).all frame082test01=true := by
  decide +kernel

private theorem frame082scope01 : fits01.all frame082test01=true := by
  have h32 := stitchAt 32 3 frame082scope01_s032 frame082scope01_end
  have h28 := stitchAt 28 4 frame082scope01_s028 h32
  have h24 := stitchAt 24 4 frame082scope01_s024 h28
  have h20 := stitchAt 20 4 frame082scope01_s020 h24
  have h16 := stitchAt 16 4 frame082scope01_s016 h20
  have h12 := stitchAt 12 4 frame082scope01_s012 h16
  have h8 := stitchAt 8 4 frame082scope01_s008 h12
  have h4 := stitchAt 4 4 frame082scope01_s004 h8
  have h0 := stitchAt 0 4 frame082scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch01 : batch01.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope01

private abbrev frame082test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch02.stop,F)

private theorem frame082scope02_s000 : ((fits02.drop 0).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s004 : ((fits02.drop 4).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s008 : ((fits02.drop 8).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s012 : ((fits02.drop 12).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s016 : ((fits02.drop 16).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s020 : ((fits02.drop 20).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s024 : ((fits02.drop 24).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s028 : ((fits02.drop 28).take 4).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_s032 : ((fits02.drop 32).take 3).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02_end : (fits02.drop 35).all frame082test02=true := by
  decide +kernel

private theorem frame082scope02 : fits02.all frame082test02=true := by
  have h32 := stitchAt 32 3 frame082scope02_s032 frame082scope02_end
  have h28 := stitchAt 28 4 frame082scope02_s028 h32
  have h24 := stitchAt 24 4 frame082scope02_s024 h28
  have h20 := stitchAt 20 4 frame082scope02_s020 h24
  have h16 := stitchAt 16 4 frame082scope02_s016 h20
  have h12 := stitchAt 12 4 frame082scope02_s012 h16
  have h8 := stitchAt 8 4 frame082scope02_s008 h12
  have h4 := stitchAt 4 4 frame082scope02_s004 h8
  have h0 := stitchAt 0 4 frame082scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch02 : batch02.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope02

private abbrev frame082test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch03.stop,F)

private theorem frame082scope03_s000 : ((fits03.drop 0).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s004 : ((fits03.drop 4).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s008 : ((fits03.drop 8).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s012 : ((fits03.drop 12).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s016 : ((fits03.drop 16).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s020 : ((fits03.drop 20).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s024 : ((fits03.drop 24).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s028 : ((fits03.drop 28).take 4).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_s032 : ((fits03.drop 32).take 3).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03_end : (fits03.drop 35).all frame082test03=true := by
  decide +kernel

private theorem frame082scope03 : fits03.all frame082test03=true := by
  have h32 := stitchAt 32 3 frame082scope03_s032 frame082scope03_end
  have h28 := stitchAt 28 4 frame082scope03_s028 h32
  have h24 := stitchAt 24 4 frame082scope03_s024 h28
  have h20 := stitchAt 20 4 frame082scope03_s020 h24
  have h16 := stitchAt 16 4 frame082scope03_s016 h20
  have h12 := stitchAt 12 4 frame082scope03_s012 h16
  have h8 := stitchAt 8 4 frame082scope03_s008 h12
  have h4 := stitchAt 4 4 frame082scope03_s004 h8
  have h0 := stitchAt 0 4 frame082scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch03 : batch03.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope03

private abbrev frame082test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch04.stop,F)

private theorem frame082scope04_s000 : ((fits04.drop 0).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s004 : ((fits04.drop 4).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s008 : ((fits04.drop 8).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s012 : ((fits04.drop 12).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s016 : ((fits04.drop 16).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s020 : ((fits04.drop 20).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s024 : ((fits04.drop 24).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s028 : ((fits04.drop 28).take 4).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_s032 : ((fits04.drop 32).take 3).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04_end : (fits04.drop 35).all frame082test04=true := by
  decide +kernel

private theorem frame082scope04 : fits04.all frame082test04=true := by
  have h32 := stitchAt 32 3 frame082scope04_s032 frame082scope04_end
  have h28 := stitchAt 28 4 frame082scope04_s028 h32
  have h24 := stitchAt 24 4 frame082scope04_s024 h28
  have h20 := stitchAt 20 4 frame082scope04_s020 h24
  have h16 := stitchAt 16 4 frame082scope04_s016 h20
  have h12 := stitchAt 12 4 frame082scope04_s012 h16
  have h8 := stitchAt 8 4 frame082scope04_s008 h12
  have h4 := stitchAt 4 4 frame082scope04_s004 h8
  have h0 := stitchAt 0 4 frame082scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch04 : batch04.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope04

private abbrev frame082test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch05.stop,F)

private theorem frame082scope05_s000 : ((fits05.drop 0).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s004 : ((fits05.drop 4).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s008 : ((fits05.drop 8).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s012 : ((fits05.drop 12).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s016 : ((fits05.drop 16).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s020 : ((fits05.drop 20).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s024 : ((fits05.drop 24).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s028 : ((fits05.drop 28).take 4).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_s032 : ((fits05.drop 32).take 3).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05_end : (fits05.drop 35).all frame082test05=true := by
  decide +kernel

private theorem frame082scope05 : fits05.all frame082test05=true := by
  have h32 := stitchAt 32 3 frame082scope05_s032 frame082scope05_end
  have h28 := stitchAt 28 4 frame082scope05_s028 h32
  have h24 := stitchAt 24 4 frame082scope05_s024 h28
  have h20 := stitchAt 20 4 frame082scope05_s020 h24
  have h16 := stitchAt 16 4 frame082scope05_s016 h20
  have h12 := stitchAt 12 4 frame082scope05_s012 h16
  have h8 := stitchAt 8 4 frame082scope05_s008 h12
  have h4 := stitchAt 4 4 frame082scope05_s004 h8
  have h0 := stitchAt 0 4 frame082scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch05 : batch05.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope05

private abbrev frame082test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch06.stop,F)

private theorem frame082scope06_s000 : ((fits06.drop 0).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s004 : ((fits06.drop 4).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s008 : ((fits06.drop 8).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s012 : ((fits06.drop 12).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s016 : ((fits06.drop 16).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s020 : ((fits06.drop 20).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s024 : ((fits06.drop 24).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s028 : ((fits06.drop 28).take 4).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_s032 : ((fits06.drop 32).take 3).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06_end : (fits06.drop 35).all frame082test06=true := by
  decide +kernel

private theorem frame082scope06 : fits06.all frame082test06=true := by
  have h32 := stitchAt 32 3 frame082scope06_s032 frame082scope06_end
  have h28 := stitchAt 28 4 frame082scope06_s028 h32
  have h24 := stitchAt 24 4 frame082scope06_s024 h28
  have h20 := stitchAt 20 4 frame082scope06_s020 h24
  have h16 := stitchAt 16 4 frame082scope06_s016 h20
  have h12 := stitchAt 12 4 frame082scope06_s012 h16
  have h8 := stitchAt 8 4 frame082scope06_s008 h12
  have h4 := stitchAt 4 4 frame082scope06_s004 h8
  have h0 := stitchAt 0 4 frame082scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch06 : batch06.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope06

private abbrev frame082test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame166 (fun z => List.lookup (guideCode z) guide082)
    (batch07.stop,F)

private theorem frame082scope07_s000 : ((fits07.drop 0).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s004 : ((fits07.drop 4).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s008 : ((fits07.drop 8).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s012 : ((fits07.drop 12).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s016 : ((fits07.drop 16).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s020 : ((fits07.drop 20).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s024 : ((fits07.drop 24).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s028 : ((fits07.drop 28).take 4).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_s032 : ((fits07.drop 32).take 3).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07_end : (fits07.drop 35).all frame082test07=true := by
  decide +kernel

private theorem frame082scope07 : fits07.all frame082test07=true := by
  have h32 := stitchAt 32 3 frame082scope07_s032 frame082scope07_end
  have h28 := stitchAt 28 4 frame082scope07_s028 h32
  have h24 := stitchAt 24 4 frame082scope07_s024 h28
  have h20 := stitchAt 20 4 frame082scope07_s020 h24
  have h16 := stitchAt 16 4 frame082scope07_s016 h20
  have h12 := stitchAt 12 4 frame082scope07_s012 h16
  have h8 := stitchAt 8 4 frame082scope07_s008 h12
  have h4 := stitchAt 4 4 frame082scope07_s004 h8
  have h0 := stitchAt 0 4 frame082scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame082batch07 : batch07.pickTest original frame166=true :=
  FitBatch.pickTest_of_scoped scoped082 frame082scope07

private theorem frameBatches082 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame166)=true := by
  simp only [List.all_cons,List.all_nil,frame082batch00,frame082batch01,frame082batch02,frame082batch03,frame082batch04,frame082batch05,frame082batch06,frame082batch07,Bool.and_self]

theorem frameOK082 : frameRankTest original useStop frame166=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches082

theorem stripOK083 : stripTest frame167=true := by decide +kernel

theorem spanOK083 : checkChain 1920 1904 [frame167.span]=true := by decide +kernel

private theorem guideAt083 : List.lookup frame167.span.1 guideTable=some guide083 := by
  decide +kernel

private theorem scoped083 : original.guide frame167.span.1 =
    (fun z => List.lookup (guideCode z) guide083) := by
  funext z
  change (List.lookup frame167.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide083
  simp only [guideAt083,Option.bind_some]

private abbrev frame083test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch00.stop,F)

private theorem frame083scope00_s000 : ((fits00.drop 0).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s004 : ((fits00.drop 4).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s008 : ((fits00.drop 8).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s012 : ((fits00.drop 12).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s016 : ((fits00.drop 16).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s020 : ((fits00.drop 20).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s024 : ((fits00.drop 24).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s028 : ((fits00.drop 28).take 4).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_s032 : ((fits00.drop 32).take 3).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00_end : (fits00.drop 35).all frame083test00=true := by
  decide +kernel

private theorem frame083scope00 : fits00.all frame083test00=true := by
  have h32 := stitchAt 32 3 frame083scope00_s032 frame083scope00_end
  have h28 := stitchAt 28 4 frame083scope00_s028 h32
  have h24 := stitchAt 24 4 frame083scope00_s024 h28
  have h20 := stitchAt 20 4 frame083scope00_s020 h24
  have h16 := stitchAt 16 4 frame083scope00_s016 h20
  have h12 := stitchAt 12 4 frame083scope00_s012 h16
  have h8 := stitchAt 8 4 frame083scope00_s008 h12
  have h4 := stitchAt 4 4 frame083scope00_s004 h8
  have h0 := stitchAt 0 4 frame083scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch00 : batch00.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope00

private abbrev frame083test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch01.stop,F)

private theorem frame083scope01_s000 : ((fits01.drop 0).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s004 : ((fits01.drop 4).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s008 : ((fits01.drop 8).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s012 : ((fits01.drop 12).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s016 : ((fits01.drop 16).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s020 : ((fits01.drop 20).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s024 : ((fits01.drop 24).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s028 : ((fits01.drop 28).take 4).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_s032 : ((fits01.drop 32).take 3).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01_end : (fits01.drop 35).all frame083test01=true := by
  decide +kernel

private theorem frame083scope01 : fits01.all frame083test01=true := by
  have h32 := stitchAt 32 3 frame083scope01_s032 frame083scope01_end
  have h28 := stitchAt 28 4 frame083scope01_s028 h32
  have h24 := stitchAt 24 4 frame083scope01_s024 h28
  have h20 := stitchAt 20 4 frame083scope01_s020 h24
  have h16 := stitchAt 16 4 frame083scope01_s016 h20
  have h12 := stitchAt 12 4 frame083scope01_s012 h16
  have h8 := stitchAt 8 4 frame083scope01_s008 h12
  have h4 := stitchAt 4 4 frame083scope01_s004 h8
  have h0 := stitchAt 0 4 frame083scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch01 : batch01.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope01

private abbrev frame083test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch02.stop,F)

private theorem frame083scope02_s000 : ((fits02.drop 0).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s004 : ((fits02.drop 4).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s008 : ((fits02.drop 8).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s012 : ((fits02.drop 12).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s016 : ((fits02.drop 16).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s020 : ((fits02.drop 20).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s024 : ((fits02.drop 24).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s028 : ((fits02.drop 28).take 4).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_s032 : ((fits02.drop 32).take 3).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02_end : (fits02.drop 35).all frame083test02=true := by
  decide +kernel

private theorem frame083scope02 : fits02.all frame083test02=true := by
  have h32 := stitchAt 32 3 frame083scope02_s032 frame083scope02_end
  have h28 := stitchAt 28 4 frame083scope02_s028 h32
  have h24 := stitchAt 24 4 frame083scope02_s024 h28
  have h20 := stitchAt 20 4 frame083scope02_s020 h24
  have h16 := stitchAt 16 4 frame083scope02_s016 h20
  have h12 := stitchAt 12 4 frame083scope02_s012 h16
  have h8 := stitchAt 8 4 frame083scope02_s008 h12
  have h4 := stitchAt 4 4 frame083scope02_s004 h8
  have h0 := stitchAt 0 4 frame083scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch02 : batch02.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope02

private abbrev frame083test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch03.stop,F)

private theorem frame083scope03_s000 : ((fits03.drop 0).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s004 : ((fits03.drop 4).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s008 : ((fits03.drop 8).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s012 : ((fits03.drop 12).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s016 : ((fits03.drop 16).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s020 : ((fits03.drop 20).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s024 : ((fits03.drop 24).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s028 : ((fits03.drop 28).take 4).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_s032 : ((fits03.drop 32).take 3).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03_end : (fits03.drop 35).all frame083test03=true := by
  decide +kernel

private theorem frame083scope03 : fits03.all frame083test03=true := by
  have h32 := stitchAt 32 3 frame083scope03_s032 frame083scope03_end
  have h28 := stitchAt 28 4 frame083scope03_s028 h32
  have h24 := stitchAt 24 4 frame083scope03_s024 h28
  have h20 := stitchAt 20 4 frame083scope03_s020 h24
  have h16 := stitchAt 16 4 frame083scope03_s016 h20
  have h12 := stitchAt 12 4 frame083scope03_s012 h16
  have h8 := stitchAt 8 4 frame083scope03_s008 h12
  have h4 := stitchAt 4 4 frame083scope03_s004 h8
  have h0 := stitchAt 0 4 frame083scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch03 : batch03.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope03

private abbrev frame083test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch04.stop,F)

private theorem frame083scope04_s000 : ((fits04.drop 0).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s004 : ((fits04.drop 4).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s008 : ((fits04.drop 8).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s012 : ((fits04.drop 12).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s016 : ((fits04.drop 16).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s020 : ((fits04.drop 20).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s024 : ((fits04.drop 24).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s028 : ((fits04.drop 28).take 4).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_s032 : ((fits04.drop 32).take 3).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04_end : (fits04.drop 35).all frame083test04=true := by
  decide +kernel

private theorem frame083scope04 : fits04.all frame083test04=true := by
  have h32 := stitchAt 32 3 frame083scope04_s032 frame083scope04_end
  have h28 := stitchAt 28 4 frame083scope04_s028 h32
  have h24 := stitchAt 24 4 frame083scope04_s024 h28
  have h20 := stitchAt 20 4 frame083scope04_s020 h24
  have h16 := stitchAt 16 4 frame083scope04_s016 h20
  have h12 := stitchAt 12 4 frame083scope04_s012 h16
  have h8 := stitchAt 8 4 frame083scope04_s008 h12
  have h4 := stitchAt 4 4 frame083scope04_s004 h8
  have h0 := stitchAt 0 4 frame083scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch04 : batch04.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope04

private abbrev frame083test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch05.stop,F)

private theorem frame083scope05_s000 : ((fits05.drop 0).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s004 : ((fits05.drop 4).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s008 : ((fits05.drop 8).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s012 : ((fits05.drop 12).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s016 : ((fits05.drop 16).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s020 : ((fits05.drop 20).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s024 : ((fits05.drop 24).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s028 : ((fits05.drop 28).take 4).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_s032 : ((fits05.drop 32).take 3).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05_end : (fits05.drop 35).all frame083test05=true := by
  decide +kernel

private theorem frame083scope05 : fits05.all frame083test05=true := by
  have h32 := stitchAt 32 3 frame083scope05_s032 frame083scope05_end
  have h28 := stitchAt 28 4 frame083scope05_s028 h32
  have h24 := stitchAt 24 4 frame083scope05_s024 h28
  have h20 := stitchAt 20 4 frame083scope05_s020 h24
  have h16 := stitchAt 16 4 frame083scope05_s016 h20
  have h12 := stitchAt 12 4 frame083scope05_s012 h16
  have h8 := stitchAt 8 4 frame083scope05_s008 h12
  have h4 := stitchAt 4 4 frame083scope05_s004 h8
  have h0 := stitchAt 0 4 frame083scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch05 : batch05.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope05

private abbrev frame083test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch06.stop,F)

private theorem frame083scope06_s000 : ((fits06.drop 0).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s004 : ((fits06.drop 4).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s008 : ((fits06.drop 8).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s012 : ((fits06.drop 12).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s016 : ((fits06.drop 16).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s020 : ((fits06.drop 20).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s024 : ((fits06.drop 24).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s028 : ((fits06.drop 28).take 4).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_s032 : ((fits06.drop 32).take 3).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06_end : (fits06.drop 35).all frame083test06=true := by
  decide +kernel

private theorem frame083scope06 : fits06.all frame083test06=true := by
  have h32 := stitchAt 32 3 frame083scope06_s032 frame083scope06_end
  have h28 := stitchAt 28 4 frame083scope06_s028 h32
  have h24 := stitchAt 24 4 frame083scope06_s024 h28
  have h20 := stitchAt 20 4 frame083scope06_s020 h24
  have h16 := stitchAt 16 4 frame083scope06_s016 h20
  have h12 := stitchAt 12 4 frame083scope06_s012 h16
  have h8 := stitchAt 8 4 frame083scope06_s008 h12
  have h4 := stitchAt 4 4 frame083scope06_s004 h8
  have h0 := stitchAt 0 4 frame083scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch06 : batch06.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope06

private abbrev frame083test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame167 (fun z => List.lookup (guideCode z) guide083)
    (batch07.stop,F)

private theorem frame083scope07_s000 : ((fits07.drop 0).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s004 : ((fits07.drop 4).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s008 : ((fits07.drop 8).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s012 : ((fits07.drop 12).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s016 : ((fits07.drop 16).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s020 : ((fits07.drop 20).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s024 : ((fits07.drop 24).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s028 : ((fits07.drop 28).take 4).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_s032 : ((fits07.drop 32).take 3).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07_end : (fits07.drop 35).all frame083test07=true := by
  decide +kernel

private theorem frame083scope07 : fits07.all frame083test07=true := by
  have h32 := stitchAt 32 3 frame083scope07_s032 frame083scope07_end
  have h28 := stitchAt 28 4 frame083scope07_s028 h32
  have h24 := stitchAt 24 4 frame083scope07_s024 h28
  have h20 := stitchAt 20 4 frame083scope07_s020 h24
  have h16 := stitchAt 16 4 frame083scope07_s016 h20
  have h12 := stitchAt 12 4 frame083scope07_s012 h16
  have h8 := stitchAt 8 4 frame083scope07_s008 h12
  have h4 := stitchAt 4 4 frame083scope07_s004 h8
  have h0 := stitchAt 0 4 frame083scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame083batch07 : batch07.pickTest original frame167=true :=
  FitBatch.pickTest_of_scoped scoped083 frame083scope07

private theorem frameBatches083 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame167)=true := by
  simp only [List.all_cons,List.all_nil,frame083batch00,frame083batch01,frame083batch02,frame083batch03,frame083batch04,frame083batch05,frame083batch06,frame083batch07,Bool.and_self]

theorem frameOK083 : frameRankTest original useStop frame167=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches083


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
