module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksLow

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK004 : stripTest frame10=true := by decide +kernel

theorem spanOK004 : checkChain 1280 1024 [frame10.span]=true := by decide +kernel

private theorem guideAt004 : List.lookup frame10.span.1 guideTable=some guide004 := by
  decide +kernel

private theorem scoped004 : original.guide frame10.span.1 =
    (fun z => List.lookup (guideCode z) guide004) := by
  funext z
  change (List.lookup frame10.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide004
  simp only [guideAt004,Option.bind_some]

private abbrev frame004test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch00.stop,F)

private theorem frame004scope00_s000 : ((fits00.drop 0).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s004 : ((fits00.drop 4).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s008 : ((fits00.drop 8).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s012 : ((fits00.drop 12).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s016 : ((fits00.drop 16).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s020 : ((fits00.drop 20).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s024 : ((fits00.drop 24).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s028 : ((fits00.drop 28).take 4).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_s032 : ((fits00.drop 32).take 3).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00_end : (fits00.drop 35).all frame004test00=true := by
  decide +kernel

private theorem frame004scope00 : fits00.all frame004test00=true := by
  have h32 := stitchAt 32 3 frame004scope00_s032 frame004scope00_end
  have h28 := stitchAt 28 4 frame004scope00_s028 h32
  have h24 := stitchAt 24 4 frame004scope00_s024 h28
  have h20 := stitchAt 20 4 frame004scope00_s020 h24
  have h16 := stitchAt 16 4 frame004scope00_s016 h20
  have h12 := stitchAt 12 4 frame004scope00_s012 h16
  have h8 := stitchAt 8 4 frame004scope00_s008 h12
  have h4 := stitchAt 4 4 frame004scope00_s004 h8
  have h0 := stitchAt 0 4 frame004scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch00 : batch00.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope00

private abbrev frame004test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch01.stop,F)

private theorem frame004scope01_s000 : ((fits01.drop 0).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s004 : ((fits01.drop 4).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s008 : ((fits01.drop 8).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s012 : ((fits01.drop 12).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s016 : ((fits01.drop 16).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s020 : ((fits01.drop 20).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s024 : ((fits01.drop 24).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s028 : ((fits01.drop 28).take 4).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_s032 : ((fits01.drop 32).take 3).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01_end : (fits01.drop 35).all frame004test01=true := by
  decide +kernel

private theorem frame004scope01 : fits01.all frame004test01=true := by
  have h32 := stitchAt 32 3 frame004scope01_s032 frame004scope01_end
  have h28 := stitchAt 28 4 frame004scope01_s028 h32
  have h24 := stitchAt 24 4 frame004scope01_s024 h28
  have h20 := stitchAt 20 4 frame004scope01_s020 h24
  have h16 := stitchAt 16 4 frame004scope01_s016 h20
  have h12 := stitchAt 12 4 frame004scope01_s012 h16
  have h8 := stitchAt 8 4 frame004scope01_s008 h12
  have h4 := stitchAt 4 4 frame004scope01_s004 h8
  have h0 := stitchAt 0 4 frame004scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch01 : batch01.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope01

private abbrev frame004test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch02.stop,F)

private theorem frame004scope02_s000 : ((fits02.drop 0).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s004 : ((fits02.drop 4).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s008 : ((fits02.drop 8).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s012 : ((fits02.drop 12).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s016 : ((fits02.drop 16).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s020 : ((fits02.drop 20).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s024 : ((fits02.drop 24).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s028 : ((fits02.drop 28).take 4).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_s032 : ((fits02.drop 32).take 3).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02_end : (fits02.drop 35).all frame004test02=true := by
  decide +kernel

private theorem frame004scope02 : fits02.all frame004test02=true := by
  have h32 := stitchAt 32 3 frame004scope02_s032 frame004scope02_end
  have h28 := stitchAt 28 4 frame004scope02_s028 h32
  have h24 := stitchAt 24 4 frame004scope02_s024 h28
  have h20 := stitchAt 20 4 frame004scope02_s020 h24
  have h16 := stitchAt 16 4 frame004scope02_s016 h20
  have h12 := stitchAt 12 4 frame004scope02_s012 h16
  have h8 := stitchAt 8 4 frame004scope02_s008 h12
  have h4 := stitchAt 4 4 frame004scope02_s004 h8
  have h0 := stitchAt 0 4 frame004scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch02 : batch02.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope02

private abbrev frame004test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch03.stop,F)

private theorem frame004scope03_s000 : ((fits03.drop 0).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s004 : ((fits03.drop 4).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s008 : ((fits03.drop 8).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s012 : ((fits03.drop 12).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s016 : ((fits03.drop 16).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s020 : ((fits03.drop 20).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s024 : ((fits03.drop 24).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s028 : ((fits03.drop 28).take 4).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_s032 : ((fits03.drop 32).take 3).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03_end : (fits03.drop 35).all frame004test03=true := by
  decide +kernel

private theorem frame004scope03 : fits03.all frame004test03=true := by
  have h32 := stitchAt 32 3 frame004scope03_s032 frame004scope03_end
  have h28 := stitchAt 28 4 frame004scope03_s028 h32
  have h24 := stitchAt 24 4 frame004scope03_s024 h28
  have h20 := stitchAt 20 4 frame004scope03_s020 h24
  have h16 := stitchAt 16 4 frame004scope03_s016 h20
  have h12 := stitchAt 12 4 frame004scope03_s012 h16
  have h8 := stitchAt 8 4 frame004scope03_s008 h12
  have h4 := stitchAt 4 4 frame004scope03_s004 h8
  have h0 := stitchAt 0 4 frame004scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch03 : batch03.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope03

private abbrev frame004test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch04.stop,F)

private theorem frame004scope04_s000 : ((fits04.drop 0).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s004 : ((fits04.drop 4).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s008 : ((fits04.drop 8).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s012 : ((fits04.drop 12).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s016 : ((fits04.drop 16).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s020 : ((fits04.drop 20).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s024 : ((fits04.drop 24).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s028 : ((fits04.drop 28).take 4).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_s032 : ((fits04.drop 32).take 3).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04_end : (fits04.drop 35).all frame004test04=true := by
  decide +kernel

private theorem frame004scope04 : fits04.all frame004test04=true := by
  have h32 := stitchAt 32 3 frame004scope04_s032 frame004scope04_end
  have h28 := stitchAt 28 4 frame004scope04_s028 h32
  have h24 := stitchAt 24 4 frame004scope04_s024 h28
  have h20 := stitchAt 20 4 frame004scope04_s020 h24
  have h16 := stitchAt 16 4 frame004scope04_s016 h20
  have h12 := stitchAt 12 4 frame004scope04_s012 h16
  have h8 := stitchAt 8 4 frame004scope04_s008 h12
  have h4 := stitchAt 4 4 frame004scope04_s004 h8
  have h0 := stitchAt 0 4 frame004scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch04 : batch04.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope04

private abbrev frame004test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch05.stop,F)

private theorem frame004scope05_s000 : ((fits05.drop 0).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s004 : ((fits05.drop 4).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s008 : ((fits05.drop 8).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s012 : ((fits05.drop 12).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s016 : ((fits05.drop 16).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s020 : ((fits05.drop 20).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s024 : ((fits05.drop 24).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s028 : ((fits05.drop 28).take 4).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_s032 : ((fits05.drop 32).take 3).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05_end : (fits05.drop 35).all frame004test05=true := by
  decide +kernel

private theorem frame004scope05 : fits05.all frame004test05=true := by
  have h32 := stitchAt 32 3 frame004scope05_s032 frame004scope05_end
  have h28 := stitchAt 28 4 frame004scope05_s028 h32
  have h24 := stitchAt 24 4 frame004scope05_s024 h28
  have h20 := stitchAt 20 4 frame004scope05_s020 h24
  have h16 := stitchAt 16 4 frame004scope05_s016 h20
  have h12 := stitchAt 12 4 frame004scope05_s012 h16
  have h8 := stitchAt 8 4 frame004scope05_s008 h12
  have h4 := stitchAt 4 4 frame004scope05_s004 h8
  have h0 := stitchAt 0 4 frame004scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch05 : batch05.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope05

private abbrev frame004test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame10 (fun z => List.lookup (guideCode z) guide004)
    (batch06.stop,F)

private theorem frame004scope06_s000 : ((fits06.drop 0).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s004 : ((fits06.drop 4).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s008 : ((fits06.drop 8).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s012 : ((fits06.drop 12).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s016 : ((fits06.drop 16).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s020 : ((fits06.drop 20).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s024 : ((fits06.drop 24).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s028 : ((fits06.drop 28).take 4).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_s032 : ((fits06.drop 32).take 3).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06_end : (fits06.drop 35).all frame004test06=true := by
  decide +kernel

private theorem frame004scope06 : fits06.all frame004test06=true := by
  have h32 := stitchAt 32 3 frame004scope06_s032 frame004scope06_end
  have h28 := stitchAt 28 4 frame004scope06_s028 h32
  have h24 := stitchAt 24 4 frame004scope06_s024 h28
  have h20 := stitchAt 20 4 frame004scope06_s020 h24
  have h16 := stitchAt 16 4 frame004scope06_s016 h20
  have h12 := stitchAt 12 4 frame004scope06_s012 h16
  have h8 := stitchAt 8 4 frame004scope06_s008 h12
  have h4 := stitchAt 4 4 frame004scope06_s004 h8
  have h0 := stitchAt 0 4 frame004scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame004batch06 : batch06.pickTest original frame10=true :=
  FitBatch.pickTest_of_scoped scoped004 frame004scope06

private theorem frameBatches004 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06].all (FitBatch.pickTest original frame10)=true := by
  simp only [List.all_cons,List.all_nil,frame004batch00,frame004batch01,frame004batch02,frame004batch03,frame004batch04,frame004batch05,frame004batch06,Bool.and_self]

theorem frameOK004 : frameRankTest original useStop frame10=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches004

theorem stripOK005 : stripTest frame12=true := by decide +kernel

theorem spanOK005 : checkChain 1408 1280 [frame12.span]=true := by decide +kernel

private theorem guideAt005 : List.lookup frame12.span.1 guideTable=some guide005 := by
  decide +kernel

private theorem scoped005 : original.guide frame12.span.1 =
    (fun z => List.lookup (guideCode z) guide005) := by
  funext z
  change (List.lookup frame12.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide005
  simp only [guideAt005,Option.bind_some]

private abbrev frame005test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch00.stop,F)

private theorem frame005scope00_s000 : ((fits00.drop 0).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s004 : ((fits00.drop 4).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s008 : ((fits00.drop 8).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s012 : ((fits00.drop 12).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s016 : ((fits00.drop 16).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s020 : ((fits00.drop 20).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s024 : ((fits00.drop 24).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s028 : ((fits00.drop 28).take 4).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_s032 : ((fits00.drop 32).take 3).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00_end : (fits00.drop 35).all frame005test00=true := by
  decide +kernel

private theorem frame005scope00 : fits00.all frame005test00=true := by
  have h32 := stitchAt 32 3 frame005scope00_s032 frame005scope00_end
  have h28 := stitchAt 28 4 frame005scope00_s028 h32
  have h24 := stitchAt 24 4 frame005scope00_s024 h28
  have h20 := stitchAt 20 4 frame005scope00_s020 h24
  have h16 := stitchAt 16 4 frame005scope00_s016 h20
  have h12 := stitchAt 12 4 frame005scope00_s012 h16
  have h8 := stitchAt 8 4 frame005scope00_s008 h12
  have h4 := stitchAt 4 4 frame005scope00_s004 h8
  have h0 := stitchAt 0 4 frame005scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch00 : batch00.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope00

private abbrev frame005test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch01.stop,F)

private theorem frame005scope01_s000 : ((fits01.drop 0).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s004 : ((fits01.drop 4).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s008 : ((fits01.drop 8).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s012 : ((fits01.drop 12).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s016 : ((fits01.drop 16).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s020 : ((fits01.drop 20).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s024 : ((fits01.drop 24).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s028 : ((fits01.drop 28).take 4).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_s032 : ((fits01.drop 32).take 3).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01_end : (fits01.drop 35).all frame005test01=true := by
  decide +kernel

private theorem frame005scope01 : fits01.all frame005test01=true := by
  have h32 := stitchAt 32 3 frame005scope01_s032 frame005scope01_end
  have h28 := stitchAt 28 4 frame005scope01_s028 h32
  have h24 := stitchAt 24 4 frame005scope01_s024 h28
  have h20 := stitchAt 20 4 frame005scope01_s020 h24
  have h16 := stitchAt 16 4 frame005scope01_s016 h20
  have h12 := stitchAt 12 4 frame005scope01_s012 h16
  have h8 := stitchAt 8 4 frame005scope01_s008 h12
  have h4 := stitchAt 4 4 frame005scope01_s004 h8
  have h0 := stitchAt 0 4 frame005scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch01 : batch01.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope01

private abbrev frame005test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch02.stop,F)

private theorem frame005scope02_s000 : ((fits02.drop 0).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s004 : ((fits02.drop 4).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s008 : ((fits02.drop 8).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s012 : ((fits02.drop 12).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s016 : ((fits02.drop 16).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s020 : ((fits02.drop 20).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s024 : ((fits02.drop 24).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s028 : ((fits02.drop 28).take 4).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_s032 : ((fits02.drop 32).take 3).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02_end : (fits02.drop 35).all frame005test02=true := by
  decide +kernel

private theorem frame005scope02 : fits02.all frame005test02=true := by
  have h32 := stitchAt 32 3 frame005scope02_s032 frame005scope02_end
  have h28 := stitchAt 28 4 frame005scope02_s028 h32
  have h24 := stitchAt 24 4 frame005scope02_s024 h28
  have h20 := stitchAt 20 4 frame005scope02_s020 h24
  have h16 := stitchAt 16 4 frame005scope02_s016 h20
  have h12 := stitchAt 12 4 frame005scope02_s012 h16
  have h8 := stitchAt 8 4 frame005scope02_s008 h12
  have h4 := stitchAt 4 4 frame005scope02_s004 h8
  have h0 := stitchAt 0 4 frame005scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch02 : batch02.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope02

private abbrev frame005test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch03.stop,F)

private theorem frame005scope03_s000 : ((fits03.drop 0).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s004 : ((fits03.drop 4).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s008 : ((fits03.drop 8).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s012 : ((fits03.drop 12).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s016 : ((fits03.drop 16).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s020 : ((fits03.drop 20).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s024 : ((fits03.drop 24).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s028 : ((fits03.drop 28).take 4).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_s032 : ((fits03.drop 32).take 3).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03_end : (fits03.drop 35).all frame005test03=true := by
  decide +kernel

private theorem frame005scope03 : fits03.all frame005test03=true := by
  have h32 := stitchAt 32 3 frame005scope03_s032 frame005scope03_end
  have h28 := stitchAt 28 4 frame005scope03_s028 h32
  have h24 := stitchAt 24 4 frame005scope03_s024 h28
  have h20 := stitchAt 20 4 frame005scope03_s020 h24
  have h16 := stitchAt 16 4 frame005scope03_s016 h20
  have h12 := stitchAt 12 4 frame005scope03_s012 h16
  have h8 := stitchAt 8 4 frame005scope03_s008 h12
  have h4 := stitchAt 4 4 frame005scope03_s004 h8
  have h0 := stitchAt 0 4 frame005scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch03 : batch03.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope03

private abbrev frame005test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch04.stop,F)

private theorem frame005scope04_s000 : ((fits04.drop 0).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s004 : ((fits04.drop 4).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s008 : ((fits04.drop 8).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s012 : ((fits04.drop 12).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s016 : ((fits04.drop 16).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s020 : ((fits04.drop 20).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s024 : ((fits04.drop 24).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s028 : ((fits04.drop 28).take 4).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_s032 : ((fits04.drop 32).take 3).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04_end : (fits04.drop 35).all frame005test04=true := by
  decide +kernel

private theorem frame005scope04 : fits04.all frame005test04=true := by
  have h32 := stitchAt 32 3 frame005scope04_s032 frame005scope04_end
  have h28 := stitchAt 28 4 frame005scope04_s028 h32
  have h24 := stitchAt 24 4 frame005scope04_s024 h28
  have h20 := stitchAt 20 4 frame005scope04_s020 h24
  have h16 := stitchAt 16 4 frame005scope04_s016 h20
  have h12 := stitchAt 12 4 frame005scope04_s012 h16
  have h8 := stitchAt 8 4 frame005scope04_s008 h12
  have h4 := stitchAt 4 4 frame005scope04_s004 h8
  have h0 := stitchAt 0 4 frame005scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch04 : batch04.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope04

private abbrev frame005test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch05.stop,F)

private theorem frame005scope05_s000 : ((fits05.drop 0).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s004 : ((fits05.drop 4).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s008 : ((fits05.drop 8).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s012 : ((fits05.drop 12).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s016 : ((fits05.drop 16).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s020 : ((fits05.drop 20).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s024 : ((fits05.drop 24).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s028 : ((fits05.drop 28).take 4).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_s032 : ((fits05.drop 32).take 3).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05_end : (fits05.drop 35).all frame005test05=true := by
  decide +kernel

private theorem frame005scope05 : fits05.all frame005test05=true := by
  have h32 := stitchAt 32 3 frame005scope05_s032 frame005scope05_end
  have h28 := stitchAt 28 4 frame005scope05_s028 h32
  have h24 := stitchAt 24 4 frame005scope05_s024 h28
  have h20 := stitchAt 20 4 frame005scope05_s020 h24
  have h16 := stitchAt 16 4 frame005scope05_s016 h20
  have h12 := stitchAt 12 4 frame005scope05_s012 h16
  have h8 := stitchAt 8 4 frame005scope05_s008 h12
  have h4 := stitchAt 4 4 frame005scope05_s004 h8
  have h0 := stitchAt 0 4 frame005scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch05 : batch05.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope05

private abbrev frame005test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame12 (fun z => List.lookup (guideCode z) guide005)
    (batch06.stop,F)

private theorem frame005scope06_s000 : ((fits06.drop 0).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s004 : ((fits06.drop 4).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s008 : ((fits06.drop 8).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s012 : ((fits06.drop 12).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s016 : ((fits06.drop 16).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s020 : ((fits06.drop 20).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s024 : ((fits06.drop 24).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s028 : ((fits06.drop 28).take 4).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_s032 : ((fits06.drop 32).take 3).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06_end : (fits06.drop 35).all frame005test06=true := by
  decide +kernel

private theorem frame005scope06 : fits06.all frame005test06=true := by
  have h32 := stitchAt 32 3 frame005scope06_s032 frame005scope06_end
  have h28 := stitchAt 28 4 frame005scope06_s028 h32
  have h24 := stitchAt 24 4 frame005scope06_s024 h28
  have h20 := stitchAt 20 4 frame005scope06_s020 h24
  have h16 := stitchAt 16 4 frame005scope06_s016 h20
  have h12 := stitchAt 12 4 frame005scope06_s012 h16
  have h8 := stitchAt 8 4 frame005scope06_s008 h12
  have h4 := stitchAt 4 4 frame005scope06_s004 h8
  have h0 := stitchAt 0 4 frame005scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame005batch06 : batch06.pickTest original frame12=true :=
  FitBatch.pickTest_of_scoped scoped005 frame005scope06

private theorem frameBatches005 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06].all (FitBatch.pickTest original frame12)=true := by
  simp only [List.all_cons,List.all_nil,frame005batch00,frame005batch01,frame005batch02,frame005batch03,frame005batch04,frame005batch05,frame005batch06,Bool.and_self]

theorem frameOK005 : frameRankTest original useStop frame12=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches005


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
