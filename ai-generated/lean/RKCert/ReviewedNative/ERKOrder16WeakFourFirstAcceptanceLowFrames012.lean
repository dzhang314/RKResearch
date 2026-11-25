module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksLow

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK024 : stripTest frame48=true := by decide +kernel

theorem spanOK024 : checkChain 2048 1792 [frame48.span]=true := by decide +kernel

private theorem guideAt024 : List.lookup frame48.span.1 guideTable=some guide024 := by
  decide +kernel

private theorem scoped024 : original.guide frame48.span.1 =
    (fun z => List.lookup (guideCode z) guide024) := by
  funext z
  change (List.lookup frame48.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide024
  simp only [guideAt024,Option.bind_some]

private abbrev frame024test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch00.stop,F)

private theorem frame024scope00_s000 : ((fits00.drop 0).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s004 : ((fits00.drop 4).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s008 : ((fits00.drop 8).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s012 : ((fits00.drop 12).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s016 : ((fits00.drop 16).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s020 : ((fits00.drop 20).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s024 : ((fits00.drop 24).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s028 : ((fits00.drop 28).take 4).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_s032 : ((fits00.drop 32).take 3).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00_end : (fits00.drop 35).all frame024test00=true := by
  decide +kernel

private theorem frame024scope00 : fits00.all frame024test00=true := by
  have h32 := stitchAt 32 3 frame024scope00_s032 frame024scope00_end
  have h28 := stitchAt 28 4 frame024scope00_s028 h32
  have h24 := stitchAt 24 4 frame024scope00_s024 h28
  have h20 := stitchAt 20 4 frame024scope00_s020 h24
  have h16 := stitchAt 16 4 frame024scope00_s016 h20
  have h12 := stitchAt 12 4 frame024scope00_s012 h16
  have h8 := stitchAt 8 4 frame024scope00_s008 h12
  have h4 := stitchAt 4 4 frame024scope00_s004 h8
  have h0 := stitchAt 0 4 frame024scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch00 : batch00.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope00

private abbrev frame024test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch01.stop,F)

private theorem frame024scope01_s000 : ((fits01.drop 0).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s004 : ((fits01.drop 4).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s008 : ((fits01.drop 8).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s012 : ((fits01.drop 12).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s016 : ((fits01.drop 16).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s020 : ((fits01.drop 20).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s024 : ((fits01.drop 24).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s028 : ((fits01.drop 28).take 4).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_s032 : ((fits01.drop 32).take 3).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01_end : (fits01.drop 35).all frame024test01=true := by
  decide +kernel

private theorem frame024scope01 : fits01.all frame024test01=true := by
  have h32 := stitchAt 32 3 frame024scope01_s032 frame024scope01_end
  have h28 := stitchAt 28 4 frame024scope01_s028 h32
  have h24 := stitchAt 24 4 frame024scope01_s024 h28
  have h20 := stitchAt 20 4 frame024scope01_s020 h24
  have h16 := stitchAt 16 4 frame024scope01_s016 h20
  have h12 := stitchAt 12 4 frame024scope01_s012 h16
  have h8 := stitchAt 8 4 frame024scope01_s008 h12
  have h4 := stitchAt 4 4 frame024scope01_s004 h8
  have h0 := stitchAt 0 4 frame024scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch01 : batch01.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope01

private abbrev frame024test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch02.stop,F)

private theorem frame024scope02_s000 : ((fits02.drop 0).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s004 : ((fits02.drop 4).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s008 : ((fits02.drop 8).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s012 : ((fits02.drop 12).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s016 : ((fits02.drop 16).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s020 : ((fits02.drop 20).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s024 : ((fits02.drop 24).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s028 : ((fits02.drop 28).take 4).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_s032 : ((fits02.drop 32).take 3).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02_end : (fits02.drop 35).all frame024test02=true := by
  decide +kernel

private theorem frame024scope02 : fits02.all frame024test02=true := by
  have h32 := stitchAt 32 3 frame024scope02_s032 frame024scope02_end
  have h28 := stitchAt 28 4 frame024scope02_s028 h32
  have h24 := stitchAt 24 4 frame024scope02_s024 h28
  have h20 := stitchAt 20 4 frame024scope02_s020 h24
  have h16 := stitchAt 16 4 frame024scope02_s016 h20
  have h12 := stitchAt 12 4 frame024scope02_s012 h16
  have h8 := stitchAt 8 4 frame024scope02_s008 h12
  have h4 := stitchAt 4 4 frame024scope02_s004 h8
  have h0 := stitchAt 0 4 frame024scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch02 : batch02.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope02

private abbrev frame024test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch03.stop,F)

private theorem frame024scope03_s000 : ((fits03.drop 0).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s004 : ((fits03.drop 4).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s008 : ((fits03.drop 8).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s012 : ((fits03.drop 12).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s016 : ((fits03.drop 16).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s020 : ((fits03.drop 20).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s024 : ((fits03.drop 24).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s028 : ((fits03.drop 28).take 4).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_s032 : ((fits03.drop 32).take 3).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03_end : (fits03.drop 35).all frame024test03=true := by
  decide +kernel

private theorem frame024scope03 : fits03.all frame024test03=true := by
  have h32 := stitchAt 32 3 frame024scope03_s032 frame024scope03_end
  have h28 := stitchAt 28 4 frame024scope03_s028 h32
  have h24 := stitchAt 24 4 frame024scope03_s024 h28
  have h20 := stitchAt 20 4 frame024scope03_s020 h24
  have h16 := stitchAt 16 4 frame024scope03_s016 h20
  have h12 := stitchAt 12 4 frame024scope03_s012 h16
  have h8 := stitchAt 8 4 frame024scope03_s008 h12
  have h4 := stitchAt 4 4 frame024scope03_s004 h8
  have h0 := stitchAt 0 4 frame024scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch03 : batch03.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope03

private abbrev frame024test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch04.stop,F)

private theorem frame024scope04_s000 : ((fits04.drop 0).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s004 : ((fits04.drop 4).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s008 : ((fits04.drop 8).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s012 : ((fits04.drop 12).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s016 : ((fits04.drop 16).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s020 : ((fits04.drop 20).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s024 : ((fits04.drop 24).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s028 : ((fits04.drop 28).take 4).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_s032 : ((fits04.drop 32).take 3).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04_end : (fits04.drop 35).all frame024test04=true := by
  decide +kernel

private theorem frame024scope04 : fits04.all frame024test04=true := by
  have h32 := stitchAt 32 3 frame024scope04_s032 frame024scope04_end
  have h28 := stitchAt 28 4 frame024scope04_s028 h32
  have h24 := stitchAt 24 4 frame024scope04_s024 h28
  have h20 := stitchAt 20 4 frame024scope04_s020 h24
  have h16 := stitchAt 16 4 frame024scope04_s016 h20
  have h12 := stitchAt 12 4 frame024scope04_s012 h16
  have h8 := stitchAt 8 4 frame024scope04_s008 h12
  have h4 := stitchAt 4 4 frame024scope04_s004 h8
  have h0 := stitchAt 0 4 frame024scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch04 : batch04.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope04

private abbrev frame024test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch05.stop,F)

private theorem frame024scope05_s000 : ((fits05.drop 0).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s004 : ((fits05.drop 4).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s008 : ((fits05.drop 8).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s012 : ((fits05.drop 12).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s016 : ((fits05.drop 16).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s020 : ((fits05.drop 20).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s024 : ((fits05.drop 24).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s028 : ((fits05.drop 28).take 4).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_s032 : ((fits05.drop 32).take 3).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05_end : (fits05.drop 35).all frame024test05=true := by
  decide +kernel

private theorem frame024scope05 : fits05.all frame024test05=true := by
  have h32 := stitchAt 32 3 frame024scope05_s032 frame024scope05_end
  have h28 := stitchAt 28 4 frame024scope05_s028 h32
  have h24 := stitchAt 24 4 frame024scope05_s024 h28
  have h20 := stitchAt 20 4 frame024scope05_s020 h24
  have h16 := stitchAt 16 4 frame024scope05_s016 h20
  have h12 := stitchAt 12 4 frame024scope05_s012 h16
  have h8 := stitchAt 8 4 frame024scope05_s008 h12
  have h4 := stitchAt 4 4 frame024scope05_s004 h8
  have h0 := stitchAt 0 4 frame024scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch05 : batch05.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope05

private abbrev frame024test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide024)
    (batch06.stop,F)

private theorem frame024scope06_s000 : ((fits06.drop 0).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s004 : ((fits06.drop 4).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s008 : ((fits06.drop 8).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s012 : ((fits06.drop 12).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s016 : ((fits06.drop 16).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s020 : ((fits06.drop 20).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s024 : ((fits06.drop 24).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s028 : ((fits06.drop 28).take 4).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_s032 : ((fits06.drop 32).take 3).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06_end : (fits06.drop 35).all frame024test06=true := by
  decide +kernel

private theorem frame024scope06 : fits06.all frame024test06=true := by
  have h32 := stitchAt 32 3 frame024scope06_s032 frame024scope06_end
  have h28 := stitchAt 28 4 frame024scope06_s028 h32
  have h24 := stitchAt 24 4 frame024scope06_s024 h28
  have h20 := stitchAt 20 4 frame024scope06_s020 h24
  have h16 := stitchAt 16 4 frame024scope06_s016 h20
  have h12 := stitchAt 12 4 frame024scope06_s012 h16
  have h8 := stitchAt 8 4 frame024scope06_s008 h12
  have h4 := stitchAt 4 4 frame024scope06_s004 h8
  have h0 := stitchAt 0 4 frame024scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame024batch06 : batch06.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped024 frame024scope06

private theorem frameBatches024 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06].all (FitBatch.pickTest original frame48)=true := by
  simp only [List.all_cons,List.all_nil,frame024batch00,frame024batch01,frame024batch02,frame024batch03,frame024batch04,frame024batch05,frame024batch06,Bool.and_self]

theorem frameOK024 : frameRankTest original useStop frame48=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches024


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
