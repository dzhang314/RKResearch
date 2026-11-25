module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksLow

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK012 : stripTest frame32=true := by decide +kernel

theorem spanOK012 : checkChain 1541 1540 [frame32.span]=true := by decide +kernel

private theorem guideAt012 : List.lookup frame32.span.1 guideTable=some guide012 := by
  decide +kernel

private theorem scoped012 : original.guide frame32.span.1 =
    (fun z => List.lookup (guideCode z) guide012) := by
  funext z
  change (List.lookup frame32.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide012
  simp only [guideAt012,Option.bind_some]

private abbrev frame012test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch00.stop,F)

private theorem frame012scope00_s000 : ((fits00.drop 0).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s004 : ((fits00.drop 4).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s008 : ((fits00.drop 8).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s012 : ((fits00.drop 12).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s016 : ((fits00.drop 16).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s020 : ((fits00.drop 20).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s024 : ((fits00.drop 24).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s028 : ((fits00.drop 28).take 4).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_s032 : ((fits00.drop 32).take 3).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00_end : (fits00.drop 35).all frame012test00=true := by
  decide +kernel

private theorem frame012scope00 : fits00.all frame012test00=true := by
  have h32 := stitchAt 32 3 frame012scope00_s032 frame012scope00_end
  have h28 := stitchAt 28 4 frame012scope00_s028 h32
  have h24 := stitchAt 24 4 frame012scope00_s024 h28
  have h20 := stitchAt 20 4 frame012scope00_s020 h24
  have h16 := stitchAt 16 4 frame012scope00_s016 h20
  have h12 := stitchAt 12 4 frame012scope00_s012 h16
  have h8 := stitchAt 8 4 frame012scope00_s008 h12
  have h4 := stitchAt 4 4 frame012scope00_s004 h8
  have h0 := stitchAt 0 4 frame012scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch00 : batch00.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope00

private abbrev frame012test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch01.stop,F)

private theorem frame012scope01_s000 : ((fits01.drop 0).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s004 : ((fits01.drop 4).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s008 : ((fits01.drop 8).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s012 : ((fits01.drop 12).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s016 : ((fits01.drop 16).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s020 : ((fits01.drop 20).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s024 : ((fits01.drop 24).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s028 : ((fits01.drop 28).take 4).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_s032 : ((fits01.drop 32).take 3).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01_end : (fits01.drop 35).all frame012test01=true := by
  decide +kernel

private theorem frame012scope01 : fits01.all frame012test01=true := by
  have h32 := stitchAt 32 3 frame012scope01_s032 frame012scope01_end
  have h28 := stitchAt 28 4 frame012scope01_s028 h32
  have h24 := stitchAt 24 4 frame012scope01_s024 h28
  have h20 := stitchAt 20 4 frame012scope01_s020 h24
  have h16 := stitchAt 16 4 frame012scope01_s016 h20
  have h12 := stitchAt 12 4 frame012scope01_s012 h16
  have h8 := stitchAt 8 4 frame012scope01_s008 h12
  have h4 := stitchAt 4 4 frame012scope01_s004 h8
  have h0 := stitchAt 0 4 frame012scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch01 : batch01.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope01

private abbrev frame012test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch02.stop,F)

private theorem frame012scope02_s000 : ((fits02.drop 0).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s004 : ((fits02.drop 4).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s008 : ((fits02.drop 8).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s012 : ((fits02.drop 12).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s016 : ((fits02.drop 16).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s020 : ((fits02.drop 20).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s024 : ((fits02.drop 24).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s028 : ((fits02.drop 28).take 4).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_s032 : ((fits02.drop 32).take 3).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02_end : (fits02.drop 35).all frame012test02=true := by
  decide +kernel

private theorem frame012scope02 : fits02.all frame012test02=true := by
  have h32 := stitchAt 32 3 frame012scope02_s032 frame012scope02_end
  have h28 := stitchAt 28 4 frame012scope02_s028 h32
  have h24 := stitchAt 24 4 frame012scope02_s024 h28
  have h20 := stitchAt 20 4 frame012scope02_s020 h24
  have h16 := stitchAt 16 4 frame012scope02_s016 h20
  have h12 := stitchAt 12 4 frame012scope02_s012 h16
  have h8 := stitchAt 8 4 frame012scope02_s008 h12
  have h4 := stitchAt 4 4 frame012scope02_s004 h8
  have h0 := stitchAt 0 4 frame012scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch02 : batch02.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope02

private abbrev frame012test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch03.stop,F)

private theorem frame012scope03_s000 : ((fits03.drop 0).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s004 : ((fits03.drop 4).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s008 : ((fits03.drop 8).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s012 : ((fits03.drop 12).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s016 : ((fits03.drop 16).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s020 : ((fits03.drop 20).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s024 : ((fits03.drop 24).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s028 : ((fits03.drop 28).take 4).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_s032 : ((fits03.drop 32).take 3).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03_end : (fits03.drop 35).all frame012test03=true := by
  decide +kernel

private theorem frame012scope03 : fits03.all frame012test03=true := by
  have h32 := stitchAt 32 3 frame012scope03_s032 frame012scope03_end
  have h28 := stitchAt 28 4 frame012scope03_s028 h32
  have h24 := stitchAt 24 4 frame012scope03_s024 h28
  have h20 := stitchAt 20 4 frame012scope03_s020 h24
  have h16 := stitchAt 16 4 frame012scope03_s016 h20
  have h12 := stitchAt 12 4 frame012scope03_s012 h16
  have h8 := stitchAt 8 4 frame012scope03_s008 h12
  have h4 := stitchAt 4 4 frame012scope03_s004 h8
  have h0 := stitchAt 0 4 frame012scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch03 : batch03.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope03

private abbrev frame012test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch04.stop,F)

private theorem frame012scope04_s000 : ((fits04.drop 0).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s004 : ((fits04.drop 4).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s008 : ((fits04.drop 8).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s012 : ((fits04.drop 12).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s016 : ((fits04.drop 16).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s020 : ((fits04.drop 20).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s024 : ((fits04.drop 24).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s028 : ((fits04.drop 28).take 4).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_s032 : ((fits04.drop 32).take 3).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04_end : (fits04.drop 35).all frame012test04=true := by
  decide +kernel

private theorem frame012scope04 : fits04.all frame012test04=true := by
  have h32 := stitchAt 32 3 frame012scope04_s032 frame012scope04_end
  have h28 := stitchAt 28 4 frame012scope04_s028 h32
  have h24 := stitchAt 24 4 frame012scope04_s024 h28
  have h20 := stitchAt 20 4 frame012scope04_s020 h24
  have h16 := stitchAt 16 4 frame012scope04_s016 h20
  have h12 := stitchAt 12 4 frame012scope04_s012 h16
  have h8 := stitchAt 8 4 frame012scope04_s008 h12
  have h4 := stitchAt 4 4 frame012scope04_s004 h8
  have h0 := stitchAt 0 4 frame012scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch04 : batch04.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope04

private abbrev frame012test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch05.stop,F)

private theorem frame012scope05_s000 : ((fits05.drop 0).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s004 : ((fits05.drop 4).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s008 : ((fits05.drop 8).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s012 : ((fits05.drop 12).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s016 : ((fits05.drop 16).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s020 : ((fits05.drop 20).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s024 : ((fits05.drop 24).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s028 : ((fits05.drop 28).take 4).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_s032 : ((fits05.drop 32).take 3).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05_end : (fits05.drop 35).all frame012test05=true := by
  decide +kernel

private theorem frame012scope05 : fits05.all frame012test05=true := by
  have h32 := stitchAt 32 3 frame012scope05_s032 frame012scope05_end
  have h28 := stitchAt 28 4 frame012scope05_s028 h32
  have h24 := stitchAt 24 4 frame012scope05_s024 h28
  have h20 := stitchAt 20 4 frame012scope05_s020 h24
  have h16 := stitchAt 16 4 frame012scope05_s016 h20
  have h12 := stitchAt 12 4 frame012scope05_s012 h16
  have h8 := stitchAt 8 4 frame012scope05_s008 h12
  have h4 := stitchAt 4 4 frame012scope05_s004 h8
  have h0 := stitchAt 0 4 frame012scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch05 : batch05.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope05

private abbrev frame012test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame32 (fun z => List.lookup (guideCode z) guide012)
    (batch06.stop,F)

private theorem frame012scope06_s000 : ((fits06.drop 0).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s004 : ((fits06.drop 4).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s008 : ((fits06.drop 8).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s012 : ((fits06.drop 12).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s016 : ((fits06.drop 16).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s020 : ((fits06.drop 20).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s024 : ((fits06.drop 24).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s028 : ((fits06.drop 28).take 4).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_s032 : ((fits06.drop 32).take 3).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06_end : (fits06.drop 35).all frame012test06=true := by
  decide +kernel

private theorem frame012scope06 : fits06.all frame012test06=true := by
  have h32 := stitchAt 32 3 frame012scope06_s032 frame012scope06_end
  have h28 := stitchAt 28 4 frame012scope06_s028 h32
  have h24 := stitchAt 24 4 frame012scope06_s024 h28
  have h20 := stitchAt 20 4 frame012scope06_s020 h24
  have h16 := stitchAt 16 4 frame012scope06_s016 h20
  have h12 := stitchAt 12 4 frame012scope06_s012 h16
  have h8 := stitchAt 8 4 frame012scope06_s008 h12
  have h4 := stitchAt 4 4 frame012scope06_s004 h8
  have h0 := stitchAt 0 4 frame012scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame012batch06 : batch06.pickTest original frame32=true :=
  FitBatch.pickTest_of_scoped scoped012 frame012scope06

private theorem frameBatches012 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06].all (FitBatch.pickTest original frame32)=true := by
  simp only [List.all_cons,List.all_nil,frame012batch00,frame012batch01,frame012batch02,frame012batch03,frame012batch04,frame012batch05,frame012batch06,Bool.and_self]

theorem frameOK012 : frameRankTest original useStop frame32=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches012

theorem stripOK013 : stripTest frame33=true := by decide +kernel

theorem spanOK013 : checkChain 1542 1541 [frame33.span]=true := by decide +kernel

private theorem guideAt013 : List.lookup frame33.span.1 guideTable=some guide013 := by
  decide +kernel

private theorem scoped013 : original.guide frame33.span.1 =
    (fun z => List.lookup (guideCode z) guide013) := by
  funext z
  change (List.lookup frame33.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide013
  simp only [guideAt013,Option.bind_some]

private abbrev frame013test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch00.stop,F)

private theorem frame013scope00_s000 : ((fits00.drop 0).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s004 : ((fits00.drop 4).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s008 : ((fits00.drop 8).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s012 : ((fits00.drop 12).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s016 : ((fits00.drop 16).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s020 : ((fits00.drop 20).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s024 : ((fits00.drop 24).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s028 : ((fits00.drop 28).take 4).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_s032 : ((fits00.drop 32).take 3).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00_end : (fits00.drop 35).all frame013test00=true := by
  decide +kernel

private theorem frame013scope00 : fits00.all frame013test00=true := by
  have h32 := stitchAt 32 3 frame013scope00_s032 frame013scope00_end
  have h28 := stitchAt 28 4 frame013scope00_s028 h32
  have h24 := stitchAt 24 4 frame013scope00_s024 h28
  have h20 := stitchAt 20 4 frame013scope00_s020 h24
  have h16 := stitchAt 16 4 frame013scope00_s016 h20
  have h12 := stitchAt 12 4 frame013scope00_s012 h16
  have h8 := stitchAt 8 4 frame013scope00_s008 h12
  have h4 := stitchAt 4 4 frame013scope00_s004 h8
  have h0 := stitchAt 0 4 frame013scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch00 : batch00.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope00

private abbrev frame013test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch01.stop,F)

private theorem frame013scope01_s000 : ((fits01.drop 0).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s004 : ((fits01.drop 4).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s008 : ((fits01.drop 8).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s012 : ((fits01.drop 12).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s016 : ((fits01.drop 16).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s020 : ((fits01.drop 20).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s024 : ((fits01.drop 24).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s028 : ((fits01.drop 28).take 4).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_s032 : ((fits01.drop 32).take 3).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01_end : (fits01.drop 35).all frame013test01=true := by
  decide +kernel

private theorem frame013scope01 : fits01.all frame013test01=true := by
  have h32 := stitchAt 32 3 frame013scope01_s032 frame013scope01_end
  have h28 := stitchAt 28 4 frame013scope01_s028 h32
  have h24 := stitchAt 24 4 frame013scope01_s024 h28
  have h20 := stitchAt 20 4 frame013scope01_s020 h24
  have h16 := stitchAt 16 4 frame013scope01_s016 h20
  have h12 := stitchAt 12 4 frame013scope01_s012 h16
  have h8 := stitchAt 8 4 frame013scope01_s008 h12
  have h4 := stitchAt 4 4 frame013scope01_s004 h8
  have h0 := stitchAt 0 4 frame013scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch01 : batch01.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope01

private abbrev frame013test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch02.stop,F)

private theorem frame013scope02_s000 : ((fits02.drop 0).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s004 : ((fits02.drop 4).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s008 : ((fits02.drop 8).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s012 : ((fits02.drop 12).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s016 : ((fits02.drop 16).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s020 : ((fits02.drop 20).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s024 : ((fits02.drop 24).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s028 : ((fits02.drop 28).take 4).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_s032 : ((fits02.drop 32).take 3).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02_end : (fits02.drop 35).all frame013test02=true := by
  decide +kernel

private theorem frame013scope02 : fits02.all frame013test02=true := by
  have h32 := stitchAt 32 3 frame013scope02_s032 frame013scope02_end
  have h28 := stitchAt 28 4 frame013scope02_s028 h32
  have h24 := stitchAt 24 4 frame013scope02_s024 h28
  have h20 := stitchAt 20 4 frame013scope02_s020 h24
  have h16 := stitchAt 16 4 frame013scope02_s016 h20
  have h12 := stitchAt 12 4 frame013scope02_s012 h16
  have h8 := stitchAt 8 4 frame013scope02_s008 h12
  have h4 := stitchAt 4 4 frame013scope02_s004 h8
  have h0 := stitchAt 0 4 frame013scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch02 : batch02.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope02

private abbrev frame013test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch03.stop,F)

private theorem frame013scope03_s000 : ((fits03.drop 0).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s004 : ((fits03.drop 4).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s008 : ((fits03.drop 8).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s012 : ((fits03.drop 12).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s016 : ((fits03.drop 16).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s020 : ((fits03.drop 20).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s024 : ((fits03.drop 24).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s028 : ((fits03.drop 28).take 4).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_s032 : ((fits03.drop 32).take 3).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03_end : (fits03.drop 35).all frame013test03=true := by
  decide +kernel

private theorem frame013scope03 : fits03.all frame013test03=true := by
  have h32 := stitchAt 32 3 frame013scope03_s032 frame013scope03_end
  have h28 := stitchAt 28 4 frame013scope03_s028 h32
  have h24 := stitchAt 24 4 frame013scope03_s024 h28
  have h20 := stitchAt 20 4 frame013scope03_s020 h24
  have h16 := stitchAt 16 4 frame013scope03_s016 h20
  have h12 := stitchAt 12 4 frame013scope03_s012 h16
  have h8 := stitchAt 8 4 frame013scope03_s008 h12
  have h4 := stitchAt 4 4 frame013scope03_s004 h8
  have h0 := stitchAt 0 4 frame013scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch03 : batch03.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope03

private abbrev frame013test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch04.stop,F)

private theorem frame013scope04_s000 : ((fits04.drop 0).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s004 : ((fits04.drop 4).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s008 : ((fits04.drop 8).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s012 : ((fits04.drop 12).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s016 : ((fits04.drop 16).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s020 : ((fits04.drop 20).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s024 : ((fits04.drop 24).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s028 : ((fits04.drop 28).take 4).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_s032 : ((fits04.drop 32).take 3).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04_end : (fits04.drop 35).all frame013test04=true := by
  decide +kernel

private theorem frame013scope04 : fits04.all frame013test04=true := by
  have h32 := stitchAt 32 3 frame013scope04_s032 frame013scope04_end
  have h28 := stitchAt 28 4 frame013scope04_s028 h32
  have h24 := stitchAt 24 4 frame013scope04_s024 h28
  have h20 := stitchAt 20 4 frame013scope04_s020 h24
  have h16 := stitchAt 16 4 frame013scope04_s016 h20
  have h12 := stitchAt 12 4 frame013scope04_s012 h16
  have h8 := stitchAt 8 4 frame013scope04_s008 h12
  have h4 := stitchAt 4 4 frame013scope04_s004 h8
  have h0 := stitchAt 0 4 frame013scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch04 : batch04.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope04

private abbrev frame013test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch05.stop,F)

private theorem frame013scope05_s000 : ((fits05.drop 0).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s004 : ((fits05.drop 4).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s008 : ((fits05.drop 8).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s012 : ((fits05.drop 12).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s016 : ((fits05.drop 16).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s020 : ((fits05.drop 20).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s024 : ((fits05.drop 24).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s028 : ((fits05.drop 28).take 4).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_s032 : ((fits05.drop 32).take 3).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05_end : (fits05.drop 35).all frame013test05=true := by
  decide +kernel

private theorem frame013scope05 : fits05.all frame013test05=true := by
  have h32 := stitchAt 32 3 frame013scope05_s032 frame013scope05_end
  have h28 := stitchAt 28 4 frame013scope05_s028 h32
  have h24 := stitchAt 24 4 frame013scope05_s024 h28
  have h20 := stitchAt 20 4 frame013scope05_s020 h24
  have h16 := stitchAt 16 4 frame013scope05_s016 h20
  have h12 := stitchAt 12 4 frame013scope05_s012 h16
  have h8 := stitchAt 8 4 frame013scope05_s008 h12
  have h4 := stitchAt 4 4 frame013scope05_s004 h8
  have h0 := stitchAt 0 4 frame013scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch05 : batch05.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope05

private abbrev frame013test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame33 (fun z => List.lookup (guideCode z) guide013)
    (batch06.stop,F)

private theorem frame013scope06_s000 : ((fits06.drop 0).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s004 : ((fits06.drop 4).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s008 : ((fits06.drop 8).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s012 : ((fits06.drop 12).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s016 : ((fits06.drop 16).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s020 : ((fits06.drop 20).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s024 : ((fits06.drop 24).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s028 : ((fits06.drop 28).take 4).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_s032 : ((fits06.drop 32).take 3).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06_end : (fits06.drop 35).all frame013test06=true := by
  decide +kernel

private theorem frame013scope06 : fits06.all frame013test06=true := by
  have h32 := stitchAt 32 3 frame013scope06_s032 frame013scope06_end
  have h28 := stitchAt 28 4 frame013scope06_s028 h32
  have h24 := stitchAt 24 4 frame013scope06_s024 h28
  have h20 := stitchAt 20 4 frame013scope06_s020 h24
  have h16 := stitchAt 16 4 frame013scope06_s016 h20
  have h12 := stitchAt 12 4 frame013scope06_s012 h16
  have h8 := stitchAt 8 4 frame013scope06_s008 h12
  have h4 := stitchAt 4 4 frame013scope06_s004 h8
  have h0 := stitchAt 0 4 frame013scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame013batch06 : batch06.pickTest original frame33=true :=
  FitBatch.pickTest_of_scoped scoped013 frame013scope06

private theorem frameBatches013 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06].all (FitBatch.pickTest original frame33)=true := by
  simp only [List.all_cons,List.all_nil,frame013batch00,frame013batch01,frame013batch02,frame013batch03,frame013batch04,frame013batch05,frame013batch06,Bool.and_self]

theorem frameOK013 : frameRankTest original useStop frame33=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches013


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
