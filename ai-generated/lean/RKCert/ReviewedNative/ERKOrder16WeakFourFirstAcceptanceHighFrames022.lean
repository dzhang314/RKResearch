module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK044 : stripTest frame92=true := by decide +kernel

theorem spanOK044 : checkChain 1750 1748 [frame92.span]=true := by decide +kernel

private theorem guideAt044 : List.lookup frame92.span.1 guideTable=some guide044 := by
  decide +kernel

private theorem scoped044 : original.guide frame92.span.1 =
    (fun z => List.lookup (guideCode z) guide044) := by
  funext z
  change (List.lookup frame92.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide044
  simp only [guideAt044,Option.bind_some]

private abbrev frame044test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch00.stop,F)

private theorem frame044scope00_s000 : ((fits00.drop 0).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s004 : ((fits00.drop 4).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s008 : ((fits00.drop 8).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s012 : ((fits00.drop 12).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s016 : ((fits00.drop 16).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s020 : ((fits00.drop 20).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s024 : ((fits00.drop 24).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s028 : ((fits00.drop 28).take 4).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_s032 : ((fits00.drop 32).take 3).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00_end : (fits00.drop 35).all frame044test00=true := by
  decide +kernel

private theorem frame044scope00 : fits00.all frame044test00=true := by
  have h32 := stitchAt 32 3 frame044scope00_s032 frame044scope00_end
  have h28 := stitchAt 28 4 frame044scope00_s028 h32
  have h24 := stitchAt 24 4 frame044scope00_s024 h28
  have h20 := stitchAt 20 4 frame044scope00_s020 h24
  have h16 := stitchAt 16 4 frame044scope00_s016 h20
  have h12 := stitchAt 12 4 frame044scope00_s012 h16
  have h8 := stitchAt 8 4 frame044scope00_s008 h12
  have h4 := stitchAt 4 4 frame044scope00_s004 h8
  have h0 := stitchAt 0 4 frame044scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch00 : batch00.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope00

private abbrev frame044test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch01.stop,F)

private theorem frame044scope01_s000 : ((fits01.drop 0).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s004 : ((fits01.drop 4).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s008 : ((fits01.drop 8).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s012 : ((fits01.drop 12).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s016 : ((fits01.drop 16).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s020 : ((fits01.drop 20).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s024 : ((fits01.drop 24).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s028 : ((fits01.drop 28).take 4).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_s032 : ((fits01.drop 32).take 3).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01_end : (fits01.drop 35).all frame044test01=true := by
  decide +kernel

private theorem frame044scope01 : fits01.all frame044test01=true := by
  have h32 := stitchAt 32 3 frame044scope01_s032 frame044scope01_end
  have h28 := stitchAt 28 4 frame044scope01_s028 h32
  have h24 := stitchAt 24 4 frame044scope01_s024 h28
  have h20 := stitchAt 20 4 frame044scope01_s020 h24
  have h16 := stitchAt 16 4 frame044scope01_s016 h20
  have h12 := stitchAt 12 4 frame044scope01_s012 h16
  have h8 := stitchAt 8 4 frame044scope01_s008 h12
  have h4 := stitchAt 4 4 frame044scope01_s004 h8
  have h0 := stitchAt 0 4 frame044scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch01 : batch01.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope01

private abbrev frame044test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch02.stop,F)

private theorem frame044scope02_s000 : ((fits02.drop 0).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s004 : ((fits02.drop 4).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s008 : ((fits02.drop 8).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s012 : ((fits02.drop 12).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s016 : ((fits02.drop 16).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s020 : ((fits02.drop 20).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s024 : ((fits02.drop 24).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s028 : ((fits02.drop 28).take 4).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_s032 : ((fits02.drop 32).take 3).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02_end : (fits02.drop 35).all frame044test02=true := by
  decide +kernel

private theorem frame044scope02 : fits02.all frame044test02=true := by
  have h32 := stitchAt 32 3 frame044scope02_s032 frame044scope02_end
  have h28 := stitchAt 28 4 frame044scope02_s028 h32
  have h24 := stitchAt 24 4 frame044scope02_s024 h28
  have h20 := stitchAt 20 4 frame044scope02_s020 h24
  have h16 := stitchAt 16 4 frame044scope02_s016 h20
  have h12 := stitchAt 12 4 frame044scope02_s012 h16
  have h8 := stitchAt 8 4 frame044scope02_s008 h12
  have h4 := stitchAt 4 4 frame044scope02_s004 h8
  have h0 := stitchAt 0 4 frame044scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch02 : batch02.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope02

private abbrev frame044test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch03.stop,F)

private theorem frame044scope03_s000 : ((fits03.drop 0).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s004 : ((fits03.drop 4).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s008 : ((fits03.drop 8).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s012 : ((fits03.drop 12).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s016 : ((fits03.drop 16).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s020 : ((fits03.drop 20).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s024 : ((fits03.drop 24).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s028 : ((fits03.drop 28).take 4).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_s032 : ((fits03.drop 32).take 3).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03_end : (fits03.drop 35).all frame044test03=true := by
  decide +kernel

private theorem frame044scope03 : fits03.all frame044test03=true := by
  have h32 := stitchAt 32 3 frame044scope03_s032 frame044scope03_end
  have h28 := stitchAt 28 4 frame044scope03_s028 h32
  have h24 := stitchAt 24 4 frame044scope03_s024 h28
  have h20 := stitchAt 20 4 frame044scope03_s020 h24
  have h16 := stitchAt 16 4 frame044scope03_s016 h20
  have h12 := stitchAt 12 4 frame044scope03_s012 h16
  have h8 := stitchAt 8 4 frame044scope03_s008 h12
  have h4 := stitchAt 4 4 frame044scope03_s004 h8
  have h0 := stitchAt 0 4 frame044scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch03 : batch03.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope03

private abbrev frame044test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch04.stop,F)

private theorem frame044scope04_s000 : ((fits04.drop 0).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s004 : ((fits04.drop 4).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s008 : ((fits04.drop 8).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s012 : ((fits04.drop 12).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s016 : ((fits04.drop 16).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s020 : ((fits04.drop 20).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s024 : ((fits04.drop 24).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s028 : ((fits04.drop 28).take 4).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_s032 : ((fits04.drop 32).take 3).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04_end : (fits04.drop 35).all frame044test04=true := by
  decide +kernel

private theorem frame044scope04 : fits04.all frame044test04=true := by
  have h32 := stitchAt 32 3 frame044scope04_s032 frame044scope04_end
  have h28 := stitchAt 28 4 frame044scope04_s028 h32
  have h24 := stitchAt 24 4 frame044scope04_s024 h28
  have h20 := stitchAt 20 4 frame044scope04_s020 h24
  have h16 := stitchAt 16 4 frame044scope04_s016 h20
  have h12 := stitchAt 12 4 frame044scope04_s012 h16
  have h8 := stitchAt 8 4 frame044scope04_s008 h12
  have h4 := stitchAt 4 4 frame044scope04_s004 h8
  have h0 := stitchAt 0 4 frame044scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch04 : batch04.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope04

private abbrev frame044test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch05.stop,F)

private theorem frame044scope05_s000 : ((fits05.drop 0).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s004 : ((fits05.drop 4).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s008 : ((fits05.drop 8).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s012 : ((fits05.drop 12).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s016 : ((fits05.drop 16).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s020 : ((fits05.drop 20).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s024 : ((fits05.drop 24).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s028 : ((fits05.drop 28).take 4).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_s032 : ((fits05.drop 32).take 3).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05_end : (fits05.drop 35).all frame044test05=true := by
  decide +kernel

private theorem frame044scope05 : fits05.all frame044test05=true := by
  have h32 := stitchAt 32 3 frame044scope05_s032 frame044scope05_end
  have h28 := stitchAt 28 4 frame044scope05_s028 h32
  have h24 := stitchAt 24 4 frame044scope05_s024 h28
  have h20 := stitchAt 20 4 frame044scope05_s020 h24
  have h16 := stitchAt 16 4 frame044scope05_s016 h20
  have h12 := stitchAt 12 4 frame044scope05_s012 h16
  have h8 := stitchAt 8 4 frame044scope05_s008 h12
  have h4 := stitchAt 4 4 frame044scope05_s004 h8
  have h0 := stitchAt 0 4 frame044scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch05 : batch05.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope05

private abbrev frame044test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch06.stop,F)

private theorem frame044scope06_s000 : ((fits06.drop 0).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s004 : ((fits06.drop 4).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s008 : ((fits06.drop 8).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s012 : ((fits06.drop 12).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s016 : ((fits06.drop 16).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s020 : ((fits06.drop 20).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s024 : ((fits06.drop 24).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s028 : ((fits06.drop 28).take 4).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_s032 : ((fits06.drop 32).take 3).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06_end : (fits06.drop 35).all frame044test06=true := by
  decide +kernel

private theorem frame044scope06 : fits06.all frame044test06=true := by
  have h32 := stitchAt 32 3 frame044scope06_s032 frame044scope06_end
  have h28 := stitchAt 28 4 frame044scope06_s028 h32
  have h24 := stitchAt 24 4 frame044scope06_s024 h28
  have h20 := stitchAt 20 4 frame044scope06_s020 h24
  have h16 := stitchAt 16 4 frame044scope06_s016 h20
  have h12 := stitchAt 12 4 frame044scope06_s012 h16
  have h8 := stitchAt 8 4 frame044scope06_s008 h12
  have h4 := stitchAt 4 4 frame044scope06_s004 h8
  have h0 := stitchAt 0 4 frame044scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch06 : batch06.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope06

private abbrev frame044test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame92 (fun z => List.lookup (guideCode z) guide044)
    (batch07.stop,F)

private theorem frame044scope07_s000 : ((fits07.drop 0).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s004 : ((fits07.drop 4).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s008 : ((fits07.drop 8).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s012 : ((fits07.drop 12).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s016 : ((fits07.drop 16).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s020 : ((fits07.drop 20).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s024 : ((fits07.drop 24).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s028 : ((fits07.drop 28).take 4).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_s032 : ((fits07.drop 32).take 3).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07_end : (fits07.drop 35).all frame044test07=true := by
  decide +kernel

private theorem frame044scope07 : fits07.all frame044test07=true := by
  have h32 := stitchAt 32 3 frame044scope07_s032 frame044scope07_end
  have h28 := stitchAt 28 4 frame044scope07_s028 h32
  have h24 := stitchAt 24 4 frame044scope07_s024 h28
  have h20 := stitchAt 20 4 frame044scope07_s020 h24
  have h16 := stitchAt 16 4 frame044scope07_s016 h20
  have h12 := stitchAt 12 4 frame044scope07_s012 h16
  have h8 := stitchAt 8 4 frame044scope07_s008 h12
  have h4 := stitchAt 4 4 frame044scope07_s004 h8
  have h0 := stitchAt 0 4 frame044scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame044batch07 : batch07.pickTest original frame92=true :=
  FitBatch.pickTest_of_scoped scoped044 frame044scope07

private theorem frameBatches044 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame92)=true := by
  simp only [List.all_cons,List.all_nil,frame044batch00,frame044batch01,frame044batch02,frame044batch03,frame044batch04,frame044batch05,frame044batch06,frame044batch07,Bool.and_self]

theorem frameOK044 : frameRankTest original useStop frame92=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches044

theorem stripOK045 : stripTest frame93=true := by decide +kernel

theorem spanOK045 : checkChain 1752 1750 [frame93.span]=true := by decide +kernel

private theorem guideAt045 : List.lookup frame93.span.1 guideTable=some guide045 := by
  decide +kernel

private theorem scoped045 : original.guide frame93.span.1 =
    (fun z => List.lookup (guideCode z) guide045) := by
  funext z
  change (List.lookup frame93.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide045
  simp only [guideAt045,Option.bind_some]

private abbrev frame045test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch00.stop,F)

private theorem frame045scope00_s000 : ((fits00.drop 0).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s004 : ((fits00.drop 4).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s008 : ((fits00.drop 8).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s012 : ((fits00.drop 12).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s016 : ((fits00.drop 16).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s020 : ((fits00.drop 20).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s024 : ((fits00.drop 24).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s028 : ((fits00.drop 28).take 4).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_s032 : ((fits00.drop 32).take 3).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00_end : (fits00.drop 35).all frame045test00=true := by
  decide +kernel

private theorem frame045scope00 : fits00.all frame045test00=true := by
  have h32 := stitchAt 32 3 frame045scope00_s032 frame045scope00_end
  have h28 := stitchAt 28 4 frame045scope00_s028 h32
  have h24 := stitchAt 24 4 frame045scope00_s024 h28
  have h20 := stitchAt 20 4 frame045scope00_s020 h24
  have h16 := stitchAt 16 4 frame045scope00_s016 h20
  have h12 := stitchAt 12 4 frame045scope00_s012 h16
  have h8 := stitchAt 8 4 frame045scope00_s008 h12
  have h4 := stitchAt 4 4 frame045scope00_s004 h8
  have h0 := stitchAt 0 4 frame045scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch00 : batch00.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope00

private abbrev frame045test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch01.stop,F)

private theorem frame045scope01_s000 : ((fits01.drop 0).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s004 : ((fits01.drop 4).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s008 : ((fits01.drop 8).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s012 : ((fits01.drop 12).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s016 : ((fits01.drop 16).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s020 : ((fits01.drop 20).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s024 : ((fits01.drop 24).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s028 : ((fits01.drop 28).take 4).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_s032 : ((fits01.drop 32).take 3).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01_end : (fits01.drop 35).all frame045test01=true := by
  decide +kernel

private theorem frame045scope01 : fits01.all frame045test01=true := by
  have h32 := stitchAt 32 3 frame045scope01_s032 frame045scope01_end
  have h28 := stitchAt 28 4 frame045scope01_s028 h32
  have h24 := stitchAt 24 4 frame045scope01_s024 h28
  have h20 := stitchAt 20 4 frame045scope01_s020 h24
  have h16 := stitchAt 16 4 frame045scope01_s016 h20
  have h12 := stitchAt 12 4 frame045scope01_s012 h16
  have h8 := stitchAt 8 4 frame045scope01_s008 h12
  have h4 := stitchAt 4 4 frame045scope01_s004 h8
  have h0 := stitchAt 0 4 frame045scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch01 : batch01.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope01

private abbrev frame045test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch02.stop,F)

private theorem frame045scope02_s000 : ((fits02.drop 0).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s004 : ((fits02.drop 4).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s008 : ((fits02.drop 8).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s012 : ((fits02.drop 12).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s016 : ((fits02.drop 16).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s020 : ((fits02.drop 20).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s024 : ((fits02.drop 24).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s028 : ((fits02.drop 28).take 4).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_s032 : ((fits02.drop 32).take 3).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02_end : (fits02.drop 35).all frame045test02=true := by
  decide +kernel

private theorem frame045scope02 : fits02.all frame045test02=true := by
  have h32 := stitchAt 32 3 frame045scope02_s032 frame045scope02_end
  have h28 := stitchAt 28 4 frame045scope02_s028 h32
  have h24 := stitchAt 24 4 frame045scope02_s024 h28
  have h20 := stitchAt 20 4 frame045scope02_s020 h24
  have h16 := stitchAt 16 4 frame045scope02_s016 h20
  have h12 := stitchAt 12 4 frame045scope02_s012 h16
  have h8 := stitchAt 8 4 frame045scope02_s008 h12
  have h4 := stitchAt 4 4 frame045scope02_s004 h8
  have h0 := stitchAt 0 4 frame045scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch02 : batch02.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope02

private abbrev frame045test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch03.stop,F)

private theorem frame045scope03_s000 : ((fits03.drop 0).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s004 : ((fits03.drop 4).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s008 : ((fits03.drop 8).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s012 : ((fits03.drop 12).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s016 : ((fits03.drop 16).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s020 : ((fits03.drop 20).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s024 : ((fits03.drop 24).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s028 : ((fits03.drop 28).take 4).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_s032 : ((fits03.drop 32).take 3).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03_end : (fits03.drop 35).all frame045test03=true := by
  decide +kernel

private theorem frame045scope03 : fits03.all frame045test03=true := by
  have h32 := stitchAt 32 3 frame045scope03_s032 frame045scope03_end
  have h28 := stitchAt 28 4 frame045scope03_s028 h32
  have h24 := stitchAt 24 4 frame045scope03_s024 h28
  have h20 := stitchAt 20 4 frame045scope03_s020 h24
  have h16 := stitchAt 16 4 frame045scope03_s016 h20
  have h12 := stitchAt 12 4 frame045scope03_s012 h16
  have h8 := stitchAt 8 4 frame045scope03_s008 h12
  have h4 := stitchAt 4 4 frame045scope03_s004 h8
  have h0 := stitchAt 0 4 frame045scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch03 : batch03.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope03

private abbrev frame045test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch04.stop,F)

private theorem frame045scope04_s000 : ((fits04.drop 0).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s004 : ((fits04.drop 4).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s008 : ((fits04.drop 8).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s012 : ((fits04.drop 12).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s016 : ((fits04.drop 16).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s020 : ((fits04.drop 20).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s024 : ((fits04.drop 24).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s028 : ((fits04.drop 28).take 4).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_s032 : ((fits04.drop 32).take 3).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04_end : (fits04.drop 35).all frame045test04=true := by
  decide +kernel

private theorem frame045scope04 : fits04.all frame045test04=true := by
  have h32 := stitchAt 32 3 frame045scope04_s032 frame045scope04_end
  have h28 := stitchAt 28 4 frame045scope04_s028 h32
  have h24 := stitchAt 24 4 frame045scope04_s024 h28
  have h20 := stitchAt 20 4 frame045scope04_s020 h24
  have h16 := stitchAt 16 4 frame045scope04_s016 h20
  have h12 := stitchAt 12 4 frame045scope04_s012 h16
  have h8 := stitchAt 8 4 frame045scope04_s008 h12
  have h4 := stitchAt 4 4 frame045scope04_s004 h8
  have h0 := stitchAt 0 4 frame045scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch04 : batch04.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope04

private abbrev frame045test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch05.stop,F)

private theorem frame045scope05_s000 : ((fits05.drop 0).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s004 : ((fits05.drop 4).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s008 : ((fits05.drop 8).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s012 : ((fits05.drop 12).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s016 : ((fits05.drop 16).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s020 : ((fits05.drop 20).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s024 : ((fits05.drop 24).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s028 : ((fits05.drop 28).take 4).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_s032 : ((fits05.drop 32).take 3).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05_end : (fits05.drop 35).all frame045test05=true := by
  decide +kernel

private theorem frame045scope05 : fits05.all frame045test05=true := by
  have h32 := stitchAt 32 3 frame045scope05_s032 frame045scope05_end
  have h28 := stitchAt 28 4 frame045scope05_s028 h32
  have h24 := stitchAt 24 4 frame045scope05_s024 h28
  have h20 := stitchAt 20 4 frame045scope05_s020 h24
  have h16 := stitchAt 16 4 frame045scope05_s016 h20
  have h12 := stitchAt 12 4 frame045scope05_s012 h16
  have h8 := stitchAt 8 4 frame045scope05_s008 h12
  have h4 := stitchAt 4 4 frame045scope05_s004 h8
  have h0 := stitchAt 0 4 frame045scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch05 : batch05.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope05

private abbrev frame045test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch06.stop,F)

private theorem frame045scope06_s000 : ((fits06.drop 0).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s004 : ((fits06.drop 4).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s008 : ((fits06.drop 8).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s012 : ((fits06.drop 12).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s016 : ((fits06.drop 16).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s020 : ((fits06.drop 20).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s024 : ((fits06.drop 24).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s028 : ((fits06.drop 28).take 4).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_s032 : ((fits06.drop 32).take 3).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06_end : (fits06.drop 35).all frame045test06=true := by
  decide +kernel

private theorem frame045scope06 : fits06.all frame045test06=true := by
  have h32 := stitchAt 32 3 frame045scope06_s032 frame045scope06_end
  have h28 := stitchAt 28 4 frame045scope06_s028 h32
  have h24 := stitchAt 24 4 frame045scope06_s024 h28
  have h20 := stitchAt 20 4 frame045scope06_s020 h24
  have h16 := stitchAt 16 4 frame045scope06_s016 h20
  have h12 := stitchAt 12 4 frame045scope06_s012 h16
  have h8 := stitchAt 8 4 frame045scope06_s008 h12
  have h4 := stitchAt 4 4 frame045scope06_s004 h8
  have h0 := stitchAt 0 4 frame045scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch06 : batch06.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope06

private abbrev frame045test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame93 (fun z => List.lookup (guideCode z) guide045)
    (batch07.stop,F)

private theorem frame045scope07_s000 : ((fits07.drop 0).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s004 : ((fits07.drop 4).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s008 : ((fits07.drop 8).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s012 : ((fits07.drop 12).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s016 : ((fits07.drop 16).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s020 : ((fits07.drop 20).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s024 : ((fits07.drop 24).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s028 : ((fits07.drop 28).take 4).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_s032 : ((fits07.drop 32).take 3).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07_end : (fits07.drop 35).all frame045test07=true := by
  decide +kernel

private theorem frame045scope07 : fits07.all frame045test07=true := by
  have h32 := stitchAt 32 3 frame045scope07_s032 frame045scope07_end
  have h28 := stitchAt 28 4 frame045scope07_s028 h32
  have h24 := stitchAt 24 4 frame045scope07_s024 h28
  have h20 := stitchAt 20 4 frame045scope07_s020 h24
  have h16 := stitchAt 16 4 frame045scope07_s016 h20
  have h12 := stitchAt 12 4 frame045scope07_s012 h16
  have h8 := stitchAt 8 4 frame045scope07_s008 h12
  have h4 := stitchAt 4 4 frame045scope07_s004 h8
  have h0 := stitchAt 0 4 frame045scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame045batch07 : batch07.pickTest original frame93=true :=
  FitBatch.pickTest_of_scoped scoped045 frame045scope07

private theorem frameBatches045 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame93)=true := by
  simp only [List.all_cons,List.all_nil,frame045batch00,frame045batch01,frame045batch02,frame045batch03,frame045batch04,frame045batch05,frame045batch06,frame045batch07,Bool.and_self]

theorem frameOK045 : frameRankTest original useStop frame93=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches045


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
