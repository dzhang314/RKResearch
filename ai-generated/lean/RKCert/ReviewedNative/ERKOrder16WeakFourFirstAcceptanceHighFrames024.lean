module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK048 : stripTest frame99=true := by decide +kernel

theorem spanOK048 : checkChain 1758 1756 [frame99.span]=true := by decide +kernel

private theorem guideAt048 : List.lookup frame99.span.1 guideTable=some guide048 := by
  decide +kernel

private theorem scoped048 : original.guide frame99.span.1 =
    (fun z => List.lookup (guideCode z) guide048) := by
  funext z
  change (List.lookup frame99.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide048
  simp only [guideAt048,Option.bind_some]

private abbrev frame048test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch00.stop,F)

private theorem frame048scope00_s000 : ((fits00.drop 0).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s004 : ((fits00.drop 4).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s008 : ((fits00.drop 8).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s012 : ((fits00.drop 12).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s016 : ((fits00.drop 16).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s020 : ((fits00.drop 20).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s024 : ((fits00.drop 24).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s028 : ((fits00.drop 28).take 4).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_s032 : ((fits00.drop 32).take 3).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00_end : (fits00.drop 35).all frame048test00=true := by
  decide +kernel

private theorem frame048scope00 : fits00.all frame048test00=true := by
  have h32 := stitchAt 32 3 frame048scope00_s032 frame048scope00_end
  have h28 := stitchAt 28 4 frame048scope00_s028 h32
  have h24 := stitchAt 24 4 frame048scope00_s024 h28
  have h20 := stitchAt 20 4 frame048scope00_s020 h24
  have h16 := stitchAt 16 4 frame048scope00_s016 h20
  have h12 := stitchAt 12 4 frame048scope00_s012 h16
  have h8 := stitchAt 8 4 frame048scope00_s008 h12
  have h4 := stitchAt 4 4 frame048scope00_s004 h8
  have h0 := stitchAt 0 4 frame048scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch00 : batch00.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope00

private abbrev frame048test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch01.stop,F)

private theorem frame048scope01_s000 : ((fits01.drop 0).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s004 : ((fits01.drop 4).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s008 : ((fits01.drop 8).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s012 : ((fits01.drop 12).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s016 : ((fits01.drop 16).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s020 : ((fits01.drop 20).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s024 : ((fits01.drop 24).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s028 : ((fits01.drop 28).take 4).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_s032 : ((fits01.drop 32).take 3).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01_end : (fits01.drop 35).all frame048test01=true := by
  decide +kernel

private theorem frame048scope01 : fits01.all frame048test01=true := by
  have h32 := stitchAt 32 3 frame048scope01_s032 frame048scope01_end
  have h28 := stitchAt 28 4 frame048scope01_s028 h32
  have h24 := stitchAt 24 4 frame048scope01_s024 h28
  have h20 := stitchAt 20 4 frame048scope01_s020 h24
  have h16 := stitchAt 16 4 frame048scope01_s016 h20
  have h12 := stitchAt 12 4 frame048scope01_s012 h16
  have h8 := stitchAt 8 4 frame048scope01_s008 h12
  have h4 := stitchAt 4 4 frame048scope01_s004 h8
  have h0 := stitchAt 0 4 frame048scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch01 : batch01.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope01

private abbrev frame048test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch02.stop,F)

private theorem frame048scope02_s000 : ((fits02.drop 0).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s004 : ((fits02.drop 4).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s008 : ((fits02.drop 8).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s012 : ((fits02.drop 12).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s016 : ((fits02.drop 16).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s020 : ((fits02.drop 20).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s024 : ((fits02.drop 24).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s028 : ((fits02.drop 28).take 4).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_s032 : ((fits02.drop 32).take 3).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02_end : (fits02.drop 35).all frame048test02=true := by
  decide +kernel

private theorem frame048scope02 : fits02.all frame048test02=true := by
  have h32 := stitchAt 32 3 frame048scope02_s032 frame048scope02_end
  have h28 := stitchAt 28 4 frame048scope02_s028 h32
  have h24 := stitchAt 24 4 frame048scope02_s024 h28
  have h20 := stitchAt 20 4 frame048scope02_s020 h24
  have h16 := stitchAt 16 4 frame048scope02_s016 h20
  have h12 := stitchAt 12 4 frame048scope02_s012 h16
  have h8 := stitchAt 8 4 frame048scope02_s008 h12
  have h4 := stitchAt 4 4 frame048scope02_s004 h8
  have h0 := stitchAt 0 4 frame048scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch02 : batch02.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope02

private abbrev frame048test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch03.stop,F)

private theorem frame048scope03_s000 : ((fits03.drop 0).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s004 : ((fits03.drop 4).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s008 : ((fits03.drop 8).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s012 : ((fits03.drop 12).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s016 : ((fits03.drop 16).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s020 : ((fits03.drop 20).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s024 : ((fits03.drop 24).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s028 : ((fits03.drop 28).take 4).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_s032 : ((fits03.drop 32).take 3).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03_end : (fits03.drop 35).all frame048test03=true := by
  decide +kernel

private theorem frame048scope03 : fits03.all frame048test03=true := by
  have h32 := stitchAt 32 3 frame048scope03_s032 frame048scope03_end
  have h28 := stitchAt 28 4 frame048scope03_s028 h32
  have h24 := stitchAt 24 4 frame048scope03_s024 h28
  have h20 := stitchAt 20 4 frame048scope03_s020 h24
  have h16 := stitchAt 16 4 frame048scope03_s016 h20
  have h12 := stitchAt 12 4 frame048scope03_s012 h16
  have h8 := stitchAt 8 4 frame048scope03_s008 h12
  have h4 := stitchAt 4 4 frame048scope03_s004 h8
  have h0 := stitchAt 0 4 frame048scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch03 : batch03.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope03

private abbrev frame048test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch04.stop,F)

private theorem frame048scope04_s000 : ((fits04.drop 0).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s004 : ((fits04.drop 4).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s008 : ((fits04.drop 8).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s012 : ((fits04.drop 12).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s016 : ((fits04.drop 16).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s020 : ((fits04.drop 20).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s024 : ((fits04.drop 24).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s028 : ((fits04.drop 28).take 4).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_s032 : ((fits04.drop 32).take 3).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04_end : (fits04.drop 35).all frame048test04=true := by
  decide +kernel

private theorem frame048scope04 : fits04.all frame048test04=true := by
  have h32 := stitchAt 32 3 frame048scope04_s032 frame048scope04_end
  have h28 := stitchAt 28 4 frame048scope04_s028 h32
  have h24 := stitchAt 24 4 frame048scope04_s024 h28
  have h20 := stitchAt 20 4 frame048scope04_s020 h24
  have h16 := stitchAt 16 4 frame048scope04_s016 h20
  have h12 := stitchAt 12 4 frame048scope04_s012 h16
  have h8 := stitchAt 8 4 frame048scope04_s008 h12
  have h4 := stitchAt 4 4 frame048scope04_s004 h8
  have h0 := stitchAt 0 4 frame048scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch04 : batch04.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope04

private abbrev frame048test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch05.stop,F)

private theorem frame048scope05_s000 : ((fits05.drop 0).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s004 : ((fits05.drop 4).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s008 : ((fits05.drop 8).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s012 : ((fits05.drop 12).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s016 : ((fits05.drop 16).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s020 : ((fits05.drop 20).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s024 : ((fits05.drop 24).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s028 : ((fits05.drop 28).take 4).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_s032 : ((fits05.drop 32).take 3).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05_end : (fits05.drop 35).all frame048test05=true := by
  decide +kernel

private theorem frame048scope05 : fits05.all frame048test05=true := by
  have h32 := stitchAt 32 3 frame048scope05_s032 frame048scope05_end
  have h28 := stitchAt 28 4 frame048scope05_s028 h32
  have h24 := stitchAt 24 4 frame048scope05_s024 h28
  have h20 := stitchAt 20 4 frame048scope05_s020 h24
  have h16 := stitchAt 16 4 frame048scope05_s016 h20
  have h12 := stitchAt 12 4 frame048scope05_s012 h16
  have h8 := stitchAt 8 4 frame048scope05_s008 h12
  have h4 := stitchAt 4 4 frame048scope05_s004 h8
  have h0 := stitchAt 0 4 frame048scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch05 : batch05.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope05

private abbrev frame048test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch06.stop,F)

private theorem frame048scope06_s000 : ((fits06.drop 0).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s004 : ((fits06.drop 4).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s008 : ((fits06.drop 8).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s012 : ((fits06.drop 12).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s016 : ((fits06.drop 16).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s020 : ((fits06.drop 20).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s024 : ((fits06.drop 24).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s028 : ((fits06.drop 28).take 4).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_s032 : ((fits06.drop 32).take 3).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06_end : (fits06.drop 35).all frame048test06=true := by
  decide +kernel

private theorem frame048scope06 : fits06.all frame048test06=true := by
  have h32 := stitchAt 32 3 frame048scope06_s032 frame048scope06_end
  have h28 := stitchAt 28 4 frame048scope06_s028 h32
  have h24 := stitchAt 24 4 frame048scope06_s024 h28
  have h20 := stitchAt 20 4 frame048scope06_s020 h24
  have h16 := stitchAt 16 4 frame048scope06_s016 h20
  have h12 := stitchAt 12 4 frame048scope06_s012 h16
  have h8 := stitchAt 8 4 frame048scope06_s008 h12
  have h4 := stitchAt 4 4 frame048scope06_s004 h8
  have h0 := stitchAt 0 4 frame048scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch06 : batch06.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope06

private abbrev frame048test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame99 (fun z => List.lookup (guideCode z) guide048)
    (batch07.stop,F)

private theorem frame048scope07_s000 : ((fits07.drop 0).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s004 : ((fits07.drop 4).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s008 : ((fits07.drop 8).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s012 : ((fits07.drop 12).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s016 : ((fits07.drop 16).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s020 : ((fits07.drop 20).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s024 : ((fits07.drop 24).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s028 : ((fits07.drop 28).take 4).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_s032 : ((fits07.drop 32).take 3).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07_end : (fits07.drop 35).all frame048test07=true := by
  decide +kernel

private theorem frame048scope07 : fits07.all frame048test07=true := by
  have h32 := stitchAt 32 3 frame048scope07_s032 frame048scope07_end
  have h28 := stitchAt 28 4 frame048scope07_s028 h32
  have h24 := stitchAt 24 4 frame048scope07_s024 h28
  have h20 := stitchAt 20 4 frame048scope07_s020 h24
  have h16 := stitchAt 16 4 frame048scope07_s016 h20
  have h12 := stitchAt 12 4 frame048scope07_s012 h16
  have h8 := stitchAt 8 4 frame048scope07_s008 h12
  have h4 := stitchAt 4 4 frame048scope07_s004 h8
  have h0 := stitchAt 0 4 frame048scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame048batch07 : batch07.pickTest original frame99=true :=
  FitBatch.pickTest_of_scoped scoped048 frame048scope07

private theorem frameBatches048 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame99)=true := by
  simp only [List.all_cons,List.all_nil,frame048batch00,frame048batch01,frame048batch02,frame048batch03,frame048batch04,frame048batch05,frame048batch06,frame048batch07,Bool.and_self]

theorem frameOK048 : frameRankTest original useStop frame99=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches048

theorem stripOK049 : stripTest frame101=true := by decide +kernel

theorem spanOK049 : checkChain 1759 1758 [frame101.span]=true := by decide +kernel

private theorem guideAt049 : List.lookup frame101.span.1 guideTable=some guide049 := by
  decide +kernel

private theorem scoped049 : original.guide frame101.span.1 =
    (fun z => List.lookup (guideCode z) guide049) := by
  funext z
  change (List.lookup frame101.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide049
  simp only [guideAt049,Option.bind_some]

private abbrev frame049test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch00.stop,F)

private theorem frame049scope00_s000 : ((fits00.drop 0).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s004 : ((fits00.drop 4).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s008 : ((fits00.drop 8).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s012 : ((fits00.drop 12).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s016 : ((fits00.drop 16).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s020 : ((fits00.drop 20).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s024 : ((fits00.drop 24).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s028 : ((fits00.drop 28).take 4).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_s032 : ((fits00.drop 32).take 3).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00_end : (fits00.drop 35).all frame049test00=true := by
  decide +kernel

private theorem frame049scope00 : fits00.all frame049test00=true := by
  have h32 := stitchAt 32 3 frame049scope00_s032 frame049scope00_end
  have h28 := stitchAt 28 4 frame049scope00_s028 h32
  have h24 := stitchAt 24 4 frame049scope00_s024 h28
  have h20 := stitchAt 20 4 frame049scope00_s020 h24
  have h16 := stitchAt 16 4 frame049scope00_s016 h20
  have h12 := stitchAt 12 4 frame049scope00_s012 h16
  have h8 := stitchAt 8 4 frame049scope00_s008 h12
  have h4 := stitchAt 4 4 frame049scope00_s004 h8
  have h0 := stitchAt 0 4 frame049scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch00 : batch00.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope00

private abbrev frame049test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch01.stop,F)

private theorem frame049scope01_s000 : ((fits01.drop 0).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s004 : ((fits01.drop 4).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s008 : ((fits01.drop 8).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s012 : ((fits01.drop 12).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s016 : ((fits01.drop 16).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s020 : ((fits01.drop 20).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s024 : ((fits01.drop 24).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s028 : ((fits01.drop 28).take 4).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_s032 : ((fits01.drop 32).take 3).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01_end : (fits01.drop 35).all frame049test01=true := by
  decide +kernel

private theorem frame049scope01 : fits01.all frame049test01=true := by
  have h32 := stitchAt 32 3 frame049scope01_s032 frame049scope01_end
  have h28 := stitchAt 28 4 frame049scope01_s028 h32
  have h24 := stitchAt 24 4 frame049scope01_s024 h28
  have h20 := stitchAt 20 4 frame049scope01_s020 h24
  have h16 := stitchAt 16 4 frame049scope01_s016 h20
  have h12 := stitchAt 12 4 frame049scope01_s012 h16
  have h8 := stitchAt 8 4 frame049scope01_s008 h12
  have h4 := stitchAt 4 4 frame049scope01_s004 h8
  have h0 := stitchAt 0 4 frame049scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch01 : batch01.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope01

private abbrev frame049test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch02.stop,F)

private theorem frame049scope02_s000 : ((fits02.drop 0).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s004 : ((fits02.drop 4).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s008 : ((fits02.drop 8).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s012 : ((fits02.drop 12).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s016 : ((fits02.drop 16).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s020 : ((fits02.drop 20).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s024 : ((fits02.drop 24).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s028 : ((fits02.drop 28).take 4).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_s032 : ((fits02.drop 32).take 3).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02_end : (fits02.drop 35).all frame049test02=true := by
  decide +kernel

private theorem frame049scope02 : fits02.all frame049test02=true := by
  have h32 := stitchAt 32 3 frame049scope02_s032 frame049scope02_end
  have h28 := stitchAt 28 4 frame049scope02_s028 h32
  have h24 := stitchAt 24 4 frame049scope02_s024 h28
  have h20 := stitchAt 20 4 frame049scope02_s020 h24
  have h16 := stitchAt 16 4 frame049scope02_s016 h20
  have h12 := stitchAt 12 4 frame049scope02_s012 h16
  have h8 := stitchAt 8 4 frame049scope02_s008 h12
  have h4 := stitchAt 4 4 frame049scope02_s004 h8
  have h0 := stitchAt 0 4 frame049scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch02 : batch02.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope02

private abbrev frame049test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch03.stop,F)

private theorem frame049scope03_s000 : ((fits03.drop 0).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s004 : ((fits03.drop 4).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s008 : ((fits03.drop 8).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s012 : ((fits03.drop 12).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s016 : ((fits03.drop 16).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s020 : ((fits03.drop 20).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s024 : ((fits03.drop 24).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s028 : ((fits03.drop 28).take 4).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_s032 : ((fits03.drop 32).take 3).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03_end : (fits03.drop 35).all frame049test03=true := by
  decide +kernel

private theorem frame049scope03 : fits03.all frame049test03=true := by
  have h32 := stitchAt 32 3 frame049scope03_s032 frame049scope03_end
  have h28 := stitchAt 28 4 frame049scope03_s028 h32
  have h24 := stitchAt 24 4 frame049scope03_s024 h28
  have h20 := stitchAt 20 4 frame049scope03_s020 h24
  have h16 := stitchAt 16 4 frame049scope03_s016 h20
  have h12 := stitchAt 12 4 frame049scope03_s012 h16
  have h8 := stitchAt 8 4 frame049scope03_s008 h12
  have h4 := stitchAt 4 4 frame049scope03_s004 h8
  have h0 := stitchAt 0 4 frame049scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch03 : batch03.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope03

private abbrev frame049test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch04.stop,F)

private theorem frame049scope04_s000 : ((fits04.drop 0).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s004 : ((fits04.drop 4).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s008 : ((fits04.drop 8).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s012 : ((fits04.drop 12).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s016 : ((fits04.drop 16).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s020 : ((fits04.drop 20).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s024 : ((fits04.drop 24).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s028 : ((fits04.drop 28).take 4).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_s032 : ((fits04.drop 32).take 3).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04_end : (fits04.drop 35).all frame049test04=true := by
  decide +kernel

private theorem frame049scope04 : fits04.all frame049test04=true := by
  have h32 := stitchAt 32 3 frame049scope04_s032 frame049scope04_end
  have h28 := stitchAt 28 4 frame049scope04_s028 h32
  have h24 := stitchAt 24 4 frame049scope04_s024 h28
  have h20 := stitchAt 20 4 frame049scope04_s020 h24
  have h16 := stitchAt 16 4 frame049scope04_s016 h20
  have h12 := stitchAt 12 4 frame049scope04_s012 h16
  have h8 := stitchAt 8 4 frame049scope04_s008 h12
  have h4 := stitchAt 4 4 frame049scope04_s004 h8
  have h0 := stitchAt 0 4 frame049scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch04 : batch04.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope04

private abbrev frame049test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch05.stop,F)

private theorem frame049scope05_s000 : ((fits05.drop 0).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s004 : ((fits05.drop 4).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s008 : ((fits05.drop 8).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s012 : ((fits05.drop 12).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s016 : ((fits05.drop 16).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s020 : ((fits05.drop 20).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s024 : ((fits05.drop 24).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s028 : ((fits05.drop 28).take 4).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_s032 : ((fits05.drop 32).take 3).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05_end : (fits05.drop 35).all frame049test05=true := by
  decide +kernel

private theorem frame049scope05 : fits05.all frame049test05=true := by
  have h32 := stitchAt 32 3 frame049scope05_s032 frame049scope05_end
  have h28 := stitchAt 28 4 frame049scope05_s028 h32
  have h24 := stitchAt 24 4 frame049scope05_s024 h28
  have h20 := stitchAt 20 4 frame049scope05_s020 h24
  have h16 := stitchAt 16 4 frame049scope05_s016 h20
  have h12 := stitchAt 12 4 frame049scope05_s012 h16
  have h8 := stitchAt 8 4 frame049scope05_s008 h12
  have h4 := stitchAt 4 4 frame049scope05_s004 h8
  have h0 := stitchAt 0 4 frame049scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch05 : batch05.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope05

private abbrev frame049test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch06.stop,F)

private theorem frame049scope06_s000 : ((fits06.drop 0).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s004 : ((fits06.drop 4).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s008 : ((fits06.drop 8).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s012 : ((fits06.drop 12).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s016 : ((fits06.drop 16).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s020 : ((fits06.drop 20).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s024 : ((fits06.drop 24).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s028 : ((fits06.drop 28).take 4).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_s032 : ((fits06.drop 32).take 3).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06_end : (fits06.drop 35).all frame049test06=true := by
  decide +kernel

private theorem frame049scope06 : fits06.all frame049test06=true := by
  have h32 := stitchAt 32 3 frame049scope06_s032 frame049scope06_end
  have h28 := stitchAt 28 4 frame049scope06_s028 h32
  have h24 := stitchAt 24 4 frame049scope06_s024 h28
  have h20 := stitchAt 20 4 frame049scope06_s020 h24
  have h16 := stitchAt 16 4 frame049scope06_s016 h20
  have h12 := stitchAt 12 4 frame049scope06_s012 h16
  have h8 := stitchAt 8 4 frame049scope06_s008 h12
  have h4 := stitchAt 4 4 frame049scope06_s004 h8
  have h0 := stitchAt 0 4 frame049scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch06 : batch06.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope06

private abbrev frame049test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame101 (fun z => List.lookup (guideCode z) guide049)
    (batch07.stop,F)

private theorem frame049scope07_s000 : ((fits07.drop 0).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s004 : ((fits07.drop 4).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s008 : ((fits07.drop 8).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s012 : ((fits07.drop 12).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s016 : ((fits07.drop 16).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s020 : ((fits07.drop 20).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s024 : ((fits07.drop 24).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s028 : ((fits07.drop 28).take 4).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_s032 : ((fits07.drop 32).take 3).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07_end : (fits07.drop 35).all frame049test07=true := by
  decide +kernel

private theorem frame049scope07 : fits07.all frame049test07=true := by
  have h32 := stitchAt 32 3 frame049scope07_s032 frame049scope07_end
  have h28 := stitchAt 28 4 frame049scope07_s028 h32
  have h24 := stitchAt 24 4 frame049scope07_s024 h28
  have h20 := stitchAt 20 4 frame049scope07_s020 h24
  have h16 := stitchAt 16 4 frame049scope07_s016 h20
  have h12 := stitchAt 12 4 frame049scope07_s012 h16
  have h8 := stitchAt 8 4 frame049scope07_s008 h12
  have h4 := stitchAt 4 4 frame049scope07_s004 h8
  have h0 := stitchAt 0 4 frame049scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame049batch07 : batch07.pickTest original frame101=true :=
  FitBatch.pickTest_of_scoped scoped049 frame049scope07

private theorem frameBatches049 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame101)=true := by
  simp only [List.all_cons,List.all_nil,frame049batch00,frame049batch01,frame049batch02,frame049batch03,frame049batch04,frame049batch05,frame049batch06,frame049batch07,Bool.and_self]

theorem frameOK049 : frameRankTest original useStop frame101=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches049


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
