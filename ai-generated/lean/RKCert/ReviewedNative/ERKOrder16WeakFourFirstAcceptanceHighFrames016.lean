module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK032 : stripTest frame67=true := by decide +kernel

theorem spanOK032 : checkChain 1696 1688 [frame67.span]=true := by decide +kernel

private theorem guideAt032 : List.lookup frame67.span.1 guideTable=some guide032 := by
  decide +kernel

private theorem scoped032 : original.guide frame67.span.1 =
    (fun z => List.lookup (guideCode z) guide032) := by
  funext z
  change (List.lookup frame67.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide032
  simp only [guideAt032,Option.bind_some]

private abbrev frame032test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch00.stop,F)

private theorem frame032scope00_s000 : ((fits00.drop 0).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s004 : ((fits00.drop 4).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s008 : ((fits00.drop 8).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s012 : ((fits00.drop 12).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s016 : ((fits00.drop 16).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s020 : ((fits00.drop 20).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s024 : ((fits00.drop 24).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s028 : ((fits00.drop 28).take 4).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_s032 : ((fits00.drop 32).take 3).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00_end : (fits00.drop 35).all frame032test00=true := by
  decide +kernel

private theorem frame032scope00 : fits00.all frame032test00=true := by
  have h32 := stitchAt 32 3 frame032scope00_s032 frame032scope00_end
  have h28 := stitchAt 28 4 frame032scope00_s028 h32
  have h24 := stitchAt 24 4 frame032scope00_s024 h28
  have h20 := stitchAt 20 4 frame032scope00_s020 h24
  have h16 := stitchAt 16 4 frame032scope00_s016 h20
  have h12 := stitchAt 12 4 frame032scope00_s012 h16
  have h8 := stitchAt 8 4 frame032scope00_s008 h12
  have h4 := stitchAt 4 4 frame032scope00_s004 h8
  have h0 := stitchAt 0 4 frame032scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch00 : batch00.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope00

private abbrev frame032test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch01.stop,F)

private theorem frame032scope01_s000 : ((fits01.drop 0).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s004 : ((fits01.drop 4).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s008 : ((fits01.drop 8).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s012 : ((fits01.drop 12).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s016 : ((fits01.drop 16).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s020 : ((fits01.drop 20).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s024 : ((fits01.drop 24).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s028 : ((fits01.drop 28).take 4).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_s032 : ((fits01.drop 32).take 3).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01_end : (fits01.drop 35).all frame032test01=true := by
  decide +kernel

private theorem frame032scope01 : fits01.all frame032test01=true := by
  have h32 := stitchAt 32 3 frame032scope01_s032 frame032scope01_end
  have h28 := stitchAt 28 4 frame032scope01_s028 h32
  have h24 := stitchAt 24 4 frame032scope01_s024 h28
  have h20 := stitchAt 20 4 frame032scope01_s020 h24
  have h16 := stitchAt 16 4 frame032scope01_s016 h20
  have h12 := stitchAt 12 4 frame032scope01_s012 h16
  have h8 := stitchAt 8 4 frame032scope01_s008 h12
  have h4 := stitchAt 4 4 frame032scope01_s004 h8
  have h0 := stitchAt 0 4 frame032scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch01 : batch01.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope01

private abbrev frame032test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch02.stop,F)

private theorem frame032scope02_s000 : ((fits02.drop 0).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s004 : ((fits02.drop 4).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s008 : ((fits02.drop 8).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s012 : ((fits02.drop 12).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s016 : ((fits02.drop 16).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s020 : ((fits02.drop 20).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s024 : ((fits02.drop 24).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s028 : ((fits02.drop 28).take 4).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_s032 : ((fits02.drop 32).take 3).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02_end : (fits02.drop 35).all frame032test02=true := by
  decide +kernel

private theorem frame032scope02 : fits02.all frame032test02=true := by
  have h32 := stitchAt 32 3 frame032scope02_s032 frame032scope02_end
  have h28 := stitchAt 28 4 frame032scope02_s028 h32
  have h24 := stitchAt 24 4 frame032scope02_s024 h28
  have h20 := stitchAt 20 4 frame032scope02_s020 h24
  have h16 := stitchAt 16 4 frame032scope02_s016 h20
  have h12 := stitchAt 12 4 frame032scope02_s012 h16
  have h8 := stitchAt 8 4 frame032scope02_s008 h12
  have h4 := stitchAt 4 4 frame032scope02_s004 h8
  have h0 := stitchAt 0 4 frame032scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch02 : batch02.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope02

private abbrev frame032test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch03.stop,F)

private theorem frame032scope03_s000 : ((fits03.drop 0).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s004 : ((fits03.drop 4).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s008 : ((fits03.drop 8).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s012 : ((fits03.drop 12).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s016 : ((fits03.drop 16).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s020 : ((fits03.drop 20).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s024 : ((fits03.drop 24).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s028 : ((fits03.drop 28).take 4).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_s032 : ((fits03.drop 32).take 3).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03_end : (fits03.drop 35).all frame032test03=true := by
  decide +kernel

private theorem frame032scope03 : fits03.all frame032test03=true := by
  have h32 := stitchAt 32 3 frame032scope03_s032 frame032scope03_end
  have h28 := stitchAt 28 4 frame032scope03_s028 h32
  have h24 := stitchAt 24 4 frame032scope03_s024 h28
  have h20 := stitchAt 20 4 frame032scope03_s020 h24
  have h16 := stitchAt 16 4 frame032scope03_s016 h20
  have h12 := stitchAt 12 4 frame032scope03_s012 h16
  have h8 := stitchAt 8 4 frame032scope03_s008 h12
  have h4 := stitchAt 4 4 frame032scope03_s004 h8
  have h0 := stitchAt 0 4 frame032scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch03 : batch03.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope03

private abbrev frame032test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch04.stop,F)

private theorem frame032scope04_s000 : ((fits04.drop 0).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s004 : ((fits04.drop 4).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s008 : ((fits04.drop 8).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s012 : ((fits04.drop 12).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s016 : ((fits04.drop 16).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s020 : ((fits04.drop 20).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s024 : ((fits04.drop 24).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s028 : ((fits04.drop 28).take 4).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_s032 : ((fits04.drop 32).take 3).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04_end : (fits04.drop 35).all frame032test04=true := by
  decide +kernel

private theorem frame032scope04 : fits04.all frame032test04=true := by
  have h32 := stitchAt 32 3 frame032scope04_s032 frame032scope04_end
  have h28 := stitchAt 28 4 frame032scope04_s028 h32
  have h24 := stitchAt 24 4 frame032scope04_s024 h28
  have h20 := stitchAt 20 4 frame032scope04_s020 h24
  have h16 := stitchAt 16 4 frame032scope04_s016 h20
  have h12 := stitchAt 12 4 frame032scope04_s012 h16
  have h8 := stitchAt 8 4 frame032scope04_s008 h12
  have h4 := stitchAt 4 4 frame032scope04_s004 h8
  have h0 := stitchAt 0 4 frame032scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch04 : batch04.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope04

private abbrev frame032test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch05.stop,F)

private theorem frame032scope05_s000 : ((fits05.drop 0).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s004 : ((fits05.drop 4).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s008 : ((fits05.drop 8).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s012 : ((fits05.drop 12).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s016 : ((fits05.drop 16).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s020 : ((fits05.drop 20).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s024 : ((fits05.drop 24).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s028 : ((fits05.drop 28).take 4).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_s032 : ((fits05.drop 32).take 3).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05_end : (fits05.drop 35).all frame032test05=true := by
  decide +kernel

private theorem frame032scope05 : fits05.all frame032test05=true := by
  have h32 := stitchAt 32 3 frame032scope05_s032 frame032scope05_end
  have h28 := stitchAt 28 4 frame032scope05_s028 h32
  have h24 := stitchAt 24 4 frame032scope05_s024 h28
  have h20 := stitchAt 20 4 frame032scope05_s020 h24
  have h16 := stitchAt 16 4 frame032scope05_s016 h20
  have h12 := stitchAt 12 4 frame032scope05_s012 h16
  have h8 := stitchAt 8 4 frame032scope05_s008 h12
  have h4 := stitchAt 4 4 frame032scope05_s004 h8
  have h0 := stitchAt 0 4 frame032scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch05 : batch05.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope05

private abbrev frame032test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch06.stop,F)

private theorem frame032scope06_s000 : ((fits06.drop 0).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s004 : ((fits06.drop 4).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s008 : ((fits06.drop 8).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s012 : ((fits06.drop 12).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s016 : ((fits06.drop 16).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s020 : ((fits06.drop 20).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s024 : ((fits06.drop 24).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s028 : ((fits06.drop 28).take 4).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_s032 : ((fits06.drop 32).take 3).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06_end : (fits06.drop 35).all frame032test06=true := by
  decide +kernel

private theorem frame032scope06 : fits06.all frame032test06=true := by
  have h32 := stitchAt 32 3 frame032scope06_s032 frame032scope06_end
  have h28 := stitchAt 28 4 frame032scope06_s028 h32
  have h24 := stitchAt 24 4 frame032scope06_s024 h28
  have h20 := stitchAt 20 4 frame032scope06_s020 h24
  have h16 := stitchAt 16 4 frame032scope06_s016 h20
  have h12 := stitchAt 12 4 frame032scope06_s012 h16
  have h8 := stitchAt 8 4 frame032scope06_s008 h12
  have h4 := stitchAt 4 4 frame032scope06_s004 h8
  have h0 := stitchAt 0 4 frame032scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch06 : batch06.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope06

private abbrev frame032test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame67 (fun z => List.lookup (guideCode z) guide032)
    (batch07.stop,F)

private theorem frame032scope07_s000 : ((fits07.drop 0).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s004 : ((fits07.drop 4).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s008 : ((fits07.drop 8).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s012 : ((fits07.drop 12).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s016 : ((fits07.drop 16).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s020 : ((fits07.drop 20).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s024 : ((fits07.drop 24).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s028 : ((fits07.drop 28).take 4).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_s032 : ((fits07.drop 32).take 3).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07_end : (fits07.drop 35).all frame032test07=true := by
  decide +kernel

private theorem frame032scope07 : fits07.all frame032test07=true := by
  have h32 := stitchAt 32 3 frame032scope07_s032 frame032scope07_end
  have h28 := stitchAt 28 4 frame032scope07_s028 h32
  have h24 := stitchAt 24 4 frame032scope07_s024 h28
  have h20 := stitchAt 20 4 frame032scope07_s020 h24
  have h16 := stitchAt 16 4 frame032scope07_s016 h20
  have h12 := stitchAt 12 4 frame032scope07_s012 h16
  have h8 := stitchAt 8 4 frame032scope07_s008 h12
  have h4 := stitchAt 4 4 frame032scope07_s004 h8
  have h0 := stitchAt 0 4 frame032scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame032batch07 : batch07.pickTest original frame67=true :=
  FitBatch.pickTest_of_scoped scoped032 frame032scope07

private theorem frameBatches032 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame67)=true := by
  simp only [List.all_cons,List.all_nil,frame032batch00,frame032batch01,frame032batch02,frame032batch03,frame032batch04,frame032batch05,frame032batch06,frame032batch07,Bool.and_self]

theorem frameOK032 : frameRankTest original useStop frame67=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches032

theorem stripOK033 : stripTest frame70=true := by decide +kernel

theorem spanOK033 : checkChain 1704 1696 [frame70.span]=true := by decide +kernel

private theorem guideAt033 : List.lookup frame70.span.1 guideTable=some guide033 := by
  decide +kernel

private theorem scoped033 : original.guide frame70.span.1 =
    (fun z => List.lookup (guideCode z) guide033) := by
  funext z
  change (List.lookup frame70.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide033
  simp only [guideAt033,Option.bind_some]

private abbrev frame033test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch00.stop,F)

private theorem frame033scope00_s000 : ((fits00.drop 0).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s004 : ((fits00.drop 4).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s008 : ((fits00.drop 8).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s012 : ((fits00.drop 12).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s016 : ((fits00.drop 16).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s020 : ((fits00.drop 20).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s024 : ((fits00.drop 24).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s028 : ((fits00.drop 28).take 4).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_s032 : ((fits00.drop 32).take 3).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00_end : (fits00.drop 35).all frame033test00=true := by
  decide +kernel

private theorem frame033scope00 : fits00.all frame033test00=true := by
  have h32 := stitchAt 32 3 frame033scope00_s032 frame033scope00_end
  have h28 := stitchAt 28 4 frame033scope00_s028 h32
  have h24 := stitchAt 24 4 frame033scope00_s024 h28
  have h20 := stitchAt 20 4 frame033scope00_s020 h24
  have h16 := stitchAt 16 4 frame033scope00_s016 h20
  have h12 := stitchAt 12 4 frame033scope00_s012 h16
  have h8 := stitchAt 8 4 frame033scope00_s008 h12
  have h4 := stitchAt 4 4 frame033scope00_s004 h8
  have h0 := stitchAt 0 4 frame033scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch00 : batch00.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope00

private abbrev frame033test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch01.stop,F)

private theorem frame033scope01_s000 : ((fits01.drop 0).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s004 : ((fits01.drop 4).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s008 : ((fits01.drop 8).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s012 : ((fits01.drop 12).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s016 : ((fits01.drop 16).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s020 : ((fits01.drop 20).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s024 : ((fits01.drop 24).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s028 : ((fits01.drop 28).take 4).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_s032 : ((fits01.drop 32).take 3).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01_end : (fits01.drop 35).all frame033test01=true := by
  decide +kernel

private theorem frame033scope01 : fits01.all frame033test01=true := by
  have h32 := stitchAt 32 3 frame033scope01_s032 frame033scope01_end
  have h28 := stitchAt 28 4 frame033scope01_s028 h32
  have h24 := stitchAt 24 4 frame033scope01_s024 h28
  have h20 := stitchAt 20 4 frame033scope01_s020 h24
  have h16 := stitchAt 16 4 frame033scope01_s016 h20
  have h12 := stitchAt 12 4 frame033scope01_s012 h16
  have h8 := stitchAt 8 4 frame033scope01_s008 h12
  have h4 := stitchAt 4 4 frame033scope01_s004 h8
  have h0 := stitchAt 0 4 frame033scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch01 : batch01.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope01

private abbrev frame033test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch02.stop,F)

private theorem frame033scope02_s000 : ((fits02.drop 0).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s004 : ((fits02.drop 4).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s008 : ((fits02.drop 8).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s012 : ((fits02.drop 12).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s016 : ((fits02.drop 16).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s020 : ((fits02.drop 20).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s024 : ((fits02.drop 24).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s028 : ((fits02.drop 28).take 4).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_s032 : ((fits02.drop 32).take 3).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02_end : (fits02.drop 35).all frame033test02=true := by
  decide +kernel

private theorem frame033scope02 : fits02.all frame033test02=true := by
  have h32 := stitchAt 32 3 frame033scope02_s032 frame033scope02_end
  have h28 := stitchAt 28 4 frame033scope02_s028 h32
  have h24 := stitchAt 24 4 frame033scope02_s024 h28
  have h20 := stitchAt 20 4 frame033scope02_s020 h24
  have h16 := stitchAt 16 4 frame033scope02_s016 h20
  have h12 := stitchAt 12 4 frame033scope02_s012 h16
  have h8 := stitchAt 8 4 frame033scope02_s008 h12
  have h4 := stitchAt 4 4 frame033scope02_s004 h8
  have h0 := stitchAt 0 4 frame033scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch02 : batch02.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope02

private abbrev frame033test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch03.stop,F)

private theorem frame033scope03_s000 : ((fits03.drop 0).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s004 : ((fits03.drop 4).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s008 : ((fits03.drop 8).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s012 : ((fits03.drop 12).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s016 : ((fits03.drop 16).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s020 : ((fits03.drop 20).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s024 : ((fits03.drop 24).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s028 : ((fits03.drop 28).take 4).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_s032 : ((fits03.drop 32).take 3).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03_end : (fits03.drop 35).all frame033test03=true := by
  decide +kernel

private theorem frame033scope03 : fits03.all frame033test03=true := by
  have h32 := stitchAt 32 3 frame033scope03_s032 frame033scope03_end
  have h28 := stitchAt 28 4 frame033scope03_s028 h32
  have h24 := stitchAt 24 4 frame033scope03_s024 h28
  have h20 := stitchAt 20 4 frame033scope03_s020 h24
  have h16 := stitchAt 16 4 frame033scope03_s016 h20
  have h12 := stitchAt 12 4 frame033scope03_s012 h16
  have h8 := stitchAt 8 4 frame033scope03_s008 h12
  have h4 := stitchAt 4 4 frame033scope03_s004 h8
  have h0 := stitchAt 0 4 frame033scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch03 : batch03.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope03

private abbrev frame033test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch04.stop,F)

private theorem frame033scope04_s000 : ((fits04.drop 0).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s004 : ((fits04.drop 4).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s008 : ((fits04.drop 8).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s012 : ((fits04.drop 12).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s016 : ((fits04.drop 16).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s020 : ((fits04.drop 20).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s024 : ((fits04.drop 24).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s028 : ((fits04.drop 28).take 4).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_s032 : ((fits04.drop 32).take 3).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04_end : (fits04.drop 35).all frame033test04=true := by
  decide +kernel

private theorem frame033scope04 : fits04.all frame033test04=true := by
  have h32 := stitchAt 32 3 frame033scope04_s032 frame033scope04_end
  have h28 := stitchAt 28 4 frame033scope04_s028 h32
  have h24 := stitchAt 24 4 frame033scope04_s024 h28
  have h20 := stitchAt 20 4 frame033scope04_s020 h24
  have h16 := stitchAt 16 4 frame033scope04_s016 h20
  have h12 := stitchAt 12 4 frame033scope04_s012 h16
  have h8 := stitchAt 8 4 frame033scope04_s008 h12
  have h4 := stitchAt 4 4 frame033scope04_s004 h8
  have h0 := stitchAt 0 4 frame033scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch04 : batch04.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope04

private abbrev frame033test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch05.stop,F)

private theorem frame033scope05_s000 : ((fits05.drop 0).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s004 : ((fits05.drop 4).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s008 : ((fits05.drop 8).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s012 : ((fits05.drop 12).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s016 : ((fits05.drop 16).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s020 : ((fits05.drop 20).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s024 : ((fits05.drop 24).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s028 : ((fits05.drop 28).take 4).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_s032 : ((fits05.drop 32).take 3).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05_end : (fits05.drop 35).all frame033test05=true := by
  decide +kernel

private theorem frame033scope05 : fits05.all frame033test05=true := by
  have h32 := stitchAt 32 3 frame033scope05_s032 frame033scope05_end
  have h28 := stitchAt 28 4 frame033scope05_s028 h32
  have h24 := stitchAt 24 4 frame033scope05_s024 h28
  have h20 := stitchAt 20 4 frame033scope05_s020 h24
  have h16 := stitchAt 16 4 frame033scope05_s016 h20
  have h12 := stitchAt 12 4 frame033scope05_s012 h16
  have h8 := stitchAt 8 4 frame033scope05_s008 h12
  have h4 := stitchAt 4 4 frame033scope05_s004 h8
  have h0 := stitchAt 0 4 frame033scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch05 : batch05.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope05

private abbrev frame033test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch06.stop,F)

private theorem frame033scope06_s000 : ((fits06.drop 0).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s004 : ((fits06.drop 4).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s008 : ((fits06.drop 8).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s012 : ((fits06.drop 12).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s016 : ((fits06.drop 16).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s020 : ((fits06.drop 20).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s024 : ((fits06.drop 24).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s028 : ((fits06.drop 28).take 4).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_s032 : ((fits06.drop 32).take 3).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06_end : (fits06.drop 35).all frame033test06=true := by
  decide +kernel

private theorem frame033scope06 : fits06.all frame033test06=true := by
  have h32 := stitchAt 32 3 frame033scope06_s032 frame033scope06_end
  have h28 := stitchAt 28 4 frame033scope06_s028 h32
  have h24 := stitchAt 24 4 frame033scope06_s024 h28
  have h20 := stitchAt 20 4 frame033scope06_s020 h24
  have h16 := stitchAt 16 4 frame033scope06_s016 h20
  have h12 := stitchAt 12 4 frame033scope06_s012 h16
  have h8 := stitchAt 8 4 frame033scope06_s008 h12
  have h4 := stitchAt 4 4 frame033scope06_s004 h8
  have h0 := stitchAt 0 4 frame033scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch06 : batch06.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope06

private abbrev frame033test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame70 (fun z => List.lookup (guideCode z) guide033)
    (batch07.stop,F)

private theorem frame033scope07_s000 : ((fits07.drop 0).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s004 : ((fits07.drop 4).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s008 : ((fits07.drop 8).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s012 : ((fits07.drop 12).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s016 : ((fits07.drop 16).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s020 : ((fits07.drop 20).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s024 : ((fits07.drop 24).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s028 : ((fits07.drop 28).take 4).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_s032 : ((fits07.drop 32).take 3).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07_end : (fits07.drop 35).all frame033test07=true := by
  decide +kernel

private theorem frame033scope07 : fits07.all frame033test07=true := by
  have h32 := stitchAt 32 3 frame033scope07_s032 frame033scope07_end
  have h28 := stitchAt 28 4 frame033scope07_s028 h32
  have h24 := stitchAt 24 4 frame033scope07_s024 h28
  have h20 := stitchAt 20 4 frame033scope07_s020 h24
  have h16 := stitchAt 16 4 frame033scope07_s016 h20
  have h12 := stitchAt 12 4 frame033scope07_s012 h16
  have h8 := stitchAt 8 4 frame033scope07_s008 h12
  have h4 := stitchAt 4 4 frame033scope07_s004 h8
  have h0 := stitchAt 0 4 frame033scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame033batch07 : batch07.pickTest original frame70=true :=
  FitBatch.pickTest_of_scoped scoped033 frame033scope07

private theorem frameBatches033 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame70)=true := by
  simp only [List.all_cons,List.all_nil,frame033batch00,frame033batch01,frame033batch02,frame033batch03,frame033batch04,frame033batch05,frame033batch06,frame033batch07,Bool.and_self]

theorem frameOK033 : frameRankTest original useStop frame70=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches033


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
