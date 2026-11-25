module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK022 : stripTest frame48=true := by decide +kernel

theorem spanOK022 : checkChain 1584 1568 [frame48.span]=true := by decide +kernel

private theorem guideAt022 : List.lookup frame48.span.1 guideTable=some guide022 := by
  decide +kernel

private theorem scoped022 : original.guide frame48.span.1 =
    (fun z => List.lookup (guideCode z) guide022) := by
  funext z
  change (List.lookup frame48.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide022
  simp only [guideAt022,Option.bind_some]

private abbrev frame022test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch00.stop,F)

private theorem frame022scope00_s000 : ((fits00.drop 0).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s004 : ((fits00.drop 4).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s008 : ((fits00.drop 8).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s012 : ((fits00.drop 12).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s016 : ((fits00.drop 16).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s020 : ((fits00.drop 20).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s024 : ((fits00.drop 24).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s028 : ((fits00.drop 28).take 4).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_s032 : ((fits00.drop 32).take 3).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00_end : (fits00.drop 35).all frame022test00=true := by
  decide +kernel

private theorem frame022scope00 : fits00.all frame022test00=true := by
  have h32 := stitchAt 32 3 frame022scope00_s032 frame022scope00_end
  have h28 := stitchAt 28 4 frame022scope00_s028 h32
  have h24 := stitchAt 24 4 frame022scope00_s024 h28
  have h20 := stitchAt 20 4 frame022scope00_s020 h24
  have h16 := stitchAt 16 4 frame022scope00_s016 h20
  have h12 := stitchAt 12 4 frame022scope00_s012 h16
  have h8 := stitchAt 8 4 frame022scope00_s008 h12
  have h4 := stitchAt 4 4 frame022scope00_s004 h8
  have h0 := stitchAt 0 4 frame022scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch00 : batch00.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope00

private abbrev frame022test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch01.stop,F)

private theorem frame022scope01_s000 : ((fits01.drop 0).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s004 : ((fits01.drop 4).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s008 : ((fits01.drop 8).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s012 : ((fits01.drop 12).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s016 : ((fits01.drop 16).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s020 : ((fits01.drop 20).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s024 : ((fits01.drop 24).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s028 : ((fits01.drop 28).take 4).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_s032 : ((fits01.drop 32).take 3).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01_end : (fits01.drop 35).all frame022test01=true := by
  decide +kernel

private theorem frame022scope01 : fits01.all frame022test01=true := by
  have h32 := stitchAt 32 3 frame022scope01_s032 frame022scope01_end
  have h28 := stitchAt 28 4 frame022scope01_s028 h32
  have h24 := stitchAt 24 4 frame022scope01_s024 h28
  have h20 := stitchAt 20 4 frame022scope01_s020 h24
  have h16 := stitchAt 16 4 frame022scope01_s016 h20
  have h12 := stitchAt 12 4 frame022scope01_s012 h16
  have h8 := stitchAt 8 4 frame022scope01_s008 h12
  have h4 := stitchAt 4 4 frame022scope01_s004 h8
  have h0 := stitchAt 0 4 frame022scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch01 : batch01.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope01

private abbrev frame022test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch02.stop,F)

private theorem frame022scope02_s000 : ((fits02.drop 0).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s004 : ((fits02.drop 4).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s008 : ((fits02.drop 8).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s012 : ((fits02.drop 12).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s016 : ((fits02.drop 16).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s020 : ((fits02.drop 20).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s024 : ((fits02.drop 24).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s028 : ((fits02.drop 28).take 4).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_s032 : ((fits02.drop 32).take 3).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02_end : (fits02.drop 35).all frame022test02=true := by
  decide +kernel

private theorem frame022scope02 : fits02.all frame022test02=true := by
  have h32 := stitchAt 32 3 frame022scope02_s032 frame022scope02_end
  have h28 := stitchAt 28 4 frame022scope02_s028 h32
  have h24 := stitchAt 24 4 frame022scope02_s024 h28
  have h20 := stitchAt 20 4 frame022scope02_s020 h24
  have h16 := stitchAt 16 4 frame022scope02_s016 h20
  have h12 := stitchAt 12 4 frame022scope02_s012 h16
  have h8 := stitchAt 8 4 frame022scope02_s008 h12
  have h4 := stitchAt 4 4 frame022scope02_s004 h8
  have h0 := stitchAt 0 4 frame022scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch02 : batch02.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope02

private abbrev frame022test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch03.stop,F)

private theorem frame022scope03_s000 : ((fits03.drop 0).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s004 : ((fits03.drop 4).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s008 : ((fits03.drop 8).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s012 : ((fits03.drop 12).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s016 : ((fits03.drop 16).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s020 : ((fits03.drop 20).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s024 : ((fits03.drop 24).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s028 : ((fits03.drop 28).take 4).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_s032 : ((fits03.drop 32).take 3).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03_end : (fits03.drop 35).all frame022test03=true := by
  decide +kernel

private theorem frame022scope03 : fits03.all frame022test03=true := by
  have h32 := stitchAt 32 3 frame022scope03_s032 frame022scope03_end
  have h28 := stitchAt 28 4 frame022scope03_s028 h32
  have h24 := stitchAt 24 4 frame022scope03_s024 h28
  have h20 := stitchAt 20 4 frame022scope03_s020 h24
  have h16 := stitchAt 16 4 frame022scope03_s016 h20
  have h12 := stitchAt 12 4 frame022scope03_s012 h16
  have h8 := stitchAt 8 4 frame022scope03_s008 h12
  have h4 := stitchAt 4 4 frame022scope03_s004 h8
  have h0 := stitchAt 0 4 frame022scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch03 : batch03.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope03

private abbrev frame022test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch04.stop,F)

private theorem frame022scope04_s000 : ((fits04.drop 0).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s004 : ((fits04.drop 4).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s008 : ((fits04.drop 8).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s012 : ((fits04.drop 12).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s016 : ((fits04.drop 16).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s020 : ((fits04.drop 20).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s024 : ((fits04.drop 24).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s028 : ((fits04.drop 28).take 4).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_s032 : ((fits04.drop 32).take 3).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04_end : (fits04.drop 35).all frame022test04=true := by
  decide +kernel

private theorem frame022scope04 : fits04.all frame022test04=true := by
  have h32 := stitchAt 32 3 frame022scope04_s032 frame022scope04_end
  have h28 := stitchAt 28 4 frame022scope04_s028 h32
  have h24 := stitchAt 24 4 frame022scope04_s024 h28
  have h20 := stitchAt 20 4 frame022scope04_s020 h24
  have h16 := stitchAt 16 4 frame022scope04_s016 h20
  have h12 := stitchAt 12 4 frame022scope04_s012 h16
  have h8 := stitchAt 8 4 frame022scope04_s008 h12
  have h4 := stitchAt 4 4 frame022scope04_s004 h8
  have h0 := stitchAt 0 4 frame022scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch04 : batch04.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope04

private abbrev frame022test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch05.stop,F)

private theorem frame022scope05_s000 : ((fits05.drop 0).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s004 : ((fits05.drop 4).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s008 : ((fits05.drop 8).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s012 : ((fits05.drop 12).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s016 : ((fits05.drop 16).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s020 : ((fits05.drop 20).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s024 : ((fits05.drop 24).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s028 : ((fits05.drop 28).take 4).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_s032 : ((fits05.drop 32).take 3).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05_end : (fits05.drop 35).all frame022test05=true := by
  decide +kernel

private theorem frame022scope05 : fits05.all frame022test05=true := by
  have h32 := stitchAt 32 3 frame022scope05_s032 frame022scope05_end
  have h28 := stitchAt 28 4 frame022scope05_s028 h32
  have h24 := stitchAt 24 4 frame022scope05_s024 h28
  have h20 := stitchAt 20 4 frame022scope05_s020 h24
  have h16 := stitchAt 16 4 frame022scope05_s016 h20
  have h12 := stitchAt 12 4 frame022scope05_s012 h16
  have h8 := stitchAt 8 4 frame022scope05_s008 h12
  have h4 := stitchAt 4 4 frame022scope05_s004 h8
  have h0 := stitchAt 0 4 frame022scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch05 : batch05.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope05

private abbrev frame022test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch06.stop,F)

private theorem frame022scope06_s000 : ((fits06.drop 0).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s004 : ((fits06.drop 4).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s008 : ((fits06.drop 8).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s012 : ((fits06.drop 12).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s016 : ((fits06.drop 16).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s020 : ((fits06.drop 20).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s024 : ((fits06.drop 24).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s028 : ((fits06.drop 28).take 4).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_s032 : ((fits06.drop 32).take 3).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06_end : (fits06.drop 35).all frame022test06=true := by
  decide +kernel

private theorem frame022scope06 : fits06.all frame022test06=true := by
  have h32 := stitchAt 32 3 frame022scope06_s032 frame022scope06_end
  have h28 := stitchAt 28 4 frame022scope06_s028 h32
  have h24 := stitchAt 24 4 frame022scope06_s024 h28
  have h20 := stitchAt 20 4 frame022scope06_s020 h24
  have h16 := stitchAt 16 4 frame022scope06_s016 h20
  have h12 := stitchAt 12 4 frame022scope06_s012 h16
  have h8 := stitchAt 8 4 frame022scope06_s008 h12
  have h4 := stitchAt 4 4 frame022scope06_s004 h8
  have h0 := stitchAt 0 4 frame022scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch06 : batch06.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope06

private abbrev frame022test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame48 (fun z => List.lookup (guideCode z) guide022)
    (batch07.stop,F)

private theorem frame022scope07_s000 : ((fits07.drop 0).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s004 : ((fits07.drop 4).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s008 : ((fits07.drop 8).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s012 : ((fits07.drop 12).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s016 : ((fits07.drop 16).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s020 : ((fits07.drop 20).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s024 : ((fits07.drop 24).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s028 : ((fits07.drop 28).take 4).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_s032 : ((fits07.drop 32).take 3).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07_end : (fits07.drop 35).all frame022test07=true := by
  decide +kernel

private theorem frame022scope07 : fits07.all frame022test07=true := by
  have h32 := stitchAt 32 3 frame022scope07_s032 frame022scope07_end
  have h28 := stitchAt 28 4 frame022scope07_s028 h32
  have h24 := stitchAt 24 4 frame022scope07_s024 h28
  have h20 := stitchAt 20 4 frame022scope07_s020 h24
  have h16 := stitchAt 16 4 frame022scope07_s016 h20
  have h12 := stitchAt 12 4 frame022scope07_s012 h16
  have h8 := stitchAt 8 4 frame022scope07_s008 h12
  have h4 := stitchAt 4 4 frame022scope07_s004 h8
  have h0 := stitchAt 0 4 frame022scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame022batch07 : batch07.pickTest original frame48=true :=
  FitBatch.pickTest_of_scoped scoped022 frame022scope07

private theorem frameBatches022 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame48)=true := by
  simp only [List.all_cons,List.all_nil,frame022batch00,frame022batch01,frame022batch02,frame022batch03,frame022batch04,frame022batch05,frame022batch06,frame022batch07,Bool.and_self]

theorem frameOK022 : frameRankTest original useStop frame48=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches022

theorem stripOK023 : stripTest frame49=true := by decide +kernel

theorem spanOK023 : checkChain 1600 1584 [frame49.span]=true := by decide +kernel

private theorem guideAt023 : List.lookup frame49.span.1 guideTable=some guide023 := by
  decide +kernel

private theorem scoped023 : original.guide frame49.span.1 =
    (fun z => List.lookup (guideCode z) guide023) := by
  funext z
  change (List.lookup frame49.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide023
  simp only [guideAt023,Option.bind_some]

private abbrev frame023test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch00.stop,F)

private theorem frame023scope00_s000 : ((fits00.drop 0).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s004 : ((fits00.drop 4).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s008 : ((fits00.drop 8).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s012 : ((fits00.drop 12).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s016 : ((fits00.drop 16).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s020 : ((fits00.drop 20).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s024 : ((fits00.drop 24).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s028 : ((fits00.drop 28).take 4).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_s032 : ((fits00.drop 32).take 3).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00_end : (fits00.drop 35).all frame023test00=true := by
  decide +kernel

private theorem frame023scope00 : fits00.all frame023test00=true := by
  have h32 := stitchAt 32 3 frame023scope00_s032 frame023scope00_end
  have h28 := stitchAt 28 4 frame023scope00_s028 h32
  have h24 := stitchAt 24 4 frame023scope00_s024 h28
  have h20 := stitchAt 20 4 frame023scope00_s020 h24
  have h16 := stitchAt 16 4 frame023scope00_s016 h20
  have h12 := stitchAt 12 4 frame023scope00_s012 h16
  have h8 := stitchAt 8 4 frame023scope00_s008 h12
  have h4 := stitchAt 4 4 frame023scope00_s004 h8
  have h0 := stitchAt 0 4 frame023scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch00 : batch00.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope00

private abbrev frame023test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch01.stop,F)

private theorem frame023scope01_s000 : ((fits01.drop 0).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s004 : ((fits01.drop 4).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s008 : ((fits01.drop 8).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s012 : ((fits01.drop 12).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s016 : ((fits01.drop 16).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s020 : ((fits01.drop 20).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s024 : ((fits01.drop 24).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s028 : ((fits01.drop 28).take 4).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_s032 : ((fits01.drop 32).take 3).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01_end : (fits01.drop 35).all frame023test01=true := by
  decide +kernel

private theorem frame023scope01 : fits01.all frame023test01=true := by
  have h32 := stitchAt 32 3 frame023scope01_s032 frame023scope01_end
  have h28 := stitchAt 28 4 frame023scope01_s028 h32
  have h24 := stitchAt 24 4 frame023scope01_s024 h28
  have h20 := stitchAt 20 4 frame023scope01_s020 h24
  have h16 := stitchAt 16 4 frame023scope01_s016 h20
  have h12 := stitchAt 12 4 frame023scope01_s012 h16
  have h8 := stitchAt 8 4 frame023scope01_s008 h12
  have h4 := stitchAt 4 4 frame023scope01_s004 h8
  have h0 := stitchAt 0 4 frame023scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch01 : batch01.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope01

private abbrev frame023test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch02.stop,F)

private theorem frame023scope02_s000 : ((fits02.drop 0).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s004 : ((fits02.drop 4).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s008 : ((fits02.drop 8).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s012 : ((fits02.drop 12).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s016 : ((fits02.drop 16).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s020 : ((fits02.drop 20).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s024 : ((fits02.drop 24).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s028 : ((fits02.drop 28).take 4).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_s032 : ((fits02.drop 32).take 3).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02_end : (fits02.drop 35).all frame023test02=true := by
  decide +kernel

private theorem frame023scope02 : fits02.all frame023test02=true := by
  have h32 := stitchAt 32 3 frame023scope02_s032 frame023scope02_end
  have h28 := stitchAt 28 4 frame023scope02_s028 h32
  have h24 := stitchAt 24 4 frame023scope02_s024 h28
  have h20 := stitchAt 20 4 frame023scope02_s020 h24
  have h16 := stitchAt 16 4 frame023scope02_s016 h20
  have h12 := stitchAt 12 4 frame023scope02_s012 h16
  have h8 := stitchAt 8 4 frame023scope02_s008 h12
  have h4 := stitchAt 4 4 frame023scope02_s004 h8
  have h0 := stitchAt 0 4 frame023scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch02 : batch02.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope02

private abbrev frame023test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch03.stop,F)

private theorem frame023scope03_s000 : ((fits03.drop 0).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s004 : ((fits03.drop 4).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s008 : ((fits03.drop 8).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s012 : ((fits03.drop 12).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s016 : ((fits03.drop 16).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s020 : ((fits03.drop 20).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s024 : ((fits03.drop 24).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s028 : ((fits03.drop 28).take 4).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_s032 : ((fits03.drop 32).take 3).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03_end : (fits03.drop 35).all frame023test03=true := by
  decide +kernel

private theorem frame023scope03 : fits03.all frame023test03=true := by
  have h32 := stitchAt 32 3 frame023scope03_s032 frame023scope03_end
  have h28 := stitchAt 28 4 frame023scope03_s028 h32
  have h24 := stitchAt 24 4 frame023scope03_s024 h28
  have h20 := stitchAt 20 4 frame023scope03_s020 h24
  have h16 := stitchAt 16 4 frame023scope03_s016 h20
  have h12 := stitchAt 12 4 frame023scope03_s012 h16
  have h8 := stitchAt 8 4 frame023scope03_s008 h12
  have h4 := stitchAt 4 4 frame023scope03_s004 h8
  have h0 := stitchAt 0 4 frame023scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch03 : batch03.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope03

private abbrev frame023test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch04.stop,F)

private theorem frame023scope04_s000 : ((fits04.drop 0).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s004 : ((fits04.drop 4).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s008 : ((fits04.drop 8).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s012 : ((fits04.drop 12).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s016 : ((fits04.drop 16).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s020 : ((fits04.drop 20).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s024 : ((fits04.drop 24).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s028 : ((fits04.drop 28).take 4).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_s032 : ((fits04.drop 32).take 3).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04_end : (fits04.drop 35).all frame023test04=true := by
  decide +kernel

private theorem frame023scope04 : fits04.all frame023test04=true := by
  have h32 := stitchAt 32 3 frame023scope04_s032 frame023scope04_end
  have h28 := stitchAt 28 4 frame023scope04_s028 h32
  have h24 := stitchAt 24 4 frame023scope04_s024 h28
  have h20 := stitchAt 20 4 frame023scope04_s020 h24
  have h16 := stitchAt 16 4 frame023scope04_s016 h20
  have h12 := stitchAt 12 4 frame023scope04_s012 h16
  have h8 := stitchAt 8 4 frame023scope04_s008 h12
  have h4 := stitchAt 4 4 frame023scope04_s004 h8
  have h0 := stitchAt 0 4 frame023scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch04 : batch04.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope04

private abbrev frame023test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch05.stop,F)

private theorem frame023scope05_s000 : ((fits05.drop 0).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s004 : ((fits05.drop 4).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s008 : ((fits05.drop 8).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s012 : ((fits05.drop 12).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s016 : ((fits05.drop 16).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s020 : ((fits05.drop 20).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s024 : ((fits05.drop 24).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s028 : ((fits05.drop 28).take 4).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_s032 : ((fits05.drop 32).take 3).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05_end : (fits05.drop 35).all frame023test05=true := by
  decide +kernel

private theorem frame023scope05 : fits05.all frame023test05=true := by
  have h32 := stitchAt 32 3 frame023scope05_s032 frame023scope05_end
  have h28 := stitchAt 28 4 frame023scope05_s028 h32
  have h24 := stitchAt 24 4 frame023scope05_s024 h28
  have h20 := stitchAt 20 4 frame023scope05_s020 h24
  have h16 := stitchAt 16 4 frame023scope05_s016 h20
  have h12 := stitchAt 12 4 frame023scope05_s012 h16
  have h8 := stitchAt 8 4 frame023scope05_s008 h12
  have h4 := stitchAt 4 4 frame023scope05_s004 h8
  have h0 := stitchAt 0 4 frame023scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch05 : batch05.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope05

private abbrev frame023test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch06.stop,F)

private theorem frame023scope06_s000 : ((fits06.drop 0).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s004 : ((fits06.drop 4).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s008 : ((fits06.drop 8).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s012 : ((fits06.drop 12).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s016 : ((fits06.drop 16).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s020 : ((fits06.drop 20).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s024 : ((fits06.drop 24).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s028 : ((fits06.drop 28).take 4).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_s032 : ((fits06.drop 32).take 3).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06_end : (fits06.drop 35).all frame023test06=true := by
  decide +kernel

private theorem frame023scope06 : fits06.all frame023test06=true := by
  have h32 := stitchAt 32 3 frame023scope06_s032 frame023scope06_end
  have h28 := stitchAt 28 4 frame023scope06_s028 h32
  have h24 := stitchAt 24 4 frame023scope06_s024 h28
  have h20 := stitchAt 20 4 frame023scope06_s020 h24
  have h16 := stitchAt 16 4 frame023scope06_s016 h20
  have h12 := stitchAt 12 4 frame023scope06_s012 h16
  have h8 := stitchAt 8 4 frame023scope06_s008 h12
  have h4 := stitchAt 4 4 frame023scope06_s004 h8
  have h0 := stitchAt 0 4 frame023scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch06 : batch06.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope06

private abbrev frame023test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame49 (fun z => List.lookup (guideCode z) guide023)
    (batch07.stop,F)

private theorem frame023scope07_s000 : ((fits07.drop 0).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s004 : ((fits07.drop 4).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s008 : ((fits07.drop 8).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s012 : ((fits07.drop 12).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s016 : ((fits07.drop 16).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s020 : ((fits07.drop 20).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s024 : ((fits07.drop 24).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s028 : ((fits07.drop 28).take 4).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_s032 : ((fits07.drop 32).take 3).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07_end : (fits07.drop 35).all frame023test07=true := by
  decide +kernel

private theorem frame023scope07 : fits07.all frame023test07=true := by
  have h32 := stitchAt 32 3 frame023scope07_s032 frame023scope07_end
  have h28 := stitchAt 28 4 frame023scope07_s028 h32
  have h24 := stitchAt 24 4 frame023scope07_s024 h28
  have h20 := stitchAt 20 4 frame023scope07_s020 h24
  have h16 := stitchAt 16 4 frame023scope07_s016 h20
  have h12 := stitchAt 12 4 frame023scope07_s012 h16
  have h8 := stitchAt 8 4 frame023scope07_s008 h12
  have h4 := stitchAt 4 4 frame023scope07_s004 h8
  have h0 := stitchAt 0 4 frame023scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame023batch07 : batch07.pickTest original frame49=true :=
  FitBatch.pickTest_of_scoped scoped023 frame023scope07

private theorem frameBatches023 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame49)=true := by
  simp only [List.all_cons,List.all_nil,frame023batch00,frame023batch01,frame023batch02,frame023batch03,frame023batch04,frame023batch05,frame023batch06,frame023batch07,Bool.and_self]

theorem frameOK023 : frameRankTest original useStop frame49=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches023


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
