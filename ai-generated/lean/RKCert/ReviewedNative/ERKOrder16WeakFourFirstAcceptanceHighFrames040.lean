module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK080 : stripTest frame163=true := by decide +kernel

theorem spanOK080 : checkChain 1880 1872 [frame163.span]=true := by decide +kernel

private theorem guideAt080 : List.lookup frame163.span.1 guideTable=some guide080 := by
  decide +kernel

private theorem scoped080 : original.guide frame163.span.1 =
    (fun z => List.lookup (guideCode z) guide080) := by
  funext z
  change (List.lookup frame163.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide080
  simp only [guideAt080,Option.bind_some]

private abbrev frame080test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch00.stop,F)

private theorem frame080scope00_s000 : ((fits00.drop 0).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s004 : ((fits00.drop 4).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s008 : ((fits00.drop 8).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s012 : ((fits00.drop 12).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s016 : ((fits00.drop 16).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s020 : ((fits00.drop 20).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s024 : ((fits00.drop 24).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s028 : ((fits00.drop 28).take 4).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_s032 : ((fits00.drop 32).take 3).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00_end : (fits00.drop 35).all frame080test00=true := by
  decide +kernel

private theorem frame080scope00 : fits00.all frame080test00=true := by
  have h32 := stitchAt 32 3 frame080scope00_s032 frame080scope00_end
  have h28 := stitchAt 28 4 frame080scope00_s028 h32
  have h24 := stitchAt 24 4 frame080scope00_s024 h28
  have h20 := stitchAt 20 4 frame080scope00_s020 h24
  have h16 := stitchAt 16 4 frame080scope00_s016 h20
  have h12 := stitchAt 12 4 frame080scope00_s012 h16
  have h8 := stitchAt 8 4 frame080scope00_s008 h12
  have h4 := stitchAt 4 4 frame080scope00_s004 h8
  have h0 := stitchAt 0 4 frame080scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch00 : batch00.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope00

private abbrev frame080test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch01.stop,F)

private theorem frame080scope01_s000 : ((fits01.drop 0).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s004 : ((fits01.drop 4).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s008 : ((fits01.drop 8).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s012 : ((fits01.drop 12).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s016 : ((fits01.drop 16).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s020 : ((fits01.drop 20).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s024 : ((fits01.drop 24).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s028 : ((fits01.drop 28).take 4).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_s032 : ((fits01.drop 32).take 3).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01_end : (fits01.drop 35).all frame080test01=true := by
  decide +kernel

private theorem frame080scope01 : fits01.all frame080test01=true := by
  have h32 := stitchAt 32 3 frame080scope01_s032 frame080scope01_end
  have h28 := stitchAt 28 4 frame080scope01_s028 h32
  have h24 := stitchAt 24 4 frame080scope01_s024 h28
  have h20 := stitchAt 20 4 frame080scope01_s020 h24
  have h16 := stitchAt 16 4 frame080scope01_s016 h20
  have h12 := stitchAt 12 4 frame080scope01_s012 h16
  have h8 := stitchAt 8 4 frame080scope01_s008 h12
  have h4 := stitchAt 4 4 frame080scope01_s004 h8
  have h0 := stitchAt 0 4 frame080scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch01 : batch01.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope01

private abbrev frame080test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch02.stop,F)

private theorem frame080scope02_s000 : ((fits02.drop 0).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s004 : ((fits02.drop 4).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s008 : ((fits02.drop 8).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s012 : ((fits02.drop 12).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s016 : ((fits02.drop 16).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s020 : ((fits02.drop 20).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s024 : ((fits02.drop 24).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s028 : ((fits02.drop 28).take 4).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_s032 : ((fits02.drop 32).take 3).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02_end : (fits02.drop 35).all frame080test02=true := by
  decide +kernel

private theorem frame080scope02 : fits02.all frame080test02=true := by
  have h32 := stitchAt 32 3 frame080scope02_s032 frame080scope02_end
  have h28 := stitchAt 28 4 frame080scope02_s028 h32
  have h24 := stitchAt 24 4 frame080scope02_s024 h28
  have h20 := stitchAt 20 4 frame080scope02_s020 h24
  have h16 := stitchAt 16 4 frame080scope02_s016 h20
  have h12 := stitchAt 12 4 frame080scope02_s012 h16
  have h8 := stitchAt 8 4 frame080scope02_s008 h12
  have h4 := stitchAt 4 4 frame080scope02_s004 h8
  have h0 := stitchAt 0 4 frame080scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch02 : batch02.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope02

private abbrev frame080test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch03.stop,F)

private theorem frame080scope03_s000 : ((fits03.drop 0).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s004 : ((fits03.drop 4).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s008 : ((fits03.drop 8).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s012 : ((fits03.drop 12).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s016 : ((fits03.drop 16).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s020 : ((fits03.drop 20).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s024 : ((fits03.drop 24).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s028 : ((fits03.drop 28).take 4).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_s032 : ((fits03.drop 32).take 3).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03_end : (fits03.drop 35).all frame080test03=true := by
  decide +kernel

private theorem frame080scope03 : fits03.all frame080test03=true := by
  have h32 := stitchAt 32 3 frame080scope03_s032 frame080scope03_end
  have h28 := stitchAt 28 4 frame080scope03_s028 h32
  have h24 := stitchAt 24 4 frame080scope03_s024 h28
  have h20 := stitchAt 20 4 frame080scope03_s020 h24
  have h16 := stitchAt 16 4 frame080scope03_s016 h20
  have h12 := stitchAt 12 4 frame080scope03_s012 h16
  have h8 := stitchAt 8 4 frame080scope03_s008 h12
  have h4 := stitchAt 4 4 frame080scope03_s004 h8
  have h0 := stitchAt 0 4 frame080scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch03 : batch03.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope03

private abbrev frame080test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch04.stop,F)

private theorem frame080scope04_s000 : ((fits04.drop 0).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s004 : ((fits04.drop 4).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s008 : ((fits04.drop 8).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s012 : ((fits04.drop 12).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s016 : ((fits04.drop 16).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s020 : ((fits04.drop 20).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s024 : ((fits04.drop 24).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s028 : ((fits04.drop 28).take 4).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_s032 : ((fits04.drop 32).take 3).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04_end : (fits04.drop 35).all frame080test04=true := by
  decide +kernel

private theorem frame080scope04 : fits04.all frame080test04=true := by
  have h32 := stitchAt 32 3 frame080scope04_s032 frame080scope04_end
  have h28 := stitchAt 28 4 frame080scope04_s028 h32
  have h24 := stitchAt 24 4 frame080scope04_s024 h28
  have h20 := stitchAt 20 4 frame080scope04_s020 h24
  have h16 := stitchAt 16 4 frame080scope04_s016 h20
  have h12 := stitchAt 12 4 frame080scope04_s012 h16
  have h8 := stitchAt 8 4 frame080scope04_s008 h12
  have h4 := stitchAt 4 4 frame080scope04_s004 h8
  have h0 := stitchAt 0 4 frame080scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch04 : batch04.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope04

private abbrev frame080test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch05.stop,F)

private theorem frame080scope05_s000 : ((fits05.drop 0).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s004 : ((fits05.drop 4).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s008 : ((fits05.drop 8).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s012 : ((fits05.drop 12).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s016 : ((fits05.drop 16).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s020 : ((fits05.drop 20).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s024 : ((fits05.drop 24).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s028 : ((fits05.drop 28).take 4).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_s032 : ((fits05.drop 32).take 3).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05_end : (fits05.drop 35).all frame080test05=true := by
  decide +kernel

private theorem frame080scope05 : fits05.all frame080test05=true := by
  have h32 := stitchAt 32 3 frame080scope05_s032 frame080scope05_end
  have h28 := stitchAt 28 4 frame080scope05_s028 h32
  have h24 := stitchAt 24 4 frame080scope05_s024 h28
  have h20 := stitchAt 20 4 frame080scope05_s020 h24
  have h16 := stitchAt 16 4 frame080scope05_s016 h20
  have h12 := stitchAt 12 4 frame080scope05_s012 h16
  have h8 := stitchAt 8 4 frame080scope05_s008 h12
  have h4 := stitchAt 4 4 frame080scope05_s004 h8
  have h0 := stitchAt 0 4 frame080scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch05 : batch05.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope05

private abbrev frame080test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch06.stop,F)

private theorem frame080scope06_s000 : ((fits06.drop 0).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s004 : ((fits06.drop 4).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s008 : ((fits06.drop 8).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s012 : ((fits06.drop 12).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s016 : ((fits06.drop 16).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s020 : ((fits06.drop 20).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s024 : ((fits06.drop 24).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s028 : ((fits06.drop 28).take 4).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_s032 : ((fits06.drop 32).take 3).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06_end : (fits06.drop 35).all frame080test06=true := by
  decide +kernel

private theorem frame080scope06 : fits06.all frame080test06=true := by
  have h32 := stitchAt 32 3 frame080scope06_s032 frame080scope06_end
  have h28 := stitchAt 28 4 frame080scope06_s028 h32
  have h24 := stitchAt 24 4 frame080scope06_s024 h28
  have h20 := stitchAt 20 4 frame080scope06_s020 h24
  have h16 := stitchAt 16 4 frame080scope06_s016 h20
  have h12 := stitchAt 12 4 frame080scope06_s012 h16
  have h8 := stitchAt 8 4 frame080scope06_s008 h12
  have h4 := stitchAt 4 4 frame080scope06_s004 h8
  have h0 := stitchAt 0 4 frame080scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch06 : batch06.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope06

private abbrev frame080test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame163 (fun z => List.lookup (guideCode z) guide080)
    (batch07.stop,F)

private theorem frame080scope07_s000 : ((fits07.drop 0).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s004 : ((fits07.drop 4).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s008 : ((fits07.drop 8).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s012 : ((fits07.drop 12).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s016 : ((fits07.drop 16).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s020 : ((fits07.drop 20).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s024 : ((fits07.drop 24).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s028 : ((fits07.drop 28).take 4).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_s032 : ((fits07.drop 32).take 3).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07_end : (fits07.drop 35).all frame080test07=true := by
  decide +kernel

private theorem frame080scope07 : fits07.all frame080test07=true := by
  have h32 := stitchAt 32 3 frame080scope07_s032 frame080scope07_end
  have h28 := stitchAt 28 4 frame080scope07_s028 h32
  have h24 := stitchAt 24 4 frame080scope07_s024 h28
  have h20 := stitchAt 20 4 frame080scope07_s020 h24
  have h16 := stitchAt 16 4 frame080scope07_s016 h20
  have h12 := stitchAt 12 4 frame080scope07_s012 h16
  have h8 := stitchAt 8 4 frame080scope07_s008 h12
  have h4 := stitchAt 4 4 frame080scope07_s004 h8
  have h0 := stitchAt 0 4 frame080scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame080batch07 : batch07.pickTest original frame163=true :=
  FitBatch.pickTest_of_scoped scoped080 frame080scope07

private theorem frameBatches080 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame163)=true := by
  simp only [List.all_cons,List.all_nil,frame080batch00,frame080batch01,frame080batch02,frame080batch03,frame080batch04,frame080batch05,frame080batch06,frame080batch07,Bool.and_self]

theorem frameOK080 : frameRankTest original useStop frame163=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches080

theorem stripOK081 : stripTest frame164=true := by decide +kernel

theorem spanOK081 : checkChain 1888 1880 [frame164.span]=true := by decide +kernel

private theorem guideAt081 : List.lookup frame164.span.1 guideTable=some guide081 := by
  decide +kernel

private theorem scoped081 : original.guide frame164.span.1 =
    (fun z => List.lookup (guideCode z) guide081) := by
  funext z
  change (List.lookup frame164.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide081
  simp only [guideAt081,Option.bind_some]

private abbrev frame081test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch00.stop,F)

private theorem frame081scope00_s000 : ((fits00.drop 0).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s004 : ((fits00.drop 4).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s008 : ((fits00.drop 8).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s012 : ((fits00.drop 12).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s016 : ((fits00.drop 16).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s020 : ((fits00.drop 20).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s024 : ((fits00.drop 24).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s028 : ((fits00.drop 28).take 4).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_s032 : ((fits00.drop 32).take 3).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00_end : (fits00.drop 35).all frame081test00=true := by
  decide +kernel

private theorem frame081scope00 : fits00.all frame081test00=true := by
  have h32 := stitchAt 32 3 frame081scope00_s032 frame081scope00_end
  have h28 := stitchAt 28 4 frame081scope00_s028 h32
  have h24 := stitchAt 24 4 frame081scope00_s024 h28
  have h20 := stitchAt 20 4 frame081scope00_s020 h24
  have h16 := stitchAt 16 4 frame081scope00_s016 h20
  have h12 := stitchAt 12 4 frame081scope00_s012 h16
  have h8 := stitchAt 8 4 frame081scope00_s008 h12
  have h4 := stitchAt 4 4 frame081scope00_s004 h8
  have h0 := stitchAt 0 4 frame081scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch00 : batch00.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope00

private abbrev frame081test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch01.stop,F)

private theorem frame081scope01_s000 : ((fits01.drop 0).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s004 : ((fits01.drop 4).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s008 : ((fits01.drop 8).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s012 : ((fits01.drop 12).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s016 : ((fits01.drop 16).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s020 : ((fits01.drop 20).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s024 : ((fits01.drop 24).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s028 : ((fits01.drop 28).take 4).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_s032 : ((fits01.drop 32).take 3).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01_end : (fits01.drop 35).all frame081test01=true := by
  decide +kernel

private theorem frame081scope01 : fits01.all frame081test01=true := by
  have h32 := stitchAt 32 3 frame081scope01_s032 frame081scope01_end
  have h28 := stitchAt 28 4 frame081scope01_s028 h32
  have h24 := stitchAt 24 4 frame081scope01_s024 h28
  have h20 := stitchAt 20 4 frame081scope01_s020 h24
  have h16 := stitchAt 16 4 frame081scope01_s016 h20
  have h12 := stitchAt 12 4 frame081scope01_s012 h16
  have h8 := stitchAt 8 4 frame081scope01_s008 h12
  have h4 := stitchAt 4 4 frame081scope01_s004 h8
  have h0 := stitchAt 0 4 frame081scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch01 : batch01.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope01

private abbrev frame081test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch02.stop,F)

private theorem frame081scope02_s000 : ((fits02.drop 0).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s004 : ((fits02.drop 4).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s008 : ((fits02.drop 8).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s012 : ((fits02.drop 12).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s016 : ((fits02.drop 16).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s020 : ((fits02.drop 20).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s024 : ((fits02.drop 24).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s028 : ((fits02.drop 28).take 4).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_s032 : ((fits02.drop 32).take 3).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02_end : (fits02.drop 35).all frame081test02=true := by
  decide +kernel

private theorem frame081scope02 : fits02.all frame081test02=true := by
  have h32 := stitchAt 32 3 frame081scope02_s032 frame081scope02_end
  have h28 := stitchAt 28 4 frame081scope02_s028 h32
  have h24 := stitchAt 24 4 frame081scope02_s024 h28
  have h20 := stitchAt 20 4 frame081scope02_s020 h24
  have h16 := stitchAt 16 4 frame081scope02_s016 h20
  have h12 := stitchAt 12 4 frame081scope02_s012 h16
  have h8 := stitchAt 8 4 frame081scope02_s008 h12
  have h4 := stitchAt 4 4 frame081scope02_s004 h8
  have h0 := stitchAt 0 4 frame081scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch02 : batch02.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope02

private abbrev frame081test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch03.stop,F)

private theorem frame081scope03_s000 : ((fits03.drop 0).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s004 : ((fits03.drop 4).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s008 : ((fits03.drop 8).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s012 : ((fits03.drop 12).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s016 : ((fits03.drop 16).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s020 : ((fits03.drop 20).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s024 : ((fits03.drop 24).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s028 : ((fits03.drop 28).take 4).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_s032 : ((fits03.drop 32).take 3).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03_end : (fits03.drop 35).all frame081test03=true := by
  decide +kernel

private theorem frame081scope03 : fits03.all frame081test03=true := by
  have h32 := stitchAt 32 3 frame081scope03_s032 frame081scope03_end
  have h28 := stitchAt 28 4 frame081scope03_s028 h32
  have h24 := stitchAt 24 4 frame081scope03_s024 h28
  have h20 := stitchAt 20 4 frame081scope03_s020 h24
  have h16 := stitchAt 16 4 frame081scope03_s016 h20
  have h12 := stitchAt 12 4 frame081scope03_s012 h16
  have h8 := stitchAt 8 4 frame081scope03_s008 h12
  have h4 := stitchAt 4 4 frame081scope03_s004 h8
  have h0 := stitchAt 0 4 frame081scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch03 : batch03.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope03

private abbrev frame081test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch04.stop,F)

private theorem frame081scope04_s000 : ((fits04.drop 0).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s004 : ((fits04.drop 4).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s008 : ((fits04.drop 8).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s012 : ((fits04.drop 12).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s016 : ((fits04.drop 16).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s020 : ((fits04.drop 20).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s024 : ((fits04.drop 24).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s028 : ((fits04.drop 28).take 4).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_s032 : ((fits04.drop 32).take 3).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04_end : (fits04.drop 35).all frame081test04=true := by
  decide +kernel

private theorem frame081scope04 : fits04.all frame081test04=true := by
  have h32 := stitchAt 32 3 frame081scope04_s032 frame081scope04_end
  have h28 := stitchAt 28 4 frame081scope04_s028 h32
  have h24 := stitchAt 24 4 frame081scope04_s024 h28
  have h20 := stitchAt 20 4 frame081scope04_s020 h24
  have h16 := stitchAt 16 4 frame081scope04_s016 h20
  have h12 := stitchAt 12 4 frame081scope04_s012 h16
  have h8 := stitchAt 8 4 frame081scope04_s008 h12
  have h4 := stitchAt 4 4 frame081scope04_s004 h8
  have h0 := stitchAt 0 4 frame081scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch04 : batch04.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope04

private abbrev frame081test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch05.stop,F)

private theorem frame081scope05_s000 : ((fits05.drop 0).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s004 : ((fits05.drop 4).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s008 : ((fits05.drop 8).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s012 : ((fits05.drop 12).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s016 : ((fits05.drop 16).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s020 : ((fits05.drop 20).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s024 : ((fits05.drop 24).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s028 : ((fits05.drop 28).take 4).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_s032 : ((fits05.drop 32).take 3).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05_end : (fits05.drop 35).all frame081test05=true := by
  decide +kernel

private theorem frame081scope05 : fits05.all frame081test05=true := by
  have h32 := stitchAt 32 3 frame081scope05_s032 frame081scope05_end
  have h28 := stitchAt 28 4 frame081scope05_s028 h32
  have h24 := stitchAt 24 4 frame081scope05_s024 h28
  have h20 := stitchAt 20 4 frame081scope05_s020 h24
  have h16 := stitchAt 16 4 frame081scope05_s016 h20
  have h12 := stitchAt 12 4 frame081scope05_s012 h16
  have h8 := stitchAt 8 4 frame081scope05_s008 h12
  have h4 := stitchAt 4 4 frame081scope05_s004 h8
  have h0 := stitchAt 0 4 frame081scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch05 : batch05.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope05

private abbrev frame081test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch06.stop,F)

private theorem frame081scope06_s000 : ((fits06.drop 0).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s004 : ((fits06.drop 4).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s008 : ((fits06.drop 8).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s012 : ((fits06.drop 12).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s016 : ((fits06.drop 16).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s020 : ((fits06.drop 20).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s024 : ((fits06.drop 24).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s028 : ((fits06.drop 28).take 4).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_s032 : ((fits06.drop 32).take 3).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06_end : (fits06.drop 35).all frame081test06=true := by
  decide +kernel

private theorem frame081scope06 : fits06.all frame081test06=true := by
  have h32 := stitchAt 32 3 frame081scope06_s032 frame081scope06_end
  have h28 := stitchAt 28 4 frame081scope06_s028 h32
  have h24 := stitchAt 24 4 frame081scope06_s024 h28
  have h20 := stitchAt 20 4 frame081scope06_s020 h24
  have h16 := stitchAt 16 4 frame081scope06_s016 h20
  have h12 := stitchAt 12 4 frame081scope06_s012 h16
  have h8 := stitchAt 8 4 frame081scope06_s008 h12
  have h4 := stitchAt 4 4 frame081scope06_s004 h8
  have h0 := stitchAt 0 4 frame081scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch06 : batch06.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope06

private abbrev frame081test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame164 (fun z => List.lookup (guideCode z) guide081)
    (batch07.stop,F)

private theorem frame081scope07_s000 : ((fits07.drop 0).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s004 : ((fits07.drop 4).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s008 : ((fits07.drop 8).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s012 : ((fits07.drop 12).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s016 : ((fits07.drop 16).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s020 : ((fits07.drop 20).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s024 : ((fits07.drop 24).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s028 : ((fits07.drop 28).take 4).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_s032 : ((fits07.drop 32).take 3).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07_end : (fits07.drop 35).all frame081test07=true := by
  decide +kernel

private theorem frame081scope07 : fits07.all frame081test07=true := by
  have h32 := stitchAt 32 3 frame081scope07_s032 frame081scope07_end
  have h28 := stitchAt 28 4 frame081scope07_s028 h32
  have h24 := stitchAt 24 4 frame081scope07_s024 h28
  have h20 := stitchAt 20 4 frame081scope07_s020 h24
  have h16 := stitchAt 16 4 frame081scope07_s016 h20
  have h12 := stitchAt 12 4 frame081scope07_s012 h16
  have h8 := stitchAt 8 4 frame081scope07_s008 h12
  have h4 := stitchAt 4 4 frame081scope07_s004 h8
  have h0 := stitchAt 0 4 frame081scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame081batch07 : batch07.pickTest original frame164=true :=
  FitBatch.pickTest_of_scoped scoped081 frame081scope07

private theorem frameBatches081 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame164)=true := by
  simp only [List.all_cons,List.all_nil,frame081batch00,frame081batch01,frame081batch02,frame081batch03,frame081batch04,frame081batch05,frame081batch06,frame081batch07,Bool.and_self]

theorem frameOK081 : frameRankTest original useStop frame164=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches081


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
