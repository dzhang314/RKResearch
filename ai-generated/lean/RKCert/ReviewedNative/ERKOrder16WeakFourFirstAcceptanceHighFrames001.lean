module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK002 : stripTest frame7=true := by decide +kernel

theorem spanOK002 : checkChain 640 512 [frame7.span]=true := by decide +kernel

private theorem guideAt002 : List.lookup frame7.span.1 guideTable=some guide002 := by
  decide +kernel

private theorem scoped002 : original.guide frame7.span.1 =
    (fun z => List.lookup (guideCode z) guide002) := by
  funext z
  change (List.lookup frame7.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide002
  simp only [guideAt002,Option.bind_some]

private abbrev frame002test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch00.stop,F)

private theorem frame002scope00_s000 : ((fits00.drop 0).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s004 : ((fits00.drop 4).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s008 : ((fits00.drop 8).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s012 : ((fits00.drop 12).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s016 : ((fits00.drop 16).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s020 : ((fits00.drop 20).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s024 : ((fits00.drop 24).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s028 : ((fits00.drop 28).take 4).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_s032 : ((fits00.drop 32).take 3).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00_end : (fits00.drop 35).all frame002test00=true := by
  decide +kernel

private theorem frame002scope00 : fits00.all frame002test00=true := by
  have h32 := stitchAt 32 3 frame002scope00_s032 frame002scope00_end
  have h28 := stitchAt 28 4 frame002scope00_s028 h32
  have h24 := stitchAt 24 4 frame002scope00_s024 h28
  have h20 := stitchAt 20 4 frame002scope00_s020 h24
  have h16 := stitchAt 16 4 frame002scope00_s016 h20
  have h12 := stitchAt 12 4 frame002scope00_s012 h16
  have h8 := stitchAt 8 4 frame002scope00_s008 h12
  have h4 := stitchAt 4 4 frame002scope00_s004 h8
  have h0 := stitchAt 0 4 frame002scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch00 : batch00.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope00

private abbrev frame002test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch01.stop,F)

private theorem frame002scope01_s000 : ((fits01.drop 0).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s004 : ((fits01.drop 4).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s008 : ((fits01.drop 8).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s012 : ((fits01.drop 12).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s016 : ((fits01.drop 16).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s020 : ((fits01.drop 20).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s024 : ((fits01.drop 24).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s028 : ((fits01.drop 28).take 4).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_s032 : ((fits01.drop 32).take 3).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01_end : (fits01.drop 35).all frame002test01=true := by
  decide +kernel

private theorem frame002scope01 : fits01.all frame002test01=true := by
  have h32 := stitchAt 32 3 frame002scope01_s032 frame002scope01_end
  have h28 := stitchAt 28 4 frame002scope01_s028 h32
  have h24 := stitchAt 24 4 frame002scope01_s024 h28
  have h20 := stitchAt 20 4 frame002scope01_s020 h24
  have h16 := stitchAt 16 4 frame002scope01_s016 h20
  have h12 := stitchAt 12 4 frame002scope01_s012 h16
  have h8 := stitchAt 8 4 frame002scope01_s008 h12
  have h4 := stitchAt 4 4 frame002scope01_s004 h8
  have h0 := stitchAt 0 4 frame002scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch01 : batch01.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope01

private abbrev frame002test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch02.stop,F)

private theorem frame002scope02_s000 : ((fits02.drop 0).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s004 : ((fits02.drop 4).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s008 : ((fits02.drop 8).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s012 : ((fits02.drop 12).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s016 : ((fits02.drop 16).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s020 : ((fits02.drop 20).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s024 : ((fits02.drop 24).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s028 : ((fits02.drop 28).take 4).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_s032 : ((fits02.drop 32).take 3).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02_end : (fits02.drop 35).all frame002test02=true := by
  decide +kernel

private theorem frame002scope02 : fits02.all frame002test02=true := by
  have h32 := stitchAt 32 3 frame002scope02_s032 frame002scope02_end
  have h28 := stitchAt 28 4 frame002scope02_s028 h32
  have h24 := stitchAt 24 4 frame002scope02_s024 h28
  have h20 := stitchAt 20 4 frame002scope02_s020 h24
  have h16 := stitchAt 16 4 frame002scope02_s016 h20
  have h12 := stitchAt 12 4 frame002scope02_s012 h16
  have h8 := stitchAt 8 4 frame002scope02_s008 h12
  have h4 := stitchAt 4 4 frame002scope02_s004 h8
  have h0 := stitchAt 0 4 frame002scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch02 : batch02.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope02

private abbrev frame002test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch03.stop,F)

private theorem frame002scope03_s000 : ((fits03.drop 0).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s004 : ((fits03.drop 4).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s008 : ((fits03.drop 8).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s012 : ((fits03.drop 12).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s016 : ((fits03.drop 16).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s020 : ((fits03.drop 20).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s024 : ((fits03.drop 24).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s028 : ((fits03.drop 28).take 4).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_s032 : ((fits03.drop 32).take 3).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03_end : (fits03.drop 35).all frame002test03=true := by
  decide +kernel

private theorem frame002scope03 : fits03.all frame002test03=true := by
  have h32 := stitchAt 32 3 frame002scope03_s032 frame002scope03_end
  have h28 := stitchAt 28 4 frame002scope03_s028 h32
  have h24 := stitchAt 24 4 frame002scope03_s024 h28
  have h20 := stitchAt 20 4 frame002scope03_s020 h24
  have h16 := stitchAt 16 4 frame002scope03_s016 h20
  have h12 := stitchAt 12 4 frame002scope03_s012 h16
  have h8 := stitchAt 8 4 frame002scope03_s008 h12
  have h4 := stitchAt 4 4 frame002scope03_s004 h8
  have h0 := stitchAt 0 4 frame002scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch03 : batch03.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope03

private abbrev frame002test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch04.stop,F)

private theorem frame002scope04_s000 : ((fits04.drop 0).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s004 : ((fits04.drop 4).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s008 : ((fits04.drop 8).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s012 : ((fits04.drop 12).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s016 : ((fits04.drop 16).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s020 : ((fits04.drop 20).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s024 : ((fits04.drop 24).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s028 : ((fits04.drop 28).take 4).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_s032 : ((fits04.drop 32).take 3).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04_end : (fits04.drop 35).all frame002test04=true := by
  decide +kernel

private theorem frame002scope04 : fits04.all frame002test04=true := by
  have h32 := stitchAt 32 3 frame002scope04_s032 frame002scope04_end
  have h28 := stitchAt 28 4 frame002scope04_s028 h32
  have h24 := stitchAt 24 4 frame002scope04_s024 h28
  have h20 := stitchAt 20 4 frame002scope04_s020 h24
  have h16 := stitchAt 16 4 frame002scope04_s016 h20
  have h12 := stitchAt 12 4 frame002scope04_s012 h16
  have h8 := stitchAt 8 4 frame002scope04_s008 h12
  have h4 := stitchAt 4 4 frame002scope04_s004 h8
  have h0 := stitchAt 0 4 frame002scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch04 : batch04.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope04

private abbrev frame002test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch05.stop,F)

private theorem frame002scope05_s000 : ((fits05.drop 0).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s004 : ((fits05.drop 4).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s008 : ((fits05.drop 8).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s012 : ((fits05.drop 12).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s016 : ((fits05.drop 16).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s020 : ((fits05.drop 20).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s024 : ((fits05.drop 24).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s028 : ((fits05.drop 28).take 4).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_s032 : ((fits05.drop 32).take 3).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05_end : (fits05.drop 35).all frame002test05=true := by
  decide +kernel

private theorem frame002scope05 : fits05.all frame002test05=true := by
  have h32 := stitchAt 32 3 frame002scope05_s032 frame002scope05_end
  have h28 := stitchAt 28 4 frame002scope05_s028 h32
  have h24 := stitchAt 24 4 frame002scope05_s024 h28
  have h20 := stitchAt 20 4 frame002scope05_s020 h24
  have h16 := stitchAt 16 4 frame002scope05_s016 h20
  have h12 := stitchAt 12 4 frame002scope05_s012 h16
  have h8 := stitchAt 8 4 frame002scope05_s008 h12
  have h4 := stitchAt 4 4 frame002scope05_s004 h8
  have h0 := stitchAt 0 4 frame002scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch05 : batch05.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope05

private abbrev frame002test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch06.stop,F)

private theorem frame002scope06_s000 : ((fits06.drop 0).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s004 : ((fits06.drop 4).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s008 : ((fits06.drop 8).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s012 : ((fits06.drop 12).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s016 : ((fits06.drop 16).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s020 : ((fits06.drop 20).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s024 : ((fits06.drop 24).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s028 : ((fits06.drop 28).take 4).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_s032 : ((fits06.drop 32).take 3).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06_end : (fits06.drop 35).all frame002test06=true := by
  decide +kernel

private theorem frame002scope06 : fits06.all frame002test06=true := by
  have h32 := stitchAt 32 3 frame002scope06_s032 frame002scope06_end
  have h28 := stitchAt 28 4 frame002scope06_s028 h32
  have h24 := stitchAt 24 4 frame002scope06_s024 h28
  have h20 := stitchAt 20 4 frame002scope06_s020 h24
  have h16 := stitchAt 16 4 frame002scope06_s016 h20
  have h12 := stitchAt 12 4 frame002scope06_s012 h16
  have h8 := stitchAt 8 4 frame002scope06_s008 h12
  have h4 := stitchAt 4 4 frame002scope06_s004 h8
  have h0 := stitchAt 0 4 frame002scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch06 : batch06.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope06

private abbrev frame002test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame7 (fun z => List.lookup (guideCode z) guide002)
    (batch07.stop,F)

private theorem frame002scope07_s000 : ((fits07.drop 0).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s004 : ((fits07.drop 4).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s008 : ((fits07.drop 8).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s012 : ((fits07.drop 12).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s016 : ((fits07.drop 16).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s020 : ((fits07.drop 20).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s024 : ((fits07.drop 24).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s028 : ((fits07.drop 28).take 4).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_s032 : ((fits07.drop 32).take 3).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07_end : (fits07.drop 35).all frame002test07=true := by
  decide +kernel

private theorem frame002scope07 : fits07.all frame002test07=true := by
  have h32 := stitchAt 32 3 frame002scope07_s032 frame002scope07_end
  have h28 := stitchAt 28 4 frame002scope07_s028 h32
  have h24 := stitchAt 24 4 frame002scope07_s024 h28
  have h20 := stitchAt 20 4 frame002scope07_s020 h24
  have h16 := stitchAt 16 4 frame002scope07_s016 h20
  have h12 := stitchAt 12 4 frame002scope07_s012 h16
  have h8 := stitchAt 8 4 frame002scope07_s008 h12
  have h4 := stitchAt 4 4 frame002scope07_s004 h8
  have h0 := stitchAt 0 4 frame002scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame002batch07 : batch07.pickTest original frame7=true :=
  FitBatch.pickTest_of_scoped scoped002 frame002scope07

private theorem frameBatches002 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame7)=true := by
  simp only [List.all_cons,List.all_nil,frame002batch00,frame002batch01,frame002batch02,frame002batch03,frame002batch04,frame002batch05,frame002batch06,frame002batch07,Bool.and_self]

theorem frameOK002 : frameRankTest original useStop frame7=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches002

theorem stripOK003 : stripTest frame8=true := by decide +kernel

theorem spanOK003 : checkChain 768 640 [frame8.span]=true := by decide +kernel

private theorem guideAt003 : List.lookup frame8.span.1 guideTable=some guide003 := by
  decide +kernel

private theorem scoped003 : original.guide frame8.span.1 =
    (fun z => List.lookup (guideCode z) guide003) := by
  funext z
  change (List.lookup frame8.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide003
  simp only [guideAt003,Option.bind_some]

private abbrev frame003test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch00.stop,F)

private theorem frame003scope00_s000 : ((fits00.drop 0).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s004 : ((fits00.drop 4).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s008 : ((fits00.drop 8).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s012 : ((fits00.drop 12).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s016 : ((fits00.drop 16).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s020 : ((fits00.drop 20).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s024 : ((fits00.drop 24).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s028 : ((fits00.drop 28).take 4).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_s032 : ((fits00.drop 32).take 3).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00_end : (fits00.drop 35).all frame003test00=true := by
  decide +kernel

private theorem frame003scope00 : fits00.all frame003test00=true := by
  have h32 := stitchAt 32 3 frame003scope00_s032 frame003scope00_end
  have h28 := stitchAt 28 4 frame003scope00_s028 h32
  have h24 := stitchAt 24 4 frame003scope00_s024 h28
  have h20 := stitchAt 20 4 frame003scope00_s020 h24
  have h16 := stitchAt 16 4 frame003scope00_s016 h20
  have h12 := stitchAt 12 4 frame003scope00_s012 h16
  have h8 := stitchAt 8 4 frame003scope00_s008 h12
  have h4 := stitchAt 4 4 frame003scope00_s004 h8
  have h0 := stitchAt 0 4 frame003scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch00 : batch00.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope00

private abbrev frame003test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch01.stop,F)

private theorem frame003scope01_s000 : ((fits01.drop 0).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s004 : ((fits01.drop 4).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s008 : ((fits01.drop 8).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s012 : ((fits01.drop 12).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s016 : ((fits01.drop 16).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s020 : ((fits01.drop 20).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s024 : ((fits01.drop 24).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s028 : ((fits01.drop 28).take 4).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_s032 : ((fits01.drop 32).take 3).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01_end : (fits01.drop 35).all frame003test01=true := by
  decide +kernel

private theorem frame003scope01 : fits01.all frame003test01=true := by
  have h32 := stitchAt 32 3 frame003scope01_s032 frame003scope01_end
  have h28 := stitchAt 28 4 frame003scope01_s028 h32
  have h24 := stitchAt 24 4 frame003scope01_s024 h28
  have h20 := stitchAt 20 4 frame003scope01_s020 h24
  have h16 := stitchAt 16 4 frame003scope01_s016 h20
  have h12 := stitchAt 12 4 frame003scope01_s012 h16
  have h8 := stitchAt 8 4 frame003scope01_s008 h12
  have h4 := stitchAt 4 4 frame003scope01_s004 h8
  have h0 := stitchAt 0 4 frame003scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch01 : batch01.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope01

private abbrev frame003test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch02.stop,F)

private theorem frame003scope02_s000 : ((fits02.drop 0).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s004 : ((fits02.drop 4).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s008 : ((fits02.drop 8).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s012 : ((fits02.drop 12).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s016 : ((fits02.drop 16).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s020 : ((fits02.drop 20).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s024 : ((fits02.drop 24).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s028 : ((fits02.drop 28).take 4).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_s032 : ((fits02.drop 32).take 3).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02_end : (fits02.drop 35).all frame003test02=true := by
  decide +kernel

private theorem frame003scope02 : fits02.all frame003test02=true := by
  have h32 := stitchAt 32 3 frame003scope02_s032 frame003scope02_end
  have h28 := stitchAt 28 4 frame003scope02_s028 h32
  have h24 := stitchAt 24 4 frame003scope02_s024 h28
  have h20 := stitchAt 20 4 frame003scope02_s020 h24
  have h16 := stitchAt 16 4 frame003scope02_s016 h20
  have h12 := stitchAt 12 4 frame003scope02_s012 h16
  have h8 := stitchAt 8 4 frame003scope02_s008 h12
  have h4 := stitchAt 4 4 frame003scope02_s004 h8
  have h0 := stitchAt 0 4 frame003scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch02 : batch02.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope02

private abbrev frame003test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch03.stop,F)

private theorem frame003scope03_s000 : ((fits03.drop 0).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s004 : ((fits03.drop 4).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s008 : ((fits03.drop 8).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s012 : ((fits03.drop 12).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s016 : ((fits03.drop 16).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s020 : ((fits03.drop 20).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s024 : ((fits03.drop 24).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s028 : ((fits03.drop 28).take 4).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_s032 : ((fits03.drop 32).take 3).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03_end : (fits03.drop 35).all frame003test03=true := by
  decide +kernel

private theorem frame003scope03 : fits03.all frame003test03=true := by
  have h32 := stitchAt 32 3 frame003scope03_s032 frame003scope03_end
  have h28 := stitchAt 28 4 frame003scope03_s028 h32
  have h24 := stitchAt 24 4 frame003scope03_s024 h28
  have h20 := stitchAt 20 4 frame003scope03_s020 h24
  have h16 := stitchAt 16 4 frame003scope03_s016 h20
  have h12 := stitchAt 12 4 frame003scope03_s012 h16
  have h8 := stitchAt 8 4 frame003scope03_s008 h12
  have h4 := stitchAt 4 4 frame003scope03_s004 h8
  have h0 := stitchAt 0 4 frame003scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch03 : batch03.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope03

private abbrev frame003test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch04.stop,F)

private theorem frame003scope04_s000 : ((fits04.drop 0).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s004 : ((fits04.drop 4).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s008 : ((fits04.drop 8).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s012 : ((fits04.drop 12).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s016 : ((fits04.drop 16).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s020 : ((fits04.drop 20).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s024 : ((fits04.drop 24).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s028 : ((fits04.drop 28).take 4).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_s032 : ((fits04.drop 32).take 3).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04_end : (fits04.drop 35).all frame003test04=true := by
  decide +kernel

private theorem frame003scope04 : fits04.all frame003test04=true := by
  have h32 := stitchAt 32 3 frame003scope04_s032 frame003scope04_end
  have h28 := stitchAt 28 4 frame003scope04_s028 h32
  have h24 := stitchAt 24 4 frame003scope04_s024 h28
  have h20 := stitchAt 20 4 frame003scope04_s020 h24
  have h16 := stitchAt 16 4 frame003scope04_s016 h20
  have h12 := stitchAt 12 4 frame003scope04_s012 h16
  have h8 := stitchAt 8 4 frame003scope04_s008 h12
  have h4 := stitchAt 4 4 frame003scope04_s004 h8
  have h0 := stitchAt 0 4 frame003scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch04 : batch04.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope04

private abbrev frame003test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch05.stop,F)

private theorem frame003scope05_s000 : ((fits05.drop 0).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s004 : ((fits05.drop 4).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s008 : ((fits05.drop 8).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s012 : ((fits05.drop 12).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s016 : ((fits05.drop 16).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s020 : ((fits05.drop 20).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s024 : ((fits05.drop 24).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s028 : ((fits05.drop 28).take 4).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_s032 : ((fits05.drop 32).take 3).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05_end : (fits05.drop 35).all frame003test05=true := by
  decide +kernel

private theorem frame003scope05 : fits05.all frame003test05=true := by
  have h32 := stitchAt 32 3 frame003scope05_s032 frame003scope05_end
  have h28 := stitchAt 28 4 frame003scope05_s028 h32
  have h24 := stitchAt 24 4 frame003scope05_s024 h28
  have h20 := stitchAt 20 4 frame003scope05_s020 h24
  have h16 := stitchAt 16 4 frame003scope05_s016 h20
  have h12 := stitchAt 12 4 frame003scope05_s012 h16
  have h8 := stitchAt 8 4 frame003scope05_s008 h12
  have h4 := stitchAt 4 4 frame003scope05_s004 h8
  have h0 := stitchAt 0 4 frame003scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch05 : batch05.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope05

private abbrev frame003test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch06.stop,F)

private theorem frame003scope06_s000 : ((fits06.drop 0).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s004 : ((fits06.drop 4).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s008 : ((fits06.drop 8).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s012 : ((fits06.drop 12).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s016 : ((fits06.drop 16).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s020 : ((fits06.drop 20).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s024 : ((fits06.drop 24).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s028 : ((fits06.drop 28).take 4).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_s032 : ((fits06.drop 32).take 3).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06_end : (fits06.drop 35).all frame003test06=true := by
  decide +kernel

private theorem frame003scope06 : fits06.all frame003test06=true := by
  have h32 := stitchAt 32 3 frame003scope06_s032 frame003scope06_end
  have h28 := stitchAt 28 4 frame003scope06_s028 h32
  have h24 := stitchAt 24 4 frame003scope06_s024 h28
  have h20 := stitchAt 20 4 frame003scope06_s020 h24
  have h16 := stitchAt 16 4 frame003scope06_s016 h20
  have h12 := stitchAt 12 4 frame003scope06_s012 h16
  have h8 := stitchAt 8 4 frame003scope06_s008 h12
  have h4 := stitchAt 4 4 frame003scope06_s004 h8
  have h0 := stitchAt 0 4 frame003scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch06 : batch06.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope06

private abbrev frame003test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame8 (fun z => List.lookup (guideCode z) guide003)
    (batch07.stop,F)

private theorem frame003scope07_s000 : ((fits07.drop 0).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s004 : ((fits07.drop 4).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s008 : ((fits07.drop 8).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s012 : ((fits07.drop 12).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s016 : ((fits07.drop 16).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s020 : ((fits07.drop 20).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s024 : ((fits07.drop 24).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s028 : ((fits07.drop 28).take 4).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_s032 : ((fits07.drop 32).take 3).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07_end : (fits07.drop 35).all frame003test07=true := by
  decide +kernel

private theorem frame003scope07 : fits07.all frame003test07=true := by
  have h32 := stitchAt 32 3 frame003scope07_s032 frame003scope07_end
  have h28 := stitchAt 28 4 frame003scope07_s028 h32
  have h24 := stitchAt 24 4 frame003scope07_s024 h28
  have h20 := stitchAt 20 4 frame003scope07_s020 h24
  have h16 := stitchAt 16 4 frame003scope07_s016 h20
  have h12 := stitchAt 12 4 frame003scope07_s012 h16
  have h8 := stitchAt 8 4 frame003scope07_s008 h12
  have h4 := stitchAt 4 4 frame003scope07_s004 h8
  have h0 := stitchAt 0 4 frame003scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame003batch07 : batch07.pickTest original frame8=true :=
  FitBatch.pickTest_of_scoped scoped003 frame003scope07

private theorem frameBatches003 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame8)=true := by
  simp only [List.all_cons,List.all_nil,frame003batch00,frame003batch01,frame003batch02,frame003batch03,frame003batch04,frame003batch05,frame003batch06,frame003batch07,Bool.and_self]

theorem frameOK003 : frameRankTest original useStop frame8=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches003


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
