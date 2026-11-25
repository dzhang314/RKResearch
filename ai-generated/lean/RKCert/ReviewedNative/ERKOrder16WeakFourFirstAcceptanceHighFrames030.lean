module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK060 : stripTest frame123=true := by decide +kernel

theorem spanOK060 : checkChain 1772 1770 [frame123.span]=true := by decide +kernel

private theorem guideAt060 : List.lookup frame123.span.1 guideTable=some guide060 := by
  decide +kernel

private theorem scoped060 : original.guide frame123.span.1 =
    (fun z => List.lookup (guideCode z) guide060) := by
  funext z
  change (List.lookup frame123.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide060
  simp only [guideAt060,Option.bind_some]

private abbrev frame060test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch00.stop,F)

private theorem frame060scope00_s000 : ((fits00.drop 0).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s004 : ((fits00.drop 4).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s008 : ((fits00.drop 8).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s012 : ((fits00.drop 12).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s016 : ((fits00.drop 16).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s020 : ((fits00.drop 20).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s024 : ((fits00.drop 24).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s028 : ((fits00.drop 28).take 4).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_s032 : ((fits00.drop 32).take 3).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00_end : (fits00.drop 35).all frame060test00=true := by
  decide +kernel

private theorem frame060scope00 : fits00.all frame060test00=true := by
  have h32 := stitchAt 32 3 frame060scope00_s032 frame060scope00_end
  have h28 := stitchAt 28 4 frame060scope00_s028 h32
  have h24 := stitchAt 24 4 frame060scope00_s024 h28
  have h20 := stitchAt 20 4 frame060scope00_s020 h24
  have h16 := stitchAt 16 4 frame060scope00_s016 h20
  have h12 := stitchAt 12 4 frame060scope00_s012 h16
  have h8 := stitchAt 8 4 frame060scope00_s008 h12
  have h4 := stitchAt 4 4 frame060scope00_s004 h8
  have h0 := stitchAt 0 4 frame060scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch00 : batch00.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope00

private abbrev frame060test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch01.stop,F)

private theorem frame060scope01_s000 : ((fits01.drop 0).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s004 : ((fits01.drop 4).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s008 : ((fits01.drop 8).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s012 : ((fits01.drop 12).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s016 : ((fits01.drop 16).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s020 : ((fits01.drop 20).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s024 : ((fits01.drop 24).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s028 : ((fits01.drop 28).take 4).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_s032 : ((fits01.drop 32).take 3).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01_end : (fits01.drop 35).all frame060test01=true := by
  decide +kernel

private theorem frame060scope01 : fits01.all frame060test01=true := by
  have h32 := stitchAt 32 3 frame060scope01_s032 frame060scope01_end
  have h28 := stitchAt 28 4 frame060scope01_s028 h32
  have h24 := stitchAt 24 4 frame060scope01_s024 h28
  have h20 := stitchAt 20 4 frame060scope01_s020 h24
  have h16 := stitchAt 16 4 frame060scope01_s016 h20
  have h12 := stitchAt 12 4 frame060scope01_s012 h16
  have h8 := stitchAt 8 4 frame060scope01_s008 h12
  have h4 := stitchAt 4 4 frame060scope01_s004 h8
  have h0 := stitchAt 0 4 frame060scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch01 : batch01.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope01

private abbrev frame060test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch02.stop,F)

private theorem frame060scope02_s000 : ((fits02.drop 0).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s004 : ((fits02.drop 4).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s008 : ((fits02.drop 8).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s012 : ((fits02.drop 12).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s016 : ((fits02.drop 16).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s020 : ((fits02.drop 20).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s024 : ((fits02.drop 24).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s028 : ((fits02.drop 28).take 4).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_s032 : ((fits02.drop 32).take 3).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02_end : (fits02.drop 35).all frame060test02=true := by
  decide +kernel

private theorem frame060scope02 : fits02.all frame060test02=true := by
  have h32 := stitchAt 32 3 frame060scope02_s032 frame060scope02_end
  have h28 := stitchAt 28 4 frame060scope02_s028 h32
  have h24 := stitchAt 24 4 frame060scope02_s024 h28
  have h20 := stitchAt 20 4 frame060scope02_s020 h24
  have h16 := stitchAt 16 4 frame060scope02_s016 h20
  have h12 := stitchAt 12 4 frame060scope02_s012 h16
  have h8 := stitchAt 8 4 frame060scope02_s008 h12
  have h4 := stitchAt 4 4 frame060scope02_s004 h8
  have h0 := stitchAt 0 4 frame060scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch02 : batch02.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope02

private abbrev frame060test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch03.stop,F)

private theorem frame060scope03_s000 : ((fits03.drop 0).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s004 : ((fits03.drop 4).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s008 : ((fits03.drop 8).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s012 : ((fits03.drop 12).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s016 : ((fits03.drop 16).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s020 : ((fits03.drop 20).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s024 : ((fits03.drop 24).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s028 : ((fits03.drop 28).take 4).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_s032 : ((fits03.drop 32).take 3).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03_end : (fits03.drop 35).all frame060test03=true := by
  decide +kernel

private theorem frame060scope03 : fits03.all frame060test03=true := by
  have h32 := stitchAt 32 3 frame060scope03_s032 frame060scope03_end
  have h28 := stitchAt 28 4 frame060scope03_s028 h32
  have h24 := stitchAt 24 4 frame060scope03_s024 h28
  have h20 := stitchAt 20 4 frame060scope03_s020 h24
  have h16 := stitchAt 16 4 frame060scope03_s016 h20
  have h12 := stitchAt 12 4 frame060scope03_s012 h16
  have h8 := stitchAt 8 4 frame060scope03_s008 h12
  have h4 := stitchAt 4 4 frame060scope03_s004 h8
  have h0 := stitchAt 0 4 frame060scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch03 : batch03.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope03

private abbrev frame060test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch04.stop,F)

private theorem frame060scope04_s000 : ((fits04.drop 0).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s004 : ((fits04.drop 4).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s008 : ((fits04.drop 8).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s012 : ((fits04.drop 12).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s016 : ((fits04.drop 16).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s020 : ((fits04.drop 20).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s024 : ((fits04.drop 24).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s028 : ((fits04.drop 28).take 4).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_s032 : ((fits04.drop 32).take 3).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04_end : (fits04.drop 35).all frame060test04=true := by
  decide +kernel

private theorem frame060scope04 : fits04.all frame060test04=true := by
  have h32 := stitchAt 32 3 frame060scope04_s032 frame060scope04_end
  have h28 := stitchAt 28 4 frame060scope04_s028 h32
  have h24 := stitchAt 24 4 frame060scope04_s024 h28
  have h20 := stitchAt 20 4 frame060scope04_s020 h24
  have h16 := stitchAt 16 4 frame060scope04_s016 h20
  have h12 := stitchAt 12 4 frame060scope04_s012 h16
  have h8 := stitchAt 8 4 frame060scope04_s008 h12
  have h4 := stitchAt 4 4 frame060scope04_s004 h8
  have h0 := stitchAt 0 4 frame060scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch04 : batch04.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope04

private abbrev frame060test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch05.stop,F)

private theorem frame060scope05_s000 : ((fits05.drop 0).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s004 : ((fits05.drop 4).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s008 : ((fits05.drop 8).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s012 : ((fits05.drop 12).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s016 : ((fits05.drop 16).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s020 : ((fits05.drop 20).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s024 : ((fits05.drop 24).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s028 : ((fits05.drop 28).take 4).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_s032 : ((fits05.drop 32).take 3).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05_end : (fits05.drop 35).all frame060test05=true := by
  decide +kernel

private theorem frame060scope05 : fits05.all frame060test05=true := by
  have h32 := stitchAt 32 3 frame060scope05_s032 frame060scope05_end
  have h28 := stitchAt 28 4 frame060scope05_s028 h32
  have h24 := stitchAt 24 4 frame060scope05_s024 h28
  have h20 := stitchAt 20 4 frame060scope05_s020 h24
  have h16 := stitchAt 16 4 frame060scope05_s016 h20
  have h12 := stitchAt 12 4 frame060scope05_s012 h16
  have h8 := stitchAt 8 4 frame060scope05_s008 h12
  have h4 := stitchAt 4 4 frame060scope05_s004 h8
  have h0 := stitchAt 0 4 frame060scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch05 : batch05.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope05

private abbrev frame060test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch06.stop,F)

private theorem frame060scope06_s000 : ((fits06.drop 0).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s004 : ((fits06.drop 4).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s008 : ((fits06.drop 8).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s012 : ((fits06.drop 12).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s016 : ((fits06.drop 16).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s020 : ((fits06.drop 20).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s024 : ((fits06.drop 24).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s028 : ((fits06.drop 28).take 4).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_s032 : ((fits06.drop 32).take 3).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06_end : (fits06.drop 35).all frame060test06=true := by
  decide +kernel

private theorem frame060scope06 : fits06.all frame060test06=true := by
  have h32 := stitchAt 32 3 frame060scope06_s032 frame060scope06_end
  have h28 := stitchAt 28 4 frame060scope06_s028 h32
  have h24 := stitchAt 24 4 frame060scope06_s024 h28
  have h20 := stitchAt 20 4 frame060scope06_s020 h24
  have h16 := stitchAt 16 4 frame060scope06_s016 h20
  have h12 := stitchAt 12 4 frame060scope06_s012 h16
  have h8 := stitchAt 8 4 frame060scope06_s008 h12
  have h4 := stitchAt 4 4 frame060scope06_s004 h8
  have h0 := stitchAt 0 4 frame060scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch06 : batch06.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope06

private abbrev frame060test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame123 (fun z => List.lookup (guideCode z) guide060)
    (batch07.stop,F)

private theorem frame060scope07_s000 : ((fits07.drop 0).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s004 : ((fits07.drop 4).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s008 : ((fits07.drop 8).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s012 : ((fits07.drop 12).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s016 : ((fits07.drop 16).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s020 : ((fits07.drop 20).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s024 : ((fits07.drop 24).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s028 : ((fits07.drop 28).take 4).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_s032 : ((fits07.drop 32).take 3).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07_end : (fits07.drop 35).all frame060test07=true := by
  decide +kernel

private theorem frame060scope07 : fits07.all frame060test07=true := by
  have h32 := stitchAt 32 3 frame060scope07_s032 frame060scope07_end
  have h28 := stitchAt 28 4 frame060scope07_s028 h32
  have h24 := stitchAt 24 4 frame060scope07_s024 h28
  have h20 := stitchAt 20 4 frame060scope07_s020 h24
  have h16 := stitchAt 16 4 frame060scope07_s016 h20
  have h12 := stitchAt 12 4 frame060scope07_s012 h16
  have h8 := stitchAt 8 4 frame060scope07_s008 h12
  have h4 := stitchAt 4 4 frame060scope07_s004 h8
  have h0 := stitchAt 0 4 frame060scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame060batch07 : batch07.pickTest original frame123=true :=
  FitBatch.pickTest_of_scoped scoped060 frame060scope07

private theorem frameBatches060 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame123)=true := by
  simp only [List.all_cons,List.all_nil,frame060batch00,frame060batch01,frame060batch02,frame060batch03,frame060batch04,frame060batch05,frame060batch06,frame060batch07,Bool.and_self]

theorem frameOK060 : frameRankTest original useStop frame123=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches060

theorem stripOK061 : stripTest frame125=true := by decide +kernel

theorem spanOK061 : checkChain 1774 1772 [frame125.span]=true := by decide +kernel

private theorem guideAt061 : List.lookup frame125.span.1 guideTable=some guide061 := by
  decide +kernel

private theorem scoped061 : original.guide frame125.span.1 =
    (fun z => List.lookup (guideCode z) guide061) := by
  funext z
  change (List.lookup frame125.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide061
  simp only [guideAt061,Option.bind_some]

private abbrev frame061test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch00.stop,F)

private theorem frame061scope00_s000 : ((fits00.drop 0).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s004 : ((fits00.drop 4).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s008 : ((fits00.drop 8).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s012 : ((fits00.drop 12).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s016 : ((fits00.drop 16).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s020 : ((fits00.drop 20).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s024 : ((fits00.drop 24).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s028 : ((fits00.drop 28).take 4).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_s032 : ((fits00.drop 32).take 3).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00_end : (fits00.drop 35).all frame061test00=true := by
  decide +kernel

private theorem frame061scope00 : fits00.all frame061test00=true := by
  have h32 := stitchAt 32 3 frame061scope00_s032 frame061scope00_end
  have h28 := stitchAt 28 4 frame061scope00_s028 h32
  have h24 := stitchAt 24 4 frame061scope00_s024 h28
  have h20 := stitchAt 20 4 frame061scope00_s020 h24
  have h16 := stitchAt 16 4 frame061scope00_s016 h20
  have h12 := stitchAt 12 4 frame061scope00_s012 h16
  have h8 := stitchAt 8 4 frame061scope00_s008 h12
  have h4 := stitchAt 4 4 frame061scope00_s004 h8
  have h0 := stitchAt 0 4 frame061scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch00 : batch00.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope00

private abbrev frame061test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch01.stop,F)

private theorem frame061scope01_s000 : ((fits01.drop 0).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s004 : ((fits01.drop 4).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s008 : ((fits01.drop 8).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s012 : ((fits01.drop 12).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s016 : ((fits01.drop 16).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s020 : ((fits01.drop 20).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s024 : ((fits01.drop 24).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s028 : ((fits01.drop 28).take 4).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_s032 : ((fits01.drop 32).take 3).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01_end : (fits01.drop 35).all frame061test01=true := by
  decide +kernel

private theorem frame061scope01 : fits01.all frame061test01=true := by
  have h32 := stitchAt 32 3 frame061scope01_s032 frame061scope01_end
  have h28 := stitchAt 28 4 frame061scope01_s028 h32
  have h24 := stitchAt 24 4 frame061scope01_s024 h28
  have h20 := stitchAt 20 4 frame061scope01_s020 h24
  have h16 := stitchAt 16 4 frame061scope01_s016 h20
  have h12 := stitchAt 12 4 frame061scope01_s012 h16
  have h8 := stitchAt 8 4 frame061scope01_s008 h12
  have h4 := stitchAt 4 4 frame061scope01_s004 h8
  have h0 := stitchAt 0 4 frame061scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch01 : batch01.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope01

private abbrev frame061test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch02.stop,F)

private theorem frame061scope02_s000 : ((fits02.drop 0).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s004 : ((fits02.drop 4).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s008 : ((fits02.drop 8).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s012 : ((fits02.drop 12).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s016 : ((fits02.drop 16).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s020 : ((fits02.drop 20).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s024 : ((fits02.drop 24).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s028 : ((fits02.drop 28).take 4).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_s032 : ((fits02.drop 32).take 3).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02_end : (fits02.drop 35).all frame061test02=true := by
  decide +kernel

private theorem frame061scope02 : fits02.all frame061test02=true := by
  have h32 := stitchAt 32 3 frame061scope02_s032 frame061scope02_end
  have h28 := stitchAt 28 4 frame061scope02_s028 h32
  have h24 := stitchAt 24 4 frame061scope02_s024 h28
  have h20 := stitchAt 20 4 frame061scope02_s020 h24
  have h16 := stitchAt 16 4 frame061scope02_s016 h20
  have h12 := stitchAt 12 4 frame061scope02_s012 h16
  have h8 := stitchAt 8 4 frame061scope02_s008 h12
  have h4 := stitchAt 4 4 frame061scope02_s004 h8
  have h0 := stitchAt 0 4 frame061scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch02 : batch02.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope02

private abbrev frame061test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch03.stop,F)

private theorem frame061scope03_s000 : ((fits03.drop 0).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s004 : ((fits03.drop 4).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s008 : ((fits03.drop 8).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s012 : ((fits03.drop 12).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s016 : ((fits03.drop 16).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s020 : ((fits03.drop 20).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s024 : ((fits03.drop 24).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s028 : ((fits03.drop 28).take 4).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_s032 : ((fits03.drop 32).take 3).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03_end : (fits03.drop 35).all frame061test03=true := by
  decide +kernel

private theorem frame061scope03 : fits03.all frame061test03=true := by
  have h32 := stitchAt 32 3 frame061scope03_s032 frame061scope03_end
  have h28 := stitchAt 28 4 frame061scope03_s028 h32
  have h24 := stitchAt 24 4 frame061scope03_s024 h28
  have h20 := stitchAt 20 4 frame061scope03_s020 h24
  have h16 := stitchAt 16 4 frame061scope03_s016 h20
  have h12 := stitchAt 12 4 frame061scope03_s012 h16
  have h8 := stitchAt 8 4 frame061scope03_s008 h12
  have h4 := stitchAt 4 4 frame061scope03_s004 h8
  have h0 := stitchAt 0 4 frame061scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch03 : batch03.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope03

private abbrev frame061test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch04.stop,F)

private theorem frame061scope04_s000 : ((fits04.drop 0).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s004 : ((fits04.drop 4).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s008 : ((fits04.drop 8).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s012 : ((fits04.drop 12).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s016 : ((fits04.drop 16).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s020 : ((fits04.drop 20).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s024 : ((fits04.drop 24).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s028 : ((fits04.drop 28).take 4).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_s032 : ((fits04.drop 32).take 3).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04_end : (fits04.drop 35).all frame061test04=true := by
  decide +kernel

private theorem frame061scope04 : fits04.all frame061test04=true := by
  have h32 := stitchAt 32 3 frame061scope04_s032 frame061scope04_end
  have h28 := stitchAt 28 4 frame061scope04_s028 h32
  have h24 := stitchAt 24 4 frame061scope04_s024 h28
  have h20 := stitchAt 20 4 frame061scope04_s020 h24
  have h16 := stitchAt 16 4 frame061scope04_s016 h20
  have h12 := stitchAt 12 4 frame061scope04_s012 h16
  have h8 := stitchAt 8 4 frame061scope04_s008 h12
  have h4 := stitchAt 4 4 frame061scope04_s004 h8
  have h0 := stitchAt 0 4 frame061scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch04 : batch04.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope04

private abbrev frame061test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch05.stop,F)

private theorem frame061scope05_s000 : ((fits05.drop 0).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s004 : ((fits05.drop 4).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s008 : ((fits05.drop 8).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s012 : ((fits05.drop 12).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s016 : ((fits05.drop 16).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s020 : ((fits05.drop 20).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s024 : ((fits05.drop 24).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s028 : ((fits05.drop 28).take 4).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_s032 : ((fits05.drop 32).take 3).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05_end : (fits05.drop 35).all frame061test05=true := by
  decide +kernel

private theorem frame061scope05 : fits05.all frame061test05=true := by
  have h32 := stitchAt 32 3 frame061scope05_s032 frame061scope05_end
  have h28 := stitchAt 28 4 frame061scope05_s028 h32
  have h24 := stitchAt 24 4 frame061scope05_s024 h28
  have h20 := stitchAt 20 4 frame061scope05_s020 h24
  have h16 := stitchAt 16 4 frame061scope05_s016 h20
  have h12 := stitchAt 12 4 frame061scope05_s012 h16
  have h8 := stitchAt 8 4 frame061scope05_s008 h12
  have h4 := stitchAt 4 4 frame061scope05_s004 h8
  have h0 := stitchAt 0 4 frame061scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch05 : batch05.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope05

private abbrev frame061test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch06.stop,F)

private theorem frame061scope06_s000 : ((fits06.drop 0).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s004 : ((fits06.drop 4).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s008 : ((fits06.drop 8).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s012 : ((fits06.drop 12).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s016 : ((fits06.drop 16).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s020 : ((fits06.drop 20).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s024 : ((fits06.drop 24).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s028 : ((fits06.drop 28).take 4).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_s032 : ((fits06.drop 32).take 3).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06_end : (fits06.drop 35).all frame061test06=true := by
  decide +kernel

private theorem frame061scope06 : fits06.all frame061test06=true := by
  have h32 := stitchAt 32 3 frame061scope06_s032 frame061scope06_end
  have h28 := stitchAt 28 4 frame061scope06_s028 h32
  have h24 := stitchAt 24 4 frame061scope06_s024 h28
  have h20 := stitchAt 20 4 frame061scope06_s020 h24
  have h16 := stitchAt 16 4 frame061scope06_s016 h20
  have h12 := stitchAt 12 4 frame061scope06_s012 h16
  have h8 := stitchAt 8 4 frame061scope06_s008 h12
  have h4 := stitchAt 4 4 frame061scope06_s004 h8
  have h0 := stitchAt 0 4 frame061scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch06 : batch06.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope06

private abbrev frame061test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame125 (fun z => List.lookup (guideCode z) guide061)
    (batch07.stop,F)

private theorem frame061scope07_s000 : ((fits07.drop 0).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s004 : ((fits07.drop 4).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s008 : ((fits07.drop 8).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s012 : ((fits07.drop 12).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s016 : ((fits07.drop 16).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s020 : ((fits07.drop 20).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s024 : ((fits07.drop 24).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s028 : ((fits07.drop 28).take 4).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_s032 : ((fits07.drop 32).take 3).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07_end : (fits07.drop 35).all frame061test07=true := by
  decide +kernel

private theorem frame061scope07 : fits07.all frame061test07=true := by
  have h32 := stitchAt 32 3 frame061scope07_s032 frame061scope07_end
  have h28 := stitchAt 28 4 frame061scope07_s028 h32
  have h24 := stitchAt 24 4 frame061scope07_s024 h28
  have h20 := stitchAt 20 4 frame061scope07_s020 h24
  have h16 := stitchAt 16 4 frame061scope07_s016 h20
  have h12 := stitchAt 12 4 frame061scope07_s012 h16
  have h8 := stitchAt 8 4 frame061scope07_s008 h12
  have h4 := stitchAt 4 4 frame061scope07_s004 h8
  have h0 := stitchAt 0 4 frame061scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame061batch07 : batch07.pickTest original frame125=true :=
  FitBatch.pickTest_of_scoped scoped061 frame061scope07

private theorem frameBatches061 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame125)=true := by
  simp only [List.all_cons,List.all_nil,frame061batch00,frame061batch01,frame061batch02,frame061batch03,frame061batch04,frame061batch05,frame061batch06,frame061batch07,Bool.and_self]

theorem frameOK061 : frameRankTest original useStop frame125=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches061


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
