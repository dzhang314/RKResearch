module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK046 : stripTest frame96=true := by decide +kernel

theorem spanOK046 : checkChain 1754 1752 [frame96.span]=true := by decide +kernel

private theorem guideAt046 : List.lookup frame96.span.1 guideTable=some guide046 := by
  decide +kernel

private theorem scoped046 : original.guide frame96.span.1 =
    (fun z => List.lookup (guideCode z) guide046) := by
  funext z
  change (List.lookup frame96.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide046
  simp only [guideAt046,Option.bind_some]

private abbrev frame046test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch00.stop,F)

private theorem frame046scope00_s000 : ((fits00.drop 0).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s004 : ((fits00.drop 4).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s008 : ((fits00.drop 8).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s012 : ((fits00.drop 12).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s016 : ((fits00.drop 16).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s020 : ((fits00.drop 20).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s024 : ((fits00.drop 24).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s028 : ((fits00.drop 28).take 4).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_s032 : ((fits00.drop 32).take 3).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00_end : (fits00.drop 35).all frame046test00=true := by
  decide +kernel

private theorem frame046scope00 : fits00.all frame046test00=true := by
  have h32 := stitchAt 32 3 frame046scope00_s032 frame046scope00_end
  have h28 := stitchAt 28 4 frame046scope00_s028 h32
  have h24 := stitchAt 24 4 frame046scope00_s024 h28
  have h20 := stitchAt 20 4 frame046scope00_s020 h24
  have h16 := stitchAt 16 4 frame046scope00_s016 h20
  have h12 := stitchAt 12 4 frame046scope00_s012 h16
  have h8 := stitchAt 8 4 frame046scope00_s008 h12
  have h4 := stitchAt 4 4 frame046scope00_s004 h8
  have h0 := stitchAt 0 4 frame046scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch00 : batch00.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope00

private abbrev frame046test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch01.stop,F)

private theorem frame046scope01_s000 : ((fits01.drop 0).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s004 : ((fits01.drop 4).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s008 : ((fits01.drop 8).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s012 : ((fits01.drop 12).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s016 : ((fits01.drop 16).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s020 : ((fits01.drop 20).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s024 : ((fits01.drop 24).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s028 : ((fits01.drop 28).take 4).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_s032 : ((fits01.drop 32).take 3).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01_end : (fits01.drop 35).all frame046test01=true := by
  decide +kernel

private theorem frame046scope01 : fits01.all frame046test01=true := by
  have h32 := stitchAt 32 3 frame046scope01_s032 frame046scope01_end
  have h28 := stitchAt 28 4 frame046scope01_s028 h32
  have h24 := stitchAt 24 4 frame046scope01_s024 h28
  have h20 := stitchAt 20 4 frame046scope01_s020 h24
  have h16 := stitchAt 16 4 frame046scope01_s016 h20
  have h12 := stitchAt 12 4 frame046scope01_s012 h16
  have h8 := stitchAt 8 4 frame046scope01_s008 h12
  have h4 := stitchAt 4 4 frame046scope01_s004 h8
  have h0 := stitchAt 0 4 frame046scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch01 : batch01.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope01

private abbrev frame046test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch02.stop,F)

private theorem frame046scope02_s000 : ((fits02.drop 0).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s004 : ((fits02.drop 4).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s008 : ((fits02.drop 8).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s012 : ((fits02.drop 12).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s016 : ((fits02.drop 16).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s020 : ((fits02.drop 20).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s024 : ((fits02.drop 24).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s028 : ((fits02.drop 28).take 4).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_s032 : ((fits02.drop 32).take 3).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02_end : (fits02.drop 35).all frame046test02=true := by
  decide +kernel

private theorem frame046scope02 : fits02.all frame046test02=true := by
  have h32 := stitchAt 32 3 frame046scope02_s032 frame046scope02_end
  have h28 := stitchAt 28 4 frame046scope02_s028 h32
  have h24 := stitchAt 24 4 frame046scope02_s024 h28
  have h20 := stitchAt 20 4 frame046scope02_s020 h24
  have h16 := stitchAt 16 4 frame046scope02_s016 h20
  have h12 := stitchAt 12 4 frame046scope02_s012 h16
  have h8 := stitchAt 8 4 frame046scope02_s008 h12
  have h4 := stitchAt 4 4 frame046scope02_s004 h8
  have h0 := stitchAt 0 4 frame046scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch02 : batch02.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope02

private abbrev frame046test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch03.stop,F)

private theorem frame046scope03_s000 : ((fits03.drop 0).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s004 : ((fits03.drop 4).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s008 : ((fits03.drop 8).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s012 : ((fits03.drop 12).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s016 : ((fits03.drop 16).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s020 : ((fits03.drop 20).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s024 : ((fits03.drop 24).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s028 : ((fits03.drop 28).take 4).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_s032 : ((fits03.drop 32).take 3).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03_end : (fits03.drop 35).all frame046test03=true := by
  decide +kernel

private theorem frame046scope03 : fits03.all frame046test03=true := by
  have h32 := stitchAt 32 3 frame046scope03_s032 frame046scope03_end
  have h28 := stitchAt 28 4 frame046scope03_s028 h32
  have h24 := stitchAt 24 4 frame046scope03_s024 h28
  have h20 := stitchAt 20 4 frame046scope03_s020 h24
  have h16 := stitchAt 16 4 frame046scope03_s016 h20
  have h12 := stitchAt 12 4 frame046scope03_s012 h16
  have h8 := stitchAt 8 4 frame046scope03_s008 h12
  have h4 := stitchAt 4 4 frame046scope03_s004 h8
  have h0 := stitchAt 0 4 frame046scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch03 : batch03.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope03

private abbrev frame046test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch04.stop,F)

private theorem frame046scope04_s000 : ((fits04.drop 0).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s004 : ((fits04.drop 4).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s008 : ((fits04.drop 8).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s012 : ((fits04.drop 12).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s016 : ((fits04.drop 16).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s020 : ((fits04.drop 20).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s024 : ((fits04.drop 24).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s028 : ((fits04.drop 28).take 4).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_s032 : ((fits04.drop 32).take 3).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04_end : (fits04.drop 35).all frame046test04=true := by
  decide +kernel

private theorem frame046scope04 : fits04.all frame046test04=true := by
  have h32 := stitchAt 32 3 frame046scope04_s032 frame046scope04_end
  have h28 := stitchAt 28 4 frame046scope04_s028 h32
  have h24 := stitchAt 24 4 frame046scope04_s024 h28
  have h20 := stitchAt 20 4 frame046scope04_s020 h24
  have h16 := stitchAt 16 4 frame046scope04_s016 h20
  have h12 := stitchAt 12 4 frame046scope04_s012 h16
  have h8 := stitchAt 8 4 frame046scope04_s008 h12
  have h4 := stitchAt 4 4 frame046scope04_s004 h8
  have h0 := stitchAt 0 4 frame046scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch04 : batch04.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope04

private abbrev frame046test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch05.stop,F)

private theorem frame046scope05_s000 : ((fits05.drop 0).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s004 : ((fits05.drop 4).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s008 : ((fits05.drop 8).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s012 : ((fits05.drop 12).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s016 : ((fits05.drop 16).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s020 : ((fits05.drop 20).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s024 : ((fits05.drop 24).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s028 : ((fits05.drop 28).take 4).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_s032 : ((fits05.drop 32).take 3).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05_end : (fits05.drop 35).all frame046test05=true := by
  decide +kernel

private theorem frame046scope05 : fits05.all frame046test05=true := by
  have h32 := stitchAt 32 3 frame046scope05_s032 frame046scope05_end
  have h28 := stitchAt 28 4 frame046scope05_s028 h32
  have h24 := stitchAt 24 4 frame046scope05_s024 h28
  have h20 := stitchAt 20 4 frame046scope05_s020 h24
  have h16 := stitchAt 16 4 frame046scope05_s016 h20
  have h12 := stitchAt 12 4 frame046scope05_s012 h16
  have h8 := stitchAt 8 4 frame046scope05_s008 h12
  have h4 := stitchAt 4 4 frame046scope05_s004 h8
  have h0 := stitchAt 0 4 frame046scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch05 : batch05.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope05

private abbrev frame046test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch06.stop,F)

private theorem frame046scope06_s000 : ((fits06.drop 0).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s004 : ((fits06.drop 4).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s008 : ((fits06.drop 8).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s012 : ((fits06.drop 12).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s016 : ((fits06.drop 16).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s020 : ((fits06.drop 20).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s024 : ((fits06.drop 24).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s028 : ((fits06.drop 28).take 4).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_s032 : ((fits06.drop 32).take 3).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06_end : (fits06.drop 35).all frame046test06=true := by
  decide +kernel

private theorem frame046scope06 : fits06.all frame046test06=true := by
  have h32 := stitchAt 32 3 frame046scope06_s032 frame046scope06_end
  have h28 := stitchAt 28 4 frame046scope06_s028 h32
  have h24 := stitchAt 24 4 frame046scope06_s024 h28
  have h20 := stitchAt 20 4 frame046scope06_s020 h24
  have h16 := stitchAt 16 4 frame046scope06_s016 h20
  have h12 := stitchAt 12 4 frame046scope06_s012 h16
  have h8 := stitchAt 8 4 frame046scope06_s008 h12
  have h4 := stitchAt 4 4 frame046scope06_s004 h8
  have h0 := stitchAt 0 4 frame046scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch06 : batch06.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope06

private abbrev frame046test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame96 (fun z => List.lookup (guideCode z) guide046)
    (batch07.stop,F)

private theorem frame046scope07_s000 : ((fits07.drop 0).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s004 : ((fits07.drop 4).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s008 : ((fits07.drop 8).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s012 : ((fits07.drop 12).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s016 : ((fits07.drop 16).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s020 : ((fits07.drop 20).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s024 : ((fits07.drop 24).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s028 : ((fits07.drop 28).take 4).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_s032 : ((fits07.drop 32).take 3).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07_end : (fits07.drop 35).all frame046test07=true := by
  decide +kernel

private theorem frame046scope07 : fits07.all frame046test07=true := by
  have h32 := stitchAt 32 3 frame046scope07_s032 frame046scope07_end
  have h28 := stitchAt 28 4 frame046scope07_s028 h32
  have h24 := stitchAt 24 4 frame046scope07_s024 h28
  have h20 := stitchAt 20 4 frame046scope07_s020 h24
  have h16 := stitchAt 16 4 frame046scope07_s016 h20
  have h12 := stitchAt 12 4 frame046scope07_s012 h16
  have h8 := stitchAt 8 4 frame046scope07_s008 h12
  have h4 := stitchAt 4 4 frame046scope07_s004 h8
  have h0 := stitchAt 0 4 frame046scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame046batch07 : batch07.pickTest original frame96=true :=
  FitBatch.pickTest_of_scoped scoped046 frame046scope07

private theorem frameBatches046 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame96)=true := by
  simp only [List.all_cons,List.all_nil,frame046batch00,frame046batch01,frame046batch02,frame046batch03,frame046batch04,frame046batch05,frame046batch06,frame046batch07,Bool.and_self]

theorem frameOK046 : frameRankTest original useStop frame96=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches046

theorem stripOK047 : stripTest frame97=true := by decide +kernel

theorem spanOK047 : checkChain 1756 1754 [frame97.span]=true := by decide +kernel

private theorem guideAt047 : List.lookup frame97.span.1 guideTable=some guide047 := by
  decide +kernel

private theorem scoped047 : original.guide frame97.span.1 =
    (fun z => List.lookup (guideCode z) guide047) := by
  funext z
  change (List.lookup frame97.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide047
  simp only [guideAt047,Option.bind_some]

private abbrev frame047test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch00.stop,F)

private theorem frame047scope00_s000 : ((fits00.drop 0).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s004 : ((fits00.drop 4).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s008 : ((fits00.drop 8).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s012 : ((fits00.drop 12).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s016 : ((fits00.drop 16).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s020 : ((fits00.drop 20).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s024 : ((fits00.drop 24).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s028 : ((fits00.drop 28).take 4).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_s032 : ((fits00.drop 32).take 3).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00_end : (fits00.drop 35).all frame047test00=true := by
  decide +kernel

private theorem frame047scope00 : fits00.all frame047test00=true := by
  have h32 := stitchAt 32 3 frame047scope00_s032 frame047scope00_end
  have h28 := stitchAt 28 4 frame047scope00_s028 h32
  have h24 := stitchAt 24 4 frame047scope00_s024 h28
  have h20 := stitchAt 20 4 frame047scope00_s020 h24
  have h16 := stitchAt 16 4 frame047scope00_s016 h20
  have h12 := stitchAt 12 4 frame047scope00_s012 h16
  have h8 := stitchAt 8 4 frame047scope00_s008 h12
  have h4 := stitchAt 4 4 frame047scope00_s004 h8
  have h0 := stitchAt 0 4 frame047scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch00 : batch00.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope00

private abbrev frame047test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch01.stop,F)

private theorem frame047scope01_s000 : ((fits01.drop 0).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s004 : ((fits01.drop 4).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s008 : ((fits01.drop 8).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s012 : ((fits01.drop 12).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s016 : ((fits01.drop 16).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s020 : ((fits01.drop 20).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s024 : ((fits01.drop 24).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s028 : ((fits01.drop 28).take 4).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_s032 : ((fits01.drop 32).take 3).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01_end : (fits01.drop 35).all frame047test01=true := by
  decide +kernel

private theorem frame047scope01 : fits01.all frame047test01=true := by
  have h32 := stitchAt 32 3 frame047scope01_s032 frame047scope01_end
  have h28 := stitchAt 28 4 frame047scope01_s028 h32
  have h24 := stitchAt 24 4 frame047scope01_s024 h28
  have h20 := stitchAt 20 4 frame047scope01_s020 h24
  have h16 := stitchAt 16 4 frame047scope01_s016 h20
  have h12 := stitchAt 12 4 frame047scope01_s012 h16
  have h8 := stitchAt 8 4 frame047scope01_s008 h12
  have h4 := stitchAt 4 4 frame047scope01_s004 h8
  have h0 := stitchAt 0 4 frame047scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch01 : batch01.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope01

private abbrev frame047test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch02.stop,F)

private theorem frame047scope02_s000 : ((fits02.drop 0).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s004 : ((fits02.drop 4).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s008 : ((fits02.drop 8).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s012 : ((fits02.drop 12).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s016 : ((fits02.drop 16).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s020 : ((fits02.drop 20).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s024 : ((fits02.drop 24).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s028 : ((fits02.drop 28).take 4).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_s032 : ((fits02.drop 32).take 3).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02_end : (fits02.drop 35).all frame047test02=true := by
  decide +kernel

private theorem frame047scope02 : fits02.all frame047test02=true := by
  have h32 := stitchAt 32 3 frame047scope02_s032 frame047scope02_end
  have h28 := stitchAt 28 4 frame047scope02_s028 h32
  have h24 := stitchAt 24 4 frame047scope02_s024 h28
  have h20 := stitchAt 20 4 frame047scope02_s020 h24
  have h16 := stitchAt 16 4 frame047scope02_s016 h20
  have h12 := stitchAt 12 4 frame047scope02_s012 h16
  have h8 := stitchAt 8 4 frame047scope02_s008 h12
  have h4 := stitchAt 4 4 frame047scope02_s004 h8
  have h0 := stitchAt 0 4 frame047scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch02 : batch02.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope02

private abbrev frame047test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch03.stop,F)

private theorem frame047scope03_s000 : ((fits03.drop 0).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s004 : ((fits03.drop 4).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s008 : ((fits03.drop 8).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s012 : ((fits03.drop 12).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s016 : ((fits03.drop 16).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s020 : ((fits03.drop 20).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s024 : ((fits03.drop 24).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s028 : ((fits03.drop 28).take 4).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_s032 : ((fits03.drop 32).take 3).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03_end : (fits03.drop 35).all frame047test03=true := by
  decide +kernel

private theorem frame047scope03 : fits03.all frame047test03=true := by
  have h32 := stitchAt 32 3 frame047scope03_s032 frame047scope03_end
  have h28 := stitchAt 28 4 frame047scope03_s028 h32
  have h24 := stitchAt 24 4 frame047scope03_s024 h28
  have h20 := stitchAt 20 4 frame047scope03_s020 h24
  have h16 := stitchAt 16 4 frame047scope03_s016 h20
  have h12 := stitchAt 12 4 frame047scope03_s012 h16
  have h8 := stitchAt 8 4 frame047scope03_s008 h12
  have h4 := stitchAt 4 4 frame047scope03_s004 h8
  have h0 := stitchAt 0 4 frame047scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch03 : batch03.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope03

private abbrev frame047test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch04.stop,F)

private theorem frame047scope04_s000 : ((fits04.drop 0).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s004 : ((fits04.drop 4).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s008 : ((fits04.drop 8).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s012 : ((fits04.drop 12).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s016 : ((fits04.drop 16).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s020 : ((fits04.drop 20).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s024 : ((fits04.drop 24).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s028 : ((fits04.drop 28).take 4).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_s032 : ((fits04.drop 32).take 3).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04_end : (fits04.drop 35).all frame047test04=true := by
  decide +kernel

private theorem frame047scope04 : fits04.all frame047test04=true := by
  have h32 := stitchAt 32 3 frame047scope04_s032 frame047scope04_end
  have h28 := stitchAt 28 4 frame047scope04_s028 h32
  have h24 := stitchAt 24 4 frame047scope04_s024 h28
  have h20 := stitchAt 20 4 frame047scope04_s020 h24
  have h16 := stitchAt 16 4 frame047scope04_s016 h20
  have h12 := stitchAt 12 4 frame047scope04_s012 h16
  have h8 := stitchAt 8 4 frame047scope04_s008 h12
  have h4 := stitchAt 4 4 frame047scope04_s004 h8
  have h0 := stitchAt 0 4 frame047scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch04 : batch04.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope04

private abbrev frame047test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch05.stop,F)

private theorem frame047scope05_s000 : ((fits05.drop 0).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s004 : ((fits05.drop 4).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s008 : ((fits05.drop 8).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s012 : ((fits05.drop 12).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s016 : ((fits05.drop 16).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s020 : ((fits05.drop 20).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s024 : ((fits05.drop 24).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s028 : ((fits05.drop 28).take 4).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_s032 : ((fits05.drop 32).take 3).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05_end : (fits05.drop 35).all frame047test05=true := by
  decide +kernel

private theorem frame047scope05 : fits05.all frame047test05=true := by
  have h32 := stitchAt 32 3 frame047scope05_s032 frame047scope05_end
  have h28 := stitchAt 28 4 frame047scope05_s028 h32
  have h24 := stitchAt 24 4 frame047scope05_s024 h28
  have h20 := stitchAt 20 4 frame047scope05_s020 h24
  have h16 := stitchAt 16 4 frame047scope05_s016 h20
  have h12 := stitchAt 12 4 frame047scope05_s012 h16
  have h8 := stitchAt 8 4 frame047scope05_s008 h12
  have h4 := stitchAt 4 4 frame047scope05_s004 h8
  have h0 := stitchAt 0 4 frame047scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch05 : batch05.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope05

private abbrev frame047test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch06.stop,F)

private theorem frame047scope06_s000 : ((fits06.drop 0).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s004 : ((fits06.drop 4).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s008 : ((fits06.drop 8).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s012 : ((fits06.drop 12).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s016 : ((fits06.drop 16).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s020 : ((fits06.drop 20).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s024 : ((fits06.drop 24).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s028 : ((fits06.drop 28).take 4).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_s032 : ((fits06.drop 32).take 3).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06_end : (fits06.drop 35).all frame047test06=true := by
  decide +kernel

private theorem frame047scope06 : fits06.all frame047test06=true := by
  have h32 := stitchAt 32 3 frame047scope06_s032 frame047scope06_end
  have h28 := stitchAt 28 4 frame047scope06_s028 h32
  have h24 := stitchAt 24 4 frame047scope06_s024 h28
  have h20 := stitchAt 20 4 frame047scope06_s020 h24
  have h16 := stitchAt 16 4 frame047scope06_s016 h20
  have h12 := stitchAt 12 4 frame047scope06_s012 h16
  have h8 := stitchAt 8 4 frame047scope06_s008 h12
  have h4 := stitchAt 4 4 frame047scope06_s004 h8
  have h0 := stitchAt 0 4 frame047scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch06 : batch06.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope06

private abbrev frame047test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame97 (fun z => List.lookup (guideCode z) guide047)
    (batch07.stop,F)

private theorem frame047scope07_s000 : ((fits07.drop 0).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s004 : ((fits07.drop 4).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s008 : ((fits07.drop 8).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s012 : ((fits07.drop 12).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s016 : ((fits07.drop 16).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s020 : ((fits07.drop 20).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s024 : ((fits07.drop 24).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s028 : ((fits07.drop 28).take 4).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_s032 : ((fits07.drop 32).take 3).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07_end : (fits07.drop 35).all frame047test07=true := by
  decide +kernel

private theorem frame047scope07 : fits07.all frame047test07=true := by
  have h32 := stitchAt 32 3 frame047scope07_s032 frame047scope07_end
  have h28 := stitchAt 28 4 frame047scope07_s028 h32
  have h24 := stitchAt 24 4 frame047scope07_s024 h28
  have h20 := stitchAt 20 4 frame047scope07_s020 h24
  have h16 := stitchAt 16 4 frame047scope07_s016 h20
  have h12 := stitchAt 12 4 frame047scope07_s012 h16
  have h8 := stitchAt 8 4 frame047scope07_s008 h12
  have h4 := stitchAt 4 4 frame047scope07_s004 h8
  have h0 := stitchAt 0 4 frame047scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame047batch07 : batch07.pickTest original frame97=true :=
  FitBatch.pickTest_of_scoped scoped047 frame047scope07

private theorem frameBatches047 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame97)=true := by
  simp only [List.all_cons,List.all_nil,frame047batch00,frame047batch01,frame047batch02,frame047batch03,frame047batch04,frame047batch05,frame047batch06,frame047batch07,Bool.and_self]

theorem frameOK047 : frameRankTest original useStop frame97=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches047


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
