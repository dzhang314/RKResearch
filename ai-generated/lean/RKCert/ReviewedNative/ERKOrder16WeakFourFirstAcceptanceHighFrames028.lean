module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK056 : stripTest frame116=true := by decide +kernel

theorem spanOK056 : checkChain 1766 1765 [frame116.span]=true := by decide +kernel

private theorem guideAt056 : List.lookup frame116.span.1 guideTable=some guide056 := by
  decide +kernel

private theorem scoped056 : original.guide frame116.span.1 =
    (fun z => List.lookup (guideCode z) guide056) := by
  funext z
  change (List.lookup frame116.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide056
  simp only [guideAt056,Option.bind_some]

private abbrev frame056test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch00.stop,F)

private theorem frame056scope00_s000 : ((fits00.drop 0).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s004 : ((fits00.drop 4).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s008 : ((fits00.drop 8).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s012 : ((fits00.drop 12).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s016 : ((fits00.drop 16).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s020 : ((fits00.drop 20).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s024 : ((fits00.drop 24).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s028 : ((fits00.drop 28).take 4).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_s032 : ((fits00.drop 32).take 3).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00_end : (fits00.drop 35).all frame056test00=true := by
  decide +kernel

private theorem frame056scope00 : fits00.all frame056test00=true := by
  have h32 := stitchAt 32 3 frame056scope00_s032 frame056scope00_end
  have h28 := stitchAt 28 4 frame056scope00_s028 h32
  have h24 := stitchAt 24 4 frame056scope00_s024 h28
  have h20 := stitchAt 20 4 frame056scope00_s020 h24
  have h16 := stitchAt 16 4 frame056scope00_s016 h20
  have h12 := stitchAt 12 4 frame056scope00_s012 h16
  have h8 := stitchAt 8 4 frame056scope00_s008 h12
  have h4 := stitchAt 4 4 frame056scope00_s004 h8
  have h0 := stitchAt 0 4 frame056scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch00 : batch00.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope00

private abbrev frame056test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch01.stop,F)

private theorem frame056scope01_s000 : ((fits01.drop 0).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s004 : ((fits01.drop 4).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s008 : ((fits01.drop 8).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s012 : ((fits01.drop 12).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s016 : ((fits01.drop 16).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s020 : ((fits01.drop 20).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s024 : ((fits01.drop 24).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s028 : ((fits01.drop 28).take 4).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_s032 : ((fits01.drop 32).take 3).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01_end : (fits01.drop 35).all frame056test01=true := by
  decide +kernel

private theorem frame056scope01 : fits01.all frame056test01=true := by
  have h32 := stitchAt 32 3 frame056scope01_s032 frame056scope01_end
  have h28 := stitchAt 28 4 frame056scope01_s028 h32
  have h24 := stitchAt 24 4 frame056scope01_s024 h28
  have h20 := stitchAt 20 4 frame056scope01_s020 h24
  have h16 := stitchAt 16 4 frame056scope01_s016 h20
  have h12 := stitchAt 12 4 frame056scope01_s012 h16
  have h8 := stitchAt 8 4 frame056scope01_s008 h12
  have h4 := stitchAt 4 4 frame056scope01_s004 h8
  have h0 := stitchAt 0 4 frame056scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch01 : batch01.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope01

private abbrev frame056test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch02.stop,F)

private theorem frame056scope02_s000 : ((fits02.drop 0).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s004 : ((fits02.drop 4).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s008 : ((fits02.drop 8).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s012 : ((fits02.drop 12).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s016 : ((fits02.drop 16).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s020 : ((fits02.drop 20).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s024 : ((fits02.drop 24).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s028 : ((fits02.drop 28).take 4).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_s032 : ((fits02.drop 32).take 3).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02_end : (fits02.drop 35).all frame056test02=true := by
  decide +kernel

private theorem frame056scope02 : fits02.all frame056test02=true := by
  have h32 := stitchAt 32 3 frame056scope02_s032 frame056scope02_end
  have h28 := stitchAt 28 4 frame056scope02_s028 h32
  have h24 := stitchAt 24 4 frame056scope02_s024 h28
  have h20 := stitchAt 20 4 frame056scope02_s020 h24
  have h16 := stitchAt 16 4 frame056scope02_s016 h20
  have h12 := stitchAt 12 4 frame056scope02_s012 h16
  have h8 := stitchAt 8 4 frame056scope02_s008 h12
  have h4 := stitchAt 4 4 frame056scope02_s004 h8
  have h0 := stitchAt 0 4 frame056scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch02 : batch02.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope02

private abbrev frame056test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch03.stop,F)

private theorem frame056scope03_s000 : ((fits03.drop 0).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s004 : ((fits03.drop 4).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s008 : ((fits03.drop 8).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s012 : ((fits03.drop 12).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s016 : ((fits03.drop 16).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s020 : ((fits03.drop 20).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s024 : ((fits03.drop 24).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s028 : ((fits03.drop 28).take 4).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_s032 : ((fits03.drop 32).take 3).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03_end : (fits03.drop 35).all frame056test03=true := by
  decide +kernel

private theorem frame056scope03 : fits03.all frame056test03=true := by
  have h32 := stitchAt 32 3 frame056scope03_s032 frame056scope03_end
  have h28 := stitchAt 28 4 frame056scope03_s028 h32
  have h24 := stitchAt 24 4 frame056scope03_s024 h28
  have h20 := stitchAt 20 4 frame056scope03_s020 h24
  have h16 := stitchAt 16 4 frame056scope03_s016 h20
  have h12 := stitchAt 12 4 frame056scope03_s012 h16
  have h8 := stitchAt 8 4 frame056scope03_s008 h12
  have h4 := stitchAt 4 4 frame056scope03_s004 h8
  have h0 := stitchAt 0 4 frame056scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch03 : batch03.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope03

private abbrev frame056test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch04.stop,F)

private theorem frame056scope04_s000 : ((fits04.drop 0).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s004 : ((fits04.drop 4).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s008 : ((fits04.drop 8).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s012 : ((fits04.drop 12).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s016 : ((fits04.drop 16).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s020 : ((fits04.drop 20).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s024 : ((fits04.drop 24).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s028 : ((fits04.drop 28).take 4).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_s032 : ((fits04.drop 32).take 3).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04_end : (fits04.drop 35).all frame056test04=true := by
  decide +kernel

private theorem frame056scope04 : fits04.all frame056test04=true := by
  have h32 := stitchAt 32 3 frame056scope04_s032 frame056scope04_end
  have h28 := stitchAt 28 4 frame056scope04_s028 h32
  have h24 := stitchAt 24 4 frame056scope04_s024 h28
  have h20 := stitchAt 20 4 frame056scope04_s020 h24
  have h16 := stitchAt 16 4 frame056scope04_s016 h20
  have h12 := stitchAt 12 4 frame056scope04_s012 h16
  have h8 := stitchAt 8 4 frame056scope04_s008 h12
  have h4 := stitchAt 4 4 frame056scope04_s004 h8
  have h0 := stitchAt 0 4 frame056scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch04 : batch04.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope04

private abbrev frame056test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch05.stop,F)

private theorem frame056scope05_s000 : ((fits05.drop 0).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s004 : ((fits05.drop 4).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s008 : ((fits05.drop 8).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s012 : ((fits05.drop 12).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s016 : ((fits05.drop 16).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s020 : ((fits05.drop 20).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s024 : ((fits05.drop 24).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s028 : ((fits05.drop 28).take 4).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_s032 : ((fits05.drop 32).take 3).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05_end : (fits05.drop 35).all frame056test05=true := by
  decide +kernel

private theorem frame056scope05 : fits05.all frame056test05=true := by
  have h32 := stitchAt 32 3 frame056scope05_s032 frame056scope05_end
  have h28 := stitchAt 28 4 frame056scope05_s028 h32
  have h24 := stitchAt 24 4 frame056scope05_s024 h28
  have h20 := stitchAt 20 4 frame056scope05_s020 h24
  have h16 := stitchAt 16 4 frame056scope05_s016 h20
  have h12 := stitchAt 12 4 frame056scope05_s012 h16
  have h8 := stitchAt 8 4 frame056scope05_s008 h12
  have h4 := stitchAt 4 4 frame056scope05_s004 h8
  have h0 := stitchAt 0 4 frame056scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch05 : batch05.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope05

private abbrev frame056test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch06.stop,F)

private theorem frame056scope06_s000 : ((fits06.drop 0).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s004 : ((fits06.drop 4).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s008 : ((fits06.drop 8).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s012 : ((fits06.drop 12).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s016 : ((fits06.drop 16).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s020 : ((fits06.drop 20).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s024 : ((fits06.drop 24).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s028 : ((fits06.drop 28).take 4).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_s032 : ((fits06.drop 32).take 3).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06_end : (fits06.drop 35).all frame056test06=true := by
  decide +kernel

private theorem frame056scope06 : fits06.all frame056test06=true := by
  have h32 := stitchAt 32 3 frame056scope06_s032 frame056scope06_end
  have h28 := stitchAt 28 4 frame056scope06_s028 h32
  have h24 := stitchAt 24 4 frame056scope06_s024 h28
  have h20 := stitchAt 20 4 frame056scope06_s020 h24
  have h16 := stitchAt 16 4 frame056scope06_s016 h20
  have h12 := stitchAt 12 4 frame056scope06_s012 h16
  have h8 := stitchAt 8 4 frame056scope06_s008 h12
  have h4 := stitchAt 4 4 frame056scope06_s004 h8
  have h0 := stitchAt 0 4 frame056scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch06 : batch06.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope06

private abbrev frame056test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame116 (fun z => List.lookup (guideCode z) guide056)
    (batch07.stop,F)

private theorem frame056scope07_s000 : ((fits07.drop 0).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s004 : ((fits07.drop 4).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s008 : ((fits07.drop 8).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s012 : ((fits07.drop 12).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s016 : ((fits07.drop 16).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s020 : ((fits07.drop 20).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s024 : ((fits07.drop 24).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s028 : ((fits07.drop 28).take 4).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_s032 : ((fits07.drop 32).take 3).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07_end : (fits07.drop 35).all frame056test07=true := by
  decide +kernel

private theorem frame056scope07 : fits07.all frame056test07=true := by
  have h32 := stitchAt 32 3 frame056scope07_s032 frame056scope07_end
  have h28 := stitchAt 28 4 frame056scope07_s028 h32
  have h24 := stitchAt 24 4 frame056scope07_s024 h28
  have h20 := stitchAt 20 4 frame056scope07_s020 h24
  have h16 := stitchAt 16 4 frame056scope07_s016 h20
  have h12 := stitchAt 12 4 frame056scope07_s012 h16
  have h8 := stitchAt 8 4 frame056scope07_s008 h12
  have h4 := stitchAt 4 4 frame056scope07_s004 h8
  have h0 := stitchAt 0 4 frame056scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame056batch07 : batch07.pickTest original frame116=true :=
  FitBatch.pickTest_of_scoped scoped056 frame056scope07

private theorem frameBatches056 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame116)=true := by
  simp only [List.all_cons,List.all_nil,frame056batch00,frame056batch01,frame056batch02,frame056batch03,frame056batch04,frame056batch05,frame056batch06,frame056batch07,Bool.and_self]

theorem frameOK056 : frameRankTest original useStop frame116=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches056

theorem stripOK057 : stripTest frame118=true := by decide +kernel

theorem spanOK057 : checkChain 1767 1766 [frame118.span]=true := by decide +kernel

private theorem guideAt057 : List.lookup frame118.span.1 guideTable=some guide057 := by
  decide +kernel

private theorem scoped057 : original.guide frame118.span.1 =
    (fun z => List.lookup (guideCode z) guide057) := by
  funext z
  change (List.lookup frame118.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide057
  simp only [guideAt057,Option.bind_some]

private abbrev frame057test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch00.stop,F)

private theorem frame057scope00_s000 : ((fits00.drop 0).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s004 : ((fits00.drop 4).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s008 : ((fits00.drop 8).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s012 : ((fits00.drop 12).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s016 : ((fits00.drop 16).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s020 : ((fits00.drop 20).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s024 : ((fits00.drop 24).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s028 : ((fits00.drop 28).take 4).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_s032 : ((fits00.drop 32).take 3).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00_end : (fits00.drop 35).all frame057test00=true := by
  decide +kernel

private theorem frame057scope00 : fits00.all frame057test00=true := by
  have h32 := stitchAt 32 3 frame057scope00_s032 frame057scope00_end
  have h28 := stitchAt 28 4 frame057scope00_s028 h32
  have h24 := stitchAt 24 4 frame057scope00_s024 h28
  have h20 := stitchAt 20 4 frame057scope00_s020 h24
  have h16 := stitchAt 16 4 frame057scope00_s016 h20
  have h12 := stitchAt 12 4 frame057scope00_s012 h16
  have h8 := stitchAt 8 4 frame057scope00_s008 h12
  have h4 := stitchAt 4 4 frame057scope00_s004 h8
  have h0 := stitchAt 0 4 frame057scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch00 : batch00.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope00

private abbrev frame057test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch01.stop,F)

private theorem frame057scope01_s000 : ((fits01.drop 0).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s004 : ((fits01.drop 4).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s008 : ((fits01.drop 8).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s012 : ((fits01.drop 12).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s016 : ((fits01.drop 16).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s020 : ((fits01.drop 20).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s024 : ((fits01.drop 24).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s028 : ((fits01.drop 28).take 4).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_s032 : ((fits01.drop 32).take 3).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01_end : (fits01.drop 35).all frame057test01=true := by
  decide +kernel

private theorem frame057scope01 : fits01.all frame057test01=true := by
  have h32 := stitchAt 32 3 frame057scope01_s032 frame057scope01_end
  have h28 := stitchAt 28 4 frame057scope01_s028 h32
  have h24 := stitchAt 24 4 frame057scope01_s024 h28
  have h20 := stitchAt 20 4 frame057scope01_s020 h24
  have h16 := stitchAt 16 4 frame057scope01_s016 h20
  have h12 := stitchAt 12 4 frame057scope01_s012 h16
  have h8 := stitchAt 8 4 frame057scope01_s008 h12
  have h4 := stitchAt 4 4 frame057scope01_s004 h8
  have h0 := stitchAt 0 4 frame057scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch01 : batch01.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope01

private abbrev frame057test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch02.stop,F)

private theorem frame057scope02_s000 : ((fits02.drop 0).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s004 : ((fits02.drop 4).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s008 : ((fits02.drop 8).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s012 : ((fits02.drop 12).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s016 : ((fits02.drop 16).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s020 : ((fits02.drop 20).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s024 : ((fits02.drop 24).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s028 : ((fits02.drop 28).take 4).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_s032 : ((fits02.drop 32).take 3).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02_end : (fits02.drop 35).all frame057test02=true := by
  decide +kernel

private theorem frame057scope02 : fits02.all frame057test02=true := by
  have h32 := stitchAt 32 3 frame057scope02_s032 frame057scope02_end
  have h28 := stitchAt 28 4 frame057scope02_s028 h32
  have h24 := stitchAt 24 4 frame057scope02_s024 h28
  have h20 := stitchAt 20 4 frame057scope02_s020 h24
  have h16 := stitchAt 16 4 frame057scope02_s016 h20
  have h12 := stitchAt 12 4 frame057scope02_s012 h16
  have h8 := stitchAt 8 4 frame057scope02_s008 h12
  have h4 := stitchAt 4 4 frame057scope02_s004 h8
  have h0 := stitchAt 0 4 frame057scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch02 : batch02.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope02

private abbrev frame057test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch03.stop,F)

private theorem frame057scope03_s000 : ((fits03.drop 0).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s004 : ((fits03.drop 4).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s008 : ((fits03.drop 8).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s012 : ((fits03.drop 12).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s016 : ((fits03.drop 16).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s020 : ((fits03.drop 20).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s024 : ((fits03.drop 24).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s028 : ((fits03.drop 28).take 4).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_s032 : ((fits03.drop 32).take 3).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03_end : (fits03.drop 35).all frame057test03=true := by
  decide +kernel

private theorem frame057scope03 : fits03.all frame057test03=true := by
  have h32 := stitchAt 32 3 frame057scope03_s032 frame057scope03_end
  have h28 := stitchAt 28 4 frame057scope03_s028 h32
  have h24 := stitchAt 24 4 frame057scope03_s024 h28
  have h20 := stitchAt 20 4 frame057scope03_s020 h24
  have h16 := stitchAt 16 4 frame057scope03_s016 h20
  have h12 := stitchAt 12 4 frame057scope03_s012 h16
  have h8 := stitchAt 8 4 frame057scope03_s008 h12
  have h4 := stitchAt 4 4 frame057scope03_s004 h8
  have h0 := stitchAt 0 4 frame057scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch03 : batch03.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope03

private abbrev frame057test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch04.stop,F)

private theorem frame057scope04_s000 : ((fits04.drop 0).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s004 : ((fits04.drop 4).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s008 : ((fits04.drop 8).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s012 : ((fits04.drop 12).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s016 : ((fits04.drop 16).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s020 : ((fits04.drop 20).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s024 : ((fits04.drop 24).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s028 : ((fits04.drop 28).take 4).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_s032 : ((fits04.drop 32).take 3).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04_end : (fits04.drop 35).all frame057test04=true := by
  decide +kernel

private theorem frame057scope04 : fits04.all frame057test04=true := by
  have h32 := stitchAt 32 3 frame057scope04_s032 frame057scope04_end
  have h28 := stitchAt 28 4 frame057scope04_s028 h32
  have h24 := stitchAt 24 4 frame057scope04_s024 h28
  have h20 := stitchAt 20 4 frame057scope04_s020 h24
  have h16 := stitchAt 16 4 frame057scope04_s016 h20
  have h12 := stitchAt 12 4 frame057scope04_s012 h16
  have h8 := stitchAt 8 4 frame057scope04_s008 h12
  have h4 := stitchAt 4 4 frame057scope04_s004 h8
  have h0 := stitchAt 0 4 frame057scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch04 : batch04.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope04

private abbrev frame057test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch05.stop,F)

private theorem frame057scope05_s000 : ((fits05.drop 0).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s004 : ((fits05.drop 4).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s008 : ((fits05.drop 8).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s012 : ((fits05.drop 12).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s016 : ((fits05.drop 16).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s020 : ((fits05.drop 20).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s024 : ((fits05.drop 24).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s028 : ((fits05.drop 28).take 4).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_s032 : ((fits05.drop 32).take 3).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05_end : (fits05.drop 35).all frame057test05=true := by
  decide +kernel

private theorem frame057scope05 : fits05.all frame057test05=true := by
  have h32 := stitchAt 32 3 frame057scope05_s032 frame057scope05_end
  have h28 := stitchAt 28 4 frame057scope05_s028 h32
  have h24 := stitchAt 24 4 frame057scope05_s024 h28
  have h20 := stitchAt 20 4 frame057scope05_s020 h24
  have h16 := stitchAt 16 4 frame057scope05_s016 h20
  have h12 := stitchAt 12 4 frame057scope05_s012 h16
  have h8 := stitchAt 8 4 frame057scope05_s008 h12
  have h4 := stitchAt 4 4 frame057scope05_s004 h8
  have h0 := stitchAt 0 4 frame057scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch05 : batch05.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope05

private abbrev frame057test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch06.stop,F)

private theorem frame057scope06_s000 : ((fits06.drop 0).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s004 : ((fits06.drop 4).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s008 : ((fits06.drop 8).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s012 : ((fits06.drop 12).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s016 : ((fits06.drop 16).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s020 : ((fits06.drop 20).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s024 : ((fits06.drop 24).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s028 : ((fits06.drop 28).take 4).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_s032 : ((fits06.drop 32).take 3).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06_end : (fits06.drop 35).all frame057test06=true := by
  decide +kernel

private theorem frame057scope06 : fits06.all frame057test06=true := by
  have h32 := stitchAt 32 3 frame057scope06_s032 frame057scope06_end
  have h28 := stitchAt 28 4 frame057scope06_s028 h32
  have h24 := stitchAt 24 4 frame057scope06_s024 h28
  have h20 := stitchAt 20 4 frame057scope06_s020 h24
  have h16 := stitchAt 16 4 frame057scope06_s016 h20
  have h12 := stitchAt 12 4 frame057scope06_s012 h16
  have h8 := stitchAt 8 4 frame057scope06_s008 h12
  have h4 := stitchAt 4 4 frame057scope06_s004 h8
  have h0 := stitchAt 0 4 frame057scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch06 : batch06.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope06

private abbrev frame057test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame118 (fun z => List.lookup (guideCode z) guide057)
    (batch07.stop,F)

private theorem frame057scope07_s000 : ((fits07.drop 0).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s004 : ((fits07.drop 4).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s008 : ((fits07.drop 8).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s012 : ((fits07.drop 12).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s016 : ((fits07.drop 16).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s020 : ((fits07.drop 20).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s024 : ((fits07.drop 24).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s028 : ((fits07.drop 28).take 4).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_s032 : ((fits07.drop 32).take 3).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07_end : (fits07.drop 35).all frame057test07=true := by
  decide +kernel

private theorem frame057scope07 : fits07.all frame057test07=true := by
  have h32 := stitchAt 32 3 frame057scope07_s032 frame057scope07_end
  have h28 := stitchAt 28 4 frame057scope07_s028 h32
  have h24 := stitchAt 24 4 frame057scope07_s024 h28
  have h20 := stitchAt 20 4 frame057scope07_s020 h24
  have h16 := stitchAt 16 4 frame057scope07_s016 h20
  have h12 := stitchAt 12 4 frame057scope07_s012 h16
  have h8 := stitchAt 8 4 frame057scope07_s008 h12
  have h4 := stitchAt 4 4 frame057scope07_s004 h8
  have h0 := stitchAt 0 4 frame057scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame057batch07 : batch07.pickTest original frame118=true :=
  FitBatch.pickTest_of_scoped scoped057 frame057scope07

private theorem frameBatches057 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame118)=true := by
  simp only [List.all_cons,List.all_nil,frame057batch00,frame057batch01,frame057batch02,frame057batch03,frame057batch04,frame057batch05,frame057batch06,frame057batch07,Bool.and_self]

theorem frameOK057 : frameRankTest original useStop frame118=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches057


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
