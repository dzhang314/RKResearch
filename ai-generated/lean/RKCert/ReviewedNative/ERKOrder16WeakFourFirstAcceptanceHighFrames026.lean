module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK052 : stripTest frame109=true := by decide +kernel

theorem spanOK052 : checkChain 1762 1761 [frame109.span]=true := by decide +kernel

private theorem guideAt052 : List.lookup frame109.span.1 guideTable=some guide052 := by
  decide +kernel

private theorem scoped052 : original.guide frame109.span.1 =
    (fun z => List.lookup (guideCode z) guide052) := by
  funext z
  change (List.lookup frame109.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide052
  simp only [guideAt052,Option.bind_some]

private abbrev frame052test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch00.stop,F)

private theorem frame052scope00_s000 : ((fits00.drop 0).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s004 : ((fits00.drop 4).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s008 : ((fits00.drop 8).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s012 : ((fits00.drop 12).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s016 : ((fits00.drop 16).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s020 : ((fits00.drop 20).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s024 : ((fits00.drop 24).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s028 : ((fits00.drop 28).take 4).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_s032 : ((fits00.drop 32).take 3).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00_end : (fits00.drop 35).all frame052test00=true := by
  decide +kernel

private theorem frame052scope00 : fits00.all frame052test00=true := by
  have h32 := stitchAt 32 3 frame052scope00_s032 frame052scope00_end
  have h28 := stitchAt 28 4 frame052scope00_s028 h32
  have h24 := stitchAt 24 4 frame052scope00_s024 h28
  have h20 := stitchAt 20 4 frame052scope00_s020 h24
  have h16 := stitchAt 16 4 frame052scope00_s016 h20
  have h12 := stitchAt 12 4 frame052scope00_s012 h16
  have h8 := stitchAt 8 4 frame052scope00_s008 h12
  have h4 := stitchAt 4 4 frame052scope00_s004 h8
  have h0 := stitchAt 0 4 frame052scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch00 : batch00.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope00

private abbrev frame052test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch01.stop,F)

private theorem frame052scope01_s000 : ((fits01.drop 0).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s004 : ((fits01.drop 4).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s008 : ((fits01.drop 8).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s012 : ((fits01.drop 12).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s016 : ((fits01.drop 16).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s020 : ((fits01.drop 20).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s024 : ((fits01.drop 24).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s028 : ((fits01.drop 28).take 4).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_s032 : ((fits01.drop 32).take 3).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01_end : (fits01.drop 35).all frame052test01=true := by
  decide +kernel

private theorem frame052scope01 : fits01.all frame052test01=true := by
  have h32 := stitchAt 32 3 frame052scope01_s032 frame052scope01_end
  have h28 := stitchAt 28 4 frame052scope01_s028 h32
  have h24 := stitchAt 24 4 frame052scope01_s024 h28
  have h20 := stitchAt 20 4 frame052scope01_s020 h24
  have h16 := stitchAt 16 4 frame052scope01_s016 h20
  have h12 := stitchAt 12 4 frame052scope01_s012 h16
  have h8 := stitchAt 8 4 frame052scope01_s008 h12
  have h4 := stitchAt 4 4 frame052scope01_s004 h8
  have h0 := stitchAt 0 4 frame052scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch01 : batch01.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope01

private abbrev frame052test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch02.stop,F)

private theorem frame052scope02_s000 : ((fits02.drop 0).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s004 : ((fits02.drop 4).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s008 : ((fits02.drop 8).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s012 : ((fits02.drop 12).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s016 : ((fits02.drop 16).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s020 : ((fits02.drop 20).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s024 : ((fits02.drop 24).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s028 : ((fits02.drop 28).take 4).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_s032 : ((fits02.drop 32).take 3).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02_end : (fits02.drop 35).all frame052test02=true := by
  decide +kernel

private theorem frame052scope02 : fits02.all frame052test02=true := by
  have h32 := stitchAt 32 3 frame052scope02_s032 frame052scope02_end
  have h28 := stitchAt 28 4 frame052scope02_s028 h32
  have h24 := stitchAt 24 4 frame052scope02_s024 h28
  have h20 := stitchAt 20 4 frame052scope02_s020 h24
  have h16 := stitchAt 16 4 frame052scope02_s016 h20
  have h12 := stitchAt 12 4 frame052scope02_s012 h16
  have h8 := stitchAt 8 4 frame052scope02_s008 h12
  have h4 := stitchAt 4 4 frame052scope02_s004 h8
  have h0 := stitchAt 0 4 frame052scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch02 : batch02.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope02

private abbrev frame052test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch03.stop,F)

private theorem frame052scope03_s000 : ((fits03.drop 0).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s004 : ((fits03.drop 4).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s008 : ((fits03.drop 8).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s012 : ((fits03.drop 12).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s016 : ((fits03.drop 16).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s020 : ((fits03.drop 20).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s024 : ((fits03.drop 24).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s028 : ((fits03.drop 28).take 4).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_s032 : ((fits03.drop 32).take 3).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03_end : (fits03.drop 35).all frame052test03=true := by
  decide +kernel

private theorem frame052scope03 : fits03.all frame052test03=true := by
  have h32 := stitchAt 32 3 frame052scope03_s032 frame052scope03_end
  have h28 := stitchAt 28 4 frame052scope03_s028 h32
  have h24 := stitchAt 24 4 frame052scope03_s024 h28
  have h20 := stitchAt 20 4 frame052scope03_s020 h24
  have h16 := stitchAt 16 4 frame052scope03_s016 h20
  have h12 := stitchAt 12 4 frame052scope03_s012 h16
  have h8 := stitchAt 8 4 frame052scope03_s008 h12
  have h4 := stitchAt 4 4 frame052scope03_s004 h8
  have h0 := stitchAt 0 4 frame052scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch03 : batch03.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope03

private abbrev frame052test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch04.stop,F)

private theorem frame052scope04_s000 : ((fits04.drop 0).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s004 : ((fits04.drop 4).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s008 : ((fits04.drop 8).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s012 : ((fits04.drop 12).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s016 : ((fits04.drop 16).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s020 : ((fits04.drop 20).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s024 : ((fits04.drop 24).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s028 : ((fits04.drop 28).take 4).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_s032 : ((fits04.drop 32).take 3).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04_end : (fits04.drop 35).all frame052test04=true := by
  decide +kernel

private theorem frame052scope04 : fits04.all frame052test04=true := by
  have h32 := stitchAt 32 3 frame052scope04_s032 frame052scope04_end
  have h28 := stitchAt 28 4 frame052scope04_s028 h32
  have h24 := stitchAt 24 4 frame052scope04_s024 h28
  have h20 := stitchAt 20 4 frame052scope04_s020 h24
  have h16 := stitchAt 16 4 frame052scope04_s016 h20
  have h12 := stitchAt 12 4 frame052scope04_s012 h16
  have h8 := stitchAt 8 4 frame052scope04_s008 h12
  have h4 := stitchAt 4 4 frame052scope04_s004 h8
  have h0 := stitchAt 0 4 frame052scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch04 : batch04.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope04

private abbrev frame052test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch05.stop,F)

private theorem frame052scope05_s000 : ((fits05.drop 0).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s004 : ((fits05.drop 4).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s008 : ((fits05.drop 8).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s012 : ((fits05.drop 12).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s016 : ((fits05.drop 16).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s020 : ((fits05.drop 20).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s024 : ((fits05.drop 24).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s028 : ((fits05.drop 28).take 4).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_s032 : ((fits05.drop 32).take 3).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05_end : (fits05.drop 35).all frame052test05=true := by
  decide +kernel

private theorem frame052scope05 : fits05.all frame052test05=true := by
  have h32 := stitchAt 32 3 frame052scope05_s032 frame052scope05_end
  have h28 := stitchAt 28 4 frame052scope05_s028 h32
  have h24 := stitchAt 24 4 frame052scope05_s024 h28
  have h20 := stitchAt 20 4 frame052scope05_s020 h24
  have h16 := stitchAt 16 4 frame052scope05_s016 h20
  have h12 := stitchAt 12 4 frame052scope05_s012 h16
  have h8 := stitchAt 8 4 frame052scope05_s008 h12
  have h4 := stitchAt 4 4 frame052scope05_s004 h8
  have h0 := stitchAt 0 4 frame052scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch05 : batch05.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope05

private abbrev frame052test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch06.stop,F)

private theorem frame052scope06_s000 : ((fits06.drop 0).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s004 : ((fits06.drop 4).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s008 : ((fits06.drop 8).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s012 : ((fits06.drop 12).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s016 : ((fits06.drop 16).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s020 : ((fits06.drop 20).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s024 : ((fits06.drop 24).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s028 : ((fits06.drop 28).take 4).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_s032 : ((fits06.drop 32).take 3).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06_end : (fits06.drop 35).all frame052test06=true := by
  decide +kernel

private theorem frame052scope06 : fits06.all frame052test06=true := by
  have h32 := stitchAt 32 3 frame052scope06_s032 frame052scope06_end
  have h28 := stitchAt 28 4 frame052scope06_s028 h32
  have h24 := stitchAt 24 4 frame052scope06_s024 h28
  have h20 := stitchAt 20 4 frame052scope06_s020 h24
  have h16 := stitchAt 16 4 frame052scope06_s016 h20
  have h12 := stitchAt 12 4 frame052scope06_s012 h16
  have h8 := stitchAt 8 4 frame052scope06_s008 h12
  have h4 := stitchAt 4 4 frame052scope06_s004 h8
  have h0 := stitchAt 0 4 frame052scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch06 : batch06.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope06

private abbrev frame052test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame109 (fun z => List.lookup (guideCode z) guide052)
    (batch07.stop,F)

private theorem frame052scope07_s000 : ((fits07.drop 0).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s004 : ((fits07.drop 4).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s008 : ((fits07.drop 8).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s012 : ((fits07.drop 12).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s016 : ((fits07.drop 16).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s020 : ((fits07.drop 20).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s024 : ((fits07.drop 24).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s028 : ((fits07.drop 28).take 4).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_s032 : ((fits07.drop 32).take 3).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07_end : (fits07.drop 35).all frame052test07=true := by
  decide +kernel

private theorem frame052scope07 : fits07.all frame052test07=true := by
  have h32 := stitchAt 32 3 frame052scope07_s032 frame052scope07_end
  have h28 := stitchAt 28 4 frame052scope07_s028 h32
  have h24 := stitchAt 24 4 frame052scope07_s024 h28
  have h20 := stitchAt 20 4 frame052scope07_s020 h24
  have h16 := stitchAt 16 4 frame052scope07_s016 h20
  have h12 := stitchAt 12 4 frame052scope07_s012 h16
  have h8 := stitchAt 8 4 frame052scope07_s008 h12
  have h4 := stitchAt 4 4 frame052scope07_s004 h8
  have h0 := stitchAt 0 4 frame052scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame052batch07 : batch07.pickTest original frame109=true :=
  FitBatch.pickTest_of_scoped scoped052 frame052scope07

private theorem frameBatches052 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame109)=true := by
  simp only [List.all_cons,List.all_nil,frame052batch00,frame052batch01,frame052batch02,frame052batch03,frame052batch04,frame052batch05,frame052batch06,frame052batch07,Bool.and_self]

theorem frameOK052 : frameRankTest original useStop frame109=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches052

theorem stripOK053 : stripTest frame111=true := by decide +kernel

theorem spanOK053 : checkChain 1763 1762 [frame111.span]=true := by decide +kernel

private theorem guideAt053 : List.lookup frame111.span.1 guideTable=some guide053 := by
  decide +kernel

private theorem scoped053 : original.guide frame111.span.1 =
    (fun z => List.lookup (guideCode z) guide053) := by
  funext z
  change (List.lookup frame111.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide053
  simp only [guideAt053,Option.bind_some]

private abbrev frame053test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch00.stop,F)

private theorem frame053scope00_s000 : ((fits00.drop 0).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s004 : ((fits00.drop 4).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s008 : ((fits00.drop 8).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s012 : ((fits00.drop 12).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s016 : ((fits00.drop 16).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s020 : ((fits00.drop 20).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s024 : ((fits00.drop 24).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s028 : ((fits00.drop 28).take 4).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_s032 : ((fits00.drop 32).take 3).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00_end : (fits00.drop 35).all frame053test00=true := by
  decide +kernel

private theorem frame053scope00 : fits00.all frame053test00=true := by
  have h32 := stitchAt 32 3 frame053scope00_s032 frame053scope00_end
  have h28 := stitchAt 28 4 frame053scope00_s028 h32
  have h24 := stitchAt 24 4 frame053scope00_s024 h28
  have h20 := stitchAt 20 4 frame053scope00_s020 h24
  have h16 := stitchAt 16 4 frame053scope00_s016 h20
  have h12 := stitchAt 12 4 frame053scope00_s012 h16
  have h8 := stitchAt 8 4 frame053scope00_s008 h12
  have h4 := stitchAt 4 4 frame053scope00_s004 h8
  have h0 := stitchAt 0 4 frame053scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch00 : batch00.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope00

private abbrev frame053test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch01.stop,F)

private theorem frame053scope01_s000 : ((fits01.drop 0).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s004 : ((fits01.drop 4).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s008 : ((fits01.drop 8).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s012 : ((fits01.drop 12).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s016 : ((fits01.drop 16).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s020 : ((fits01.drop 20).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s024 : ((fits01.drop 24).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s028 : ((fits01.drop 28).take 4).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_s032 : ((fits01.drop 32).take 3).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01_end : (fits01.drop 35).all frame053test01=true := by
  decide +kernel

private theorem frame053scope01 : fits01.all frame053test01=true := by
  have h32 := stitchAt 32 3 frame053scope01_s032 frame053scope01_end
  have h28 := stitchAt 28 4 frame053scope01_s028 h32
  have h24 := stitchAt 24 4 frame053scope01_s024 h28
  have h20 := stitchAt 20 4 frame053scope01_s020 h24
  have h16 := stitchAt 16 4 frame053scope01_s016 h20
  have h12 := stitchAt 12 4 frame053scope01_s012 h16
  have h8 := stitchAt 8 4 frame053scope01_s008 h12
  have h4 := stitchAt 4 4 frame053scope01_s004 h8
  have h0 := stitchAt 0 4 frame053scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch01 : batch01.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope01

private abbrev frame053test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch02.stop,F)

private theorem frame053scope02_s000 : ((fits02.drop 0).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s004 : ((fits02.drop 4).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s008 : ((fits02.drop 8).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s012 : ((fits02.drop 12).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s016 : ((fits02.drop 16).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s020 : ((fits02.drop 20).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s024 : ((fits02.drop 24).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s028 : ((fits02.drop 28).take 4).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_s032 : ((fits02.drop 32).take 3).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02_end : (fits02.drop 35).all frame053test02=true := by
  decide +kernel

private theorem frame053scope02 : fits02.all frame053test02=true := by
  have h32 := stitchAt 32 3 frame053scope02_s032 frame053scope02_end
  have h28 := stitchAt 28 4 frame053scope02_s028 h32
  have h24 := stitchAt 24 4 frame053scope02_s024 h28
  have h20 := stitchAt 20 4 frame053scope02_s020 h24
  have h16 := stitchAt 16 4 frame053scope02_s016 h20
  have h12 := stitchAt 12 4 frame053scope02_s012 h16
  have h8 := stitchAt 8 4 frame053scope02_s008 h12
  have h4 := stitchAt 4 4 frame053scope02_s004 h8
  have h0 := stitchAt 0 4 frame053scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch02 : batch02.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope02

private abbrev frame053test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch03.stop,F)

private theorem frame053scope03_s000 : ((fits03.drop 0).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s004 : ((fits03.drop 4).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s008 : ((fits03.drop 8).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s012 : ((fits03.drop 12).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s016 : ((fits03.drop 16).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s020 : ((fits03.drop 20).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s024 : ((fits03.drop 24).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s028 : ((fits03.drop 28).take 4).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_s032 : ((fits03.drop 32).take 3).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03_end : (fits03.drop 35).all frame053test03=true := by
  decide +kernel

private theorem frame053scope03 : fits03.all frame053test03=true := by
  have h32 := stitchAt 32 3 frame053scope03_s032 frame053scope03_end
  have h28 := stitchAt 28 4 frame053scope03_s028 h32
  have h24 := stitchAt 24 4 frame053scope03_s024 h28
  have h20 := stitchAt 20 4 frame053scope03_s020 h24
  have h16 := stitchAt 16 4 frame053scope03_s016 h20
  have h12 := stitchAt 12 4 frame053scope03_s012 h16
  have h8 := stitchAt 8 4 frame053scope03_s008 h12
  have h4 := stitchAt 4 4 frame053scope03_s004 h8
  have h0 := stitchAt 0 4 frame053scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch03 : batch03.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope03

private abbrev frame053test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch04.stop,F)

private theorem frame053scope04_s000 : ((fits04.drop 0).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s004 : ((fits04.drop 4).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s008 : ((fits04.drop 8).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s012 : ((fits04.drop 12).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s016 : ((fits04.drop 16).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s020 : ((fits04.drop 20).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s024 : ((fits04.drop 24).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s028 : ((fits04.drop 28).take 4).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_s032 : ((fits04.drop 32).take 3).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04_end : (fits04.drop 35).all frame053test04=true := by
  decide +kernel

private theorem frame053scope04 : fits04.all frame053test04=true := by
  have h32 := stitchAt 32 3 frame053scope04_s032 frame053scope04_end
  have h28 := stitchAt 28 4 frame053scope04_s028 h32
  have h24 := stitchAt 24 4 frame053scope04_s024 h28
  have h20 := stitchAt 20 4 frame053scope04_s020 h24
  have h16 := stitchAt 16 4 frame053scope04_s016 h20
  have h12 := stitchAt 12 4 frame053scope04_s012 h16
  have h8 := stitchAt 8 4 frame053scope04_s008 h12
  have h4 := stitchAt 4 4 frame053scope04_s004 h8
  have h0 := stitchAt 0 4 frame053scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch04 : batch04.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope04

private abbrev frame053test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch05.stop,F)

private theorem frame053scope05_s000 : ((fits05.drop 0).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s004 : ((fits05.drop 4).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s008 : ((fits05.drop 8).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s012 : ((fits05.drop 12).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s016 : ((fits05.drop 16).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s020 : ((fits05.drop 20).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s024 : ((fits05.drop 24).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s028 : ((fits05.drop 28).take 4).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_s032 : ((fits05.drop 32).take 3).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05_end : (fits05.drop 35).all frame053test05=true := by
  decide +kernel

private theorem frame053scope05 : fits05.all frame053test05=true := by
  have h32 := stitchAt 32 3 frame053scope05_s032 frame053scope05_end
  have h28 := stitchAt 28 4 frame053scope05_s028 h32
  have h24 := stitchAt 24 4 frame053scope05_s024 h28
  have h20 := stitchAt 20 4 frame053scope05_s020 h24
  have h16 := stitchAt 16 4 frame053scope05_s016 h20
  have h12 := stitchAt 12 4 frame053scope05_s012 h16
  have h8 := stitchAt 8 4 frame053scope05_s008 h12
  have h4 := stitchAt 4 4 frame053scope05_s004 h8
  have h0 := stitchAt 0 4 frame053scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch05 : batch05.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope05

private abbrev frame053test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch06.stop,F)

private theorem frame053scope06_s000 : ((fits06.drop 0).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s004 : ((fits06.drop 4).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s008 : ((fits06.drop 8).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s012 : ((fits06.drop 12).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s016 : ((fits06.drop 16).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s020 : ((fits06.drop 20).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s024 : ((fits06.drop 24).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s028 : ((fits06.drop 28).take 4).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_s032 : ((fits06.drop 32).take 3).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06_end : (fits06.drop 35).all frame053test06=true := by
  decide +kernel

private theorem frame053scope06 : fits06.all frame053test06=true := by
  have h32 := stitchAt 32 3 frame053scope06_s032 frame053scope06_end
  have h28 := stitchAt 28 4 frame053scope06_s028 h32
  have h24 := stitchAt 24 4 frame053scope06_s024 h28
  have h20 := stitchAt 20 4 frame053scope06_s020 h24
  have h16 := stitchAt 16 4 frame053scope06_s016 h20
  have h12 := stitchAt 12 4 frame053scope06_s012 h16
  have h8 := stitchAt 8 4 frame053scope06_s008 h12
  have h4 := stitchAt 4 4 frame053scope06_s004 h8
  have h0 := stitchAt 0 4 frame053scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch06 : batch06.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope06

private abbrev frame053test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame111 (fun z => List.lookup (guideCode z) guide053)
    (batch07.stop,F)

private theorem frame053scope07_s000 : ((fits07.drop 0).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s004 : ((fits07.drop 4).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s008 : ((fits07.drop 8).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s012 : ((fits07.drop 12).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s016 : ((fits07.drop 16).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s020 : ((fits07.drop 20).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s024 : ((fits07.drop 24).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s028 : ((fits07.drop 28).take 4).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_s032 : ((fits07.drop 32).take 3).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07_end : (fits07.drop 35).all frame053test07=true := by
  decide +kernel

private theorem frame053scope07 : fits07.all frame053test07=true := by
  have h32 := stitchAt 32 3 frame053scope07_s032 frame053scope07_end
  have h28 := stitchAt 28 4 frame053scope07_s028 h32
  have h24 := stitchAt 24 4 frame053scope07_s024 h28
  have h20 := stitchAt 20 4 frame053scope07_s020 h24
  have h16 := stitchAt 16 4 frame053scope07_s016 h20
  have h12 := stitchAt 12 4 frame053scope07_s012 h16
  have h8 := stitchAt 8 4 frame053scope07_s008 h12
  have h4 := stitchAt 4 4 frame053scope07_s004 h8
  have h0 := stitchAt 0 4 frame053scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame053batch07 : batch07.pickTest original frame111=true :=
  FitBatch.pickTest_of_scoped scoped053 frame053scope07

private theorem frameBatches053 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame111)=true := by
  simp only [List.all_cons,List.all_nil,frame053batch00,frame053batch01,frame053batch02,frame053batch03,frame053batch04,frame053batch05,frame053batch06,frame053batch07,Bool.and_self]

theorem frameOK053 : frameRankTest original useStop frame111=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches053


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
