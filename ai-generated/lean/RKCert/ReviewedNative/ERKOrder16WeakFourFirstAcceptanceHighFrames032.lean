module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK064 : stripTest frame131=true := by decide +kernel

theorem spanOK064 : checkChain 1780 1778 [frame131.span]=true := by decide +kernel

private theorem guideAt064 : List.lookup frame131.span.1 guideTable=some guide064 := by
  decide +kernel

private theorem scoped064 : original.guide frame131.span.1 =
    (fun z => List.lookup (guideCode z) guide064) := by
  funext z
  change (List.lookup frame131.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide064
  simp only [guideAt064,Option.bind_some]

private abbrev frame064test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch00.stop,F)

private theorem frame064scope00_s000 : ((fits00.drop 0).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s004 : ((fits00.drop 4).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s008 : ((fits00.drop 8).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s012 : ((fits00.drop 12).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s016 : ((fits00.drop 16).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s020 : ((fits00.drop 20).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s024 : ((fits00.drop 24).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s028 : ((fits00.drop 28).take 4).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_s032 : ((fits00.drop 32).take 3).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00_end : (fits00.drop 35).all frame064test00=true := by
  decide +kernel

private theorem frame064scope00 : fits00.all frame064test00=true := by
  have h32 := stitchAt 32 3 frame064scope00_s032 frame064scope00_end
  have h28 := stitchAt 28 4 frame064scope00_s028 h32
  have h24 := stitchAt 24 4 frame064scope00_s024 h28
  have h20 := stitchAt 20 4 frame064scope00_s020 h24
  have h16 := stitchAt 16 4 frame064scope00_s016 h20
  have h12 := stitchAt 12 4 frame064scope00_s012 h16
  have h8 := stitchAt 8 4 frame064scope00_s008 h12
  have h4 := stitchAt 4 4 frame064scope00_s004 h8
  have h0 := stitchAt 0 4 frame064scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch00 : batch00.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope00

private abbrev frame064test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch01.stop,F)

private theorem frame064scope01_s000 : ((fits01.drop 0).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s004 : ((fits01.drop 4).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s008 : ((fits01.drop 8).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s012 : ((fits01.drop 12).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s016 : ((fits01.drop 16).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s020 : ((fits01.drop 20).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s024 : ((fits01.drop 24).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s028 : ((fits01.drop 28).take 4).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_s032 : ((fits01.drop 32).take 3).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01_end : (fits01.drop 35).all frame064test01=true := by
  decide +kernel

private theorem frame064scope01 : fits01.all frame064test01=true := by
  have h32 := stitchAt 32 3 frame064scope01_s032 frame064scope01_end
  have h28 := stitchAt 28 4 frame064scope01_s028 h32
  have h24 := stitchAt 24 4 frame064scope01_s024 h28
  have h20 := stitchAt 20 4 frame064scope01_s020 h24
  have h16 := stitchAt 16 4 frame064scope01_s016 h20
  have h12 := stitchAt 12 4 frame064scope01_s012 h16
  have h8 := stitchAt 8 4 frame064scope01_s008 h12
  have h4 := stitchAt 4 4 frame064scope01_s004 h8
  have h0 := stitchAt 0 4 frame064scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch01 : batch01.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope01

private abbrev frame064test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch02.stop,F)

private theorem frame064scope02_s000 : ((fits02.drop 0).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s004 : ((fits02.drop 4).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s008 : ((fits02.drop 8).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s012 : ((fits02.drop 12).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s016 : ((fits02.drop 16).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s020 : ((fits02.drop 20).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s024 : ((fits02.drop 24).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s028 : ((fits02.drop 28).take 4).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_s032 : ((fits02.drop 32).take 3).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02_end : (fits02.drop 35).all frame064test02=true := by
  decide +kernel

private theorem frame064scope02 : fits02.all frame064test02=true := by
  have h32 := stitchAt 32 3 frame064scope02_s032 frame064scope02_end
  have h28 := stitchAt 28 4 frame064scope02_s028 h32
  have h24 := stitchAt 24 4 frame064scope02_s024 h28
  have h20 := stitchAt 20 4 frame064scope02_s020 h24
  have h16 := stitchAt 16 4 frame064scope02_s016 h20
  have h12 := stitchAt 12 4 frame064scope02_s012 h16
  have h8 := stitchAt 8 4 frame064scope02_s008 h12
  have h4 := stitchAt 4 4 frame064scope02_s004 h8
  have h0 := stitchAt 0 4 frame064scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch02 : batch02.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope02

private abbrev frame064test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch03.stop,F)

private theorem frame064scope03_s000 : ((fits03.drop 0).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s004 : ((fits03.drop 4).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s008 : ((fits03.drop 8).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s012 : ((fits03.drop 12).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s016 : ((fits03.drop 16).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s020 : ((fits03.drop 20).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s024 : ((fits03.drop 24).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s028 : ((fits03.drop 28).take 4).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_s032 : ((fits03.drop 32).take 3).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03_end : (fits03.drop 35).all frame064test03=true := by
  decide +kernel

private theorem frame064scope03 : fits03.all frame064test03=true := by
  have h32 := stitchAt 32 3 frame064scope03_s032 frame064scope03_end
  have h28 := stitchAt 28 4 frame064scope03_s028 h32
  have h24 := stitchAt 24 4 frame064scope03_s024 h28
  have h20 := stitchAt 20 4 frame064scope03_s020 h24
  have h16 := stitchAt 16 4 frame064scope03_s016 h20
  have h12 := stitchAt 12 4 frame064scope03_s012 h16
  have h8 := stitchAt 8 4 frame064scope03_s008 h12
  have h4 := stitchAt 4 4 frame064scope03_s004 h8
  have h0 := stitchAt 0 4 frame064scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch03 : batch03.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope03

private abbrev frame064test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch04.stop,F)

private theorem frame064scope04_s000 : ((fits04.drop 0).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s004 : ((fits04.drop 4).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s008 : ((fits04.drop 8).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s012 : ((fits04.drop 12).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s016 : ((fits04.drop 16).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s020 : ((fits04.drop 20).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s024 : ((fits04.drop 24).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s028 : ((fits04.drop 28).take 4).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_s032 : ((fits04.drop 32).take 3).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04_end : (fits04.drop 35).all frame064test04=true := by
  decide +kernel

private theorem frame064scope04 : fits04.all frame064test04=true := by
  have h32 := stitchAt 32 3 frame064scope04_s032 frame064scope04_end
  have h28 := stitchAt 28 4 frame064scope04_s028 h32
  have h24 := stitchAt 24 4 frame064scope04_s024 h28
  have h20 := stitchAt 20 4 frame064scope04_s020 h24
  have h16 := stitchAt 16 4 frame064scope04_s016 h20
  have h12 := stitchAt 12 4 frame064scope04_s012 h16
  have h8 := stitchAt 8 4 frame064scope04_s008 h12
  have h4 := stitchAt 4 4 frame064scope04_s004 h8
  have h0 := stitchAt 0 4 frame064scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch04 : batch04.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope04

private abbrev frame064test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch05.stop,F)

private theorem frame064scope05_s000 : ((fits05.drop 0).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s004 : ((fits05.drop 4).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s008 : ((fits05.drop 8).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s012 : ((fits05.drop 12).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s016 : ((fits05.drop 16).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s020 : ((fits05.drop 20).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s024 : ((fits05.drop 24).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s028 : ((fits05.drop 28).take 4).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_s032 : ((fits05.drop 32).take 3).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05_end : (fits05.drop 35).all frame064test05=true := by
  decide +kernel

private theorem frame064scope05 : fits05.all frame064test05=true := by
  have h32 := stitchAt 32 3 frame064scope05_s032 frame064scope05_end
  have h28 := stitchAt 28 4 frame064scope05_s028 h32
  have h24 := stitchAt 24 4 frame064scope05_s024 h28
  have h20 := stitchAt 20 4 frame064scope05_s020 h24
  have h16 := stitchAt 16 4 frame064scope05_s016 h20
  have h12 := stitchAt 12 4 frame064scope05_s012 h16
  have h8 := stitchAt 8 4 frame064scope05_s008 h12
  have h4 := stitchAt 4 4 frame064scope05_s004 h8
  have h0 := stitchAt 0 4 frame064scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch05 : batch05.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope05

private abbrev frame064test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch06.stop,F)

private theorem frame064scope06_s000 : ((fits06.drop 0).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s004 : ((fits06.drop 4).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s008 : ((fits06.drop 8).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s012 : ((fits06.drop 12).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s016 : ((fits06.drop 16).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s020 : ((fits06.drop 20).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s024 : ((fits06.drop 24).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s028 : ((fits06.drop 28).take 4).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_s032 : ((fits06.drop 32).take 3).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06_end : (fits06.drop 35).all frame064test06=true := by
  decide +kernel

private theorem frame064scope06 : fits06.all frame064test06=true := by
  have h32 := stitchAt 32 3 frame064scope06_s032 frame064scope06_end
  have h28 := stitchAt 28 4 frame064scope06_s028 h32
  have h24 := stitchAt 24 4 frame064scope06_s024 h28
  have h20 := stitchAt 20 4 frame064scope06_s020 h24
  have h16 := stitchAt 16 4 frame064scope06_s016 h20
  have h12 := stitchAt 12 4 frame064scope06_s012 h16
  have h8 := stitchAt 8 4 frame064scope06_s008 h12
  have h4 := stitchAt 4 4 frame064scope06_s004 h8
  have h0 := stitchAt 0 4 frame064scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch06 : batch06.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope06

private abbrev frame064test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame131 (fun z => List.lookup (guideCode z) guide064)
    (batch07.stop,F)

private theorem frame064scope07_s000 : ((fits07.drop 0).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s004 : ((fits07.drop 4).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s008 : ((fits07.drop 8).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s012 : ((fits07.drop 12).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s016 : ((fits07.drop 16).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s020 : ((fits07.drop 20).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s024 : ((fits07.drop 24).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s028 : ((fits07.drop 28).take 4).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_s032 : ((fits07.drop 32).take 3).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07_end : (fits07.drop 35).all frame064test07=true := by
  decide +kernel

private theorem frame064scope07 : fits07.all frame064test07=true := by
  have h32 := stitchAt 32 3 frame064scope07_s032 frame064scope07_end
  have h28 := stitchAt 28 4 frame064scope07_s028 h32
  have h24 := stitchAt 24 4 frame064scope07_s024 h28
  have h20 := stitchAt 20 4 frame064scope07_s020 h24
  have h16 := stitchAt 16 4 frame064scope07_s016 h20
  have h12 := stitchAt 12 4 frame064scope07_s012 h16
  have h8 := stitchAt 8 4 frame064scope07_s008 h12
  have h4 := stitchAt 4 4 frame064scope07_s004 h8
  have h0 := stitchAt 0 4 frame064scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame064batch07 : batch07.pickTest original frame131=true :=
  FitBatch.pickTest_of_scoped scoped064 frame064scope07

private theorem frameBatches064 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame131)=true := by
  simp only [List.all_cons,List.all_nil,frame064batch00,frame064batch01,frame064batch02,frame064batch03,frame064batch04,frame064batch05,frame064batch06,frame064batch07,Bool.and_self]

theorem frameOK064 : frameRankTest original useStop frame131=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches064

theorem stripOK065 : stripTest frame132=true := by decide +kernel

theorem spanOK065 : checkChain 1784 1780 [frame132.span]=true := by decide +kernel

private theorem guideAt065 : List.lookup frame132.span.1 guideTable=some guide065 := by
  decide +kernel

private theorem scoped065 : original.guide frame132.span.1 =
    (fun z => List.lookup (guideCode z) guide065) := by
  funext z
  change (List.lookup frame132.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide065
  simp only [guideAt065,Option.bind_some]

private abbrev frame065test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch00.stop,F)

private theorem frame065scope00_s000 : ((fits00.drop 0).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s004 : ((fits00.drop 4).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s008 : ((fits00.drop 8).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s012 : ((fits00.drop 12).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s016 : ((fits00.drop 16).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s020 : ((fits00.drop 20).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s024 : ((fits00.drop 24).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s028 : ((fits00.drop 28).take 4).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_s032 : ((fits00.drop 32).take 3).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00_end : (fits00.drop 35).all frame065test00=true := by
  decide +kernel

private theorem frame065scope00 : fits00.all frame065test00=true := by
  have h32 := stitchAt 32 3 frame065scope00_s032 frame065scope00_end
  have h28 := stitchAt 28 4 frame065scope00_s028 h32
  have h24 := stitchAt 24 4 frame065scope00_s024 h28
  have h20 := stitchAt 20 4 frame065scope00_s020 h24
  have h16 := stitchAt 16 4 frame065scope00_s016 h20
  have h12 := stitchAt 12 4 frame065scope00_s012 h16
  have h8 := stitchAt 8 4 frame065scope00_s008 h12
  have h4 := stitchAt 4 4 frame065scope00_s004 h8
  have h0 := stitchAt 0 4 frame065scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch00 : batch00.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope00

private abbrev frame065test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch01.stop,F)

private theorem frame065scope01_s000 : ((fits01.drop 0).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s004 : ((fits01.drop 4).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s008 : ((fits01.drop 8).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s012 : ((fits01.drop 12).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s016 : ((fits01.drop 16).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s020 : ((fits01.drop 20).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s024 : ((fits01.drop 24).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s028 : ((fits01.drop 28).take 4).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_s032 : ((fits01.drop 32).take 3).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01_end : (fits01.drop 35).all frame065test01=true := by
  decide +kernel

private theorem frame065scope01 : fits01.all frame065test01=true := by
  have h32 := stitchAt 32 3 frame065scope01_s032 frame065scope01_end
  have h28 := stitchAt 28 4 frame065scope01_s028 h32
  have h24 := stitchAt 24 4 frame065scope01_s024 h28
  have h20 := stitchAt 20 4 frame065scope01_s020 h24
  have h16 := stitchAt 16 4 frame065scope01_s016 h20
  have h12 := stitchAt 12 4 frame065scope01_s012 h16
  have h8 := stitchAt 8 4 frame065scope01_s008 h12
  have h4 := stitchAt 4 4 frame065scope01_s004 h8
  have h0 := stitchAt 0 4 frame065scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch01 : batch01.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope01

private abbrev frame065test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch02.stop,F)

private theorem frame065scope02_s000 : ((fits02.drop 0).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s004 : ((fits02.drop 4).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s008 : ((fits02.drop 8).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s012 : ((fits02.drop 12).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s016 : ((fits02.drop 16).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s020 : ((fits02.drop 20).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s024 : ((fits02.drop 24).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s028 : ((fits02.drop 28).take 4).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_s032 : ((fits02.drop 32).take 3).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02_end : (fits02.drop 35).all frame065test02=true := by
  decide +kernel

private theorem frame065scope02 : fits02.all frame065test02=true := by
  have h32 := stitchAt 32 3 frame065scope02_s032 frame065scope02_end
  have h28 := stitchAt 28 4 frame065scope02_s028 h32
  have h24 := stitchAt 24 4 frame065scope02_s024 h28
  have h20 := stitchAt 20 4 frame065scope02_s020 h24
  have h16 := stitchAt 16 4 frame065scope02_s016 h20
  have h12 := stitchAt 12 4 frame065scope02_s012 h16
  have h8 := stitchAt 8 4 frame065scope02_s008 h12
  have h4 := stitchAt 4 4 frame065scope02_s004 h8
  have h0 := stitchAt 0 4 frame065scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch02 : batch02.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope02

private abbrev frame065test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch03.stop,F)

private theorem frame065scope03_s000 : ((fits03.drop 0).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s004 : ((fits03.drop 4).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s008 : ((fits03.drop 8).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s012 : ((fits03.drop 12).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s016 : ((fits03.drop 16).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s020 : ((fits03.drop 20).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s024 : ((fits03.drop 24).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s028 : ((fits03.drop 28).take 4).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_s032 : ((fits03.drop 32).take 3).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03_end : (fits03.drop 35).all frame065test03=true := by
  decide +kernel

private theorem frame065scope03 : fits03.all frame065test03=true := by
  have h32 := stitchAt 32 3 frame065scope03_s032 frame065scope03_end
  have h28 := stitchAt 28 4 frame065scope03_s028 h32
  have h24 := stitchAt 24 4 frame065scope03_s024 h28
  have h20 := stitchAt 20 4 frame065scope03_s020 h24
  have h16 := stitchAt 16 4 frame065scope03_s016 h20
  have h12 := stitchAt 12 4 frame065scope03_s012 h16
  have h8 := stitchAt 8 4 frame065scope03_s008 h12
  have h4 := stitchAt 4 4 frame065scope03_s004 h8
  have h0 := stitchAt 0 4 frame065scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch03 : batch03.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope03

private abbrev frame065test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch04.stop,F)

private theorem frame065scope04_s000 : ((fits04.drop 0).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s004 : ((fits04.drop 4).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s008 : ((fits04.drop 8).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s012 : ((fits04.drop 12).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s016 : ((fits04.drop 16).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s020 : ((fits04.drop 20).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s024 : ((fits04.drop 24).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s028 : ((fits04.drop 28).take 4).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_s032 : ((fits04.drop 32).take 3).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04_end : (fits04.drop 35).all frame065test04=true := by
  decide +kernel

private theorem frame065scope04 : fits04.all frame065test04=true := by
  have h32 := stitchAt 32 3 frame065scope04_s032 frame065scope04_end
  have h28 := stitchAt 28 4 frame065scope04_s028 h32
  have h24 := stitchAt 24 4 frame065scope04_s024 h28
  have h20 := stitchAt 20 4 frame065scope04_s020 h24
  have h16 := stitchAt 16 4 frame065scope04_s016 h20
  have h12 := stitchAt 12 4 frame065scope04_s012 h16
  have h8 := stitchAt 8 4 frame065scope04_s008 h12
  have h4 := stitchAt 4 4 frame065scope04_s004 h8
  have h0 := stitchAt 0 4 frame065scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch04 : batch04.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope04

private abbrev frame065test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch05.stop,F)

private theorem frame065scope05_s000 : ((fits05.drop 0).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s004 : ((fits05.drop 4).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s008 : ((fits05.drop 8).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s012 : ((fits05.drop 12).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s016 : ((fits05.drop 16).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s020 : ((fits05.drop 20).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s024 : ((fits05.drop 24).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s028 : ((fits05.drop 28).take 4).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_s032 : ((fits05.drop 32).take 3).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05_end : (fits05.drop 35).all frame065test05=true := by
  decide +kernel

private theorem frame065scope05 : fits05.all frame065test05=true := by
  have h32 := stitchAt 32 3 frame065scope05_s032 frame065scope05_end
  have h28 := stitchAt 28 4 frame065scope05_s028 h32
  have h24 := stitchAt 24 4 frame065scope05_s024 h28
  have h20 := stitchAt 20 4 frame065scope05_s020 h24
  have h16 := stitchAt 16 4 frame065scope05_s016 h20
  have h12 := stitchAt 12 4 frame065scope05_s012 h16
  have h8 := stitchAt 8 4 frame065scope05_s008 h12
  have h4 := stitchAt 4 4 frame065scope05_s004 h8
  have h0 := stitchAt 0 4 frame065scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch05 : batch05.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope05

private abbrev frame065test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch06.stop,F)

private theorem frame065scope06_s000 : ((fits06.drop 0).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s004 : ((fits06.drop 4).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s008 : ((fits06.drop 8).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s012 : ((fits06.drop 12).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s016 : ((fits06.drop 16).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s020 : ((fits06.drop 20).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s024 : ((fits06.drop 24).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s028 : ((fits06.drop 28).take 4).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_s032 : ((fits06.drop 32).take 3).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06_end : (fits06.drop 35).all frame065test06=true := by
  decide +kernel

private theorem frame065scope06 : fits06.all frame065test06=true := by
  have h32 := stitchAt 32 3 frame065scope06_s032 frame065scope06_end
  have h28 := stitchAt 28 4 frame065scope06_s028 h32
  have h24 := stitchAt 24 4 frame065scope06_s024 h28
  have h20 := stitchAt 20 4 frame065scope06_s020 h24
  have h16 := stitchAt 16 4 frame065scope06_s016 h20
  have h12 := stitchAt 12 4 frame065scope06_s012 h16
  have h8 := stitchAt 8 4 frame065scope06_s008 h12
  have h4 := stitchAt 4 4 frame065scope06_s004 h8
  have h0 := stitchAt 0 4 frame065scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch06 : batch06.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope06

private abbrev frame065test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame132 (fun z => List.lookup (guideCode z) guide065)
    (batch07.stop,F)

private theorem frame065scope07_s000 : ((fits07.drop 0).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s004 : ((fits07.drop 4).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s008 : ((fits07.drop 8).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s012 : ((fits07.drop 12).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s016 : ((fits07.drop 16).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s020 : ((fits07.drop 20).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s024 : ((fits07.drop 24).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s028 : ((fits07.drop 28).take 4).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_s032 : ((fits07.drop 32).take 3).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07_end : (fits07.drop 35).all frame065test07=true := by
  decide +kernel

private theorem frame065scope07 : fits07.all frame065test07=true := by
  have h32 := stitchAt 32 3 frame065scope07_s032 frame065scope07_end
  have h28 := stitchAt 28 4 frame065scope07_s028 h32
  have h24 := stitchAt 24 4 frame065scope07_s024 h28
  have h20 := stitchAt 20 4 frame065scope07_s020 h24
  have h16 := stitchAt 16 4 frame065scope07_s016 h20
  have h12 := stitchAt 12 4 frame065scope07_s012 h16
  have h8 := stitchAt 8 4 frame065scope07_s008 h12
  have h4 := stitchAt 4 4 frame065scope07_s004 h8
  have h0 := stitchAt 0 4 frame065scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame065batch07 : batch07.pickTest original frame132=true :=
  FitBatch.pickTest_of_scoped scoped065 frame065scope07

private theorem frameBatches065 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame132)=true := by
  simp only [List.all_cons,List.all_nil,frame065batch00,frame065batch01,frame065batch02,frame065batch03,frame065batch04,frame065batch05,frame065batch06,frame065batch07,Bool.and_self]

theorem frameOK065 : frameRankTest original useStop frame132=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches065


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
