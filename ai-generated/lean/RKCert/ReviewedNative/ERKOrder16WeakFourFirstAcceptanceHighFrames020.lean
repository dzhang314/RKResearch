module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK040 : stripTest frame84=true := by decide +kernel

theorem spanOK040 : checkChain 1740 1736 [frame84.span]=true := by decide +kernel

private theorem guideAt040 : List.lookup frame84.span.1 guideTable=some guide040 := by
  decide +kernel

private theorem scoped040 : original.guide frame84.span.1 =
    (fun z => List.lookup (guideCode z) guide040) := by
  funext z
  change (List.lookup frame84.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide040
  simp only [guideAt040,Option.bind_some]

private abbrev frame040test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch00.stop,F)

private theorem frame040scope00_s000 : ((fits00.drop 0).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s004 : ((fits00.drop 4).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s008 : ((fits00.drop 8).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s012 : ((fits00.drop 12).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s016 : ((fits00.drop 16).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s020 : ((fits00.drop 20).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s024 : ((fits00.drop 24).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s028 : ((fits00.drop 28).take 4).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_s032 : ((fits00.drop 32).take 3).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00_end : (fits00.drop 35).all frame040test00=true := by
  decide +kernel

private theorem frame040scope00 : fits00.all frame040test00=true := by
  have h32 := stitchAt 32 3 frame040scope00_s032 frame040scope00_end
  have h28 := stitchAt 28 4 frame040scope00_s028 h32
  have h24 := stitchAt 24 4 frame040scope00_s024 h28
  have h20 := stitchAt 20 4 frame040scope00_s020 h24
  have h16 := stitchAt 16 4 frame040scope00_s016 h20
  have h12 := stitchAt 12 4 frame040scope00_s012 h16
  have h8 := stitchAt 8 4 frame040scope00_s008 h12
  have h4 := stitchAt 4 4 frame040scope00_s004 h8
  have h0 := stitchAt 0 4 frame040scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch00 : batch00.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope00

private abbrev frame040test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch01.stop,F)

private theorem frame040scope01_s000 : ((fits01.drop 0).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s004 : ((fits01.drop 4).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s008 : ((fits01.drop 8).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s012 : ((fits01.drop 12).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s016 : ((fits01.drop 16).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s020 : ((fits01.drop 20).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s024 : ((fits01.drop 24).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s028 : ((fits01.drop 28).take 4).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_s032 : ((fits01.drop 32).take 3).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01_end : (fits01.drop 35).all frame040test01=true := by
  decide +kernel

private theorem frame040scope01 : fits01.all frame040test01=true := by
  have h32 := stitchAt 32 3 frame040scope01_s032 frame040scope01_end
  have h28 := stitchAt 28 4 frame040scope01_s028 h32
  have h24 := stitchAt 24 4 frame040scope01_s024 h28
  have h20 := stitchAt 20 4 frame040scope01_s020 h24
  have h16 := stitchAt 16 4 frame040scope01_s016 h20
  have h12 := stitchAt 12 4 frame040scope01_s012 h16
  have h8 := stitchAt 8 4 frame040scope01_s008 h12
  have h4 := stitchAt 4 4 frame040scope01_s004 h8
  have h0 := stitchAt 0 4 frame040scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch01 : batch01.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope01

private abbrev frame040test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch02.stop,F)

private theorem frame040scope02_s000 : ((fits02.drop 0).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s004 : ((fits02.drop 4).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s008 : ((fits02.drop 8).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s012 : ((fits02.drop 12).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s016 : ((fits02.drop 16).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s020 : ((fits02.drop 20).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s024 : ((fits02.drop 24).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s028 : ((fits02.drop 28).take 4).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_s032 : ((fits02.drop 32).take 3).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02_end : (fits02.drop 35).all frame040test02=true := by
  decide +kernel

private theorem frame040scope02 : fits02.all frame040test02=true := by
  have h32 := stitchAt 32 3 frame040scope02_s032 frame040scope02_end
  have h28 := stitchAt 28 4 frame040scope02_s028 h32
  have h24 := stitchAt 24 4 frame040scope02_s024 h28
  have h20 := stitchAt 20 4 frame040scope02_s020 h24
  have h16 := stitchAt 16 4 frame040scope02_s016 h20
  have h12 := stitchAt 12 4 frame040scope02_s012 h16
  have h8 := stitchAt 8 4 frame040scope02_s008 h12
  have h4 := stitchAt 4 4 frame040scope02_s004 h8
  have h0 := stitchAt 0 4 frame040scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch02 : batch02.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope02

private abbrev frame040test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch03.stop,F)

private theorem frame040scope03_s000 : ((fits03.drop 0).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s004 : ((fits03.drop 4).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s008 : ((fits03.drop 8).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s012 : ((fits03.drop 12).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s016 : ((fits03.drop 16).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s020 : ((fits03.drop 20).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s024 : ((fits03.drop 24).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s028 : ((fits03.drop 28).take 4).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_s032 : ((fits03.drop 32).take 3).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03_end : (fits03.drop 35).all frame040test03=true := by
  decide +kernel

private theorem frame040scope03 : fits03.all frame040test03=true := by
  have h32 := stitchAt 32 3 frame040scope03_s032 frame040scope03_end
  have h28 := stitchAt 28 4 frame040scope03_s028 h32
  have h24 := stitchAt 24 4 frame040scope03_s024 h28
  have h20 := stitchAt 20 4 frame040scope03_s020 h24
  have h16 := stitchAt 16 4 frame040scope03_s016 h20
  have h12 := stitchAt 12 4 frame040scope03_s012 h16
  have h8 := stitchAt 8 4 frame040scope03_s008 h12
  have h4 := stitchAt 4 4 frame040scope03_s004 h8
  have h0 := stitchAt 0 4 frame040scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch03 : batch03.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope03

private abbrev frame040test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch04.stop,F)

private theorem frame040scope04_s000 : ((fits04.drop 0).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s004 : ((fits04.drop 4).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s008 : ((fits04.drop 8).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s012 : ((fits04.drop 12).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s016 : ((fits04.drop 16).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s020 : ((fits04.drop 20).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s024 : ((fits04.drop 24).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s028 : ((fits04.drop 28).take 4).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_s032 : ((fits04.drop 32).take 3).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04_end : (fits04.drop 35).all frame040test04=true := by
  decide +kernel

private theorem frame040scope04 : fits04.all frame040test04=true := by
  have h32 := stitchAt 32 3 frame040scope04_s032 frame040scope04_end
  have h28 := stitchAt 28 4 frame040scope04_s028 h32
  have h24 := stitchAt 24 4 frame040scope04_s024 h28
  have h20 := stitchAt 20 4 frame040scope04_s020 h24
  have h16 := stitchAt 16 4 frame040scope04_s016 h20
  have h12 := stitchAt 12 4 frame040scope04_s012 h16
  have h8 := stitchAt 8 4 frame040scope04_s008 h12
  have h4 := stitchAt 4 4 frame040scope04_s004 h8
  have h0 := stitchAt 0 4 frame040scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch04 : batch04.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope04

private abbrev frame040test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch05.stop,F)

private theorem frame040scope05_s000 : ((fits05.drop 0).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s004 : ((fits05.drop 4).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s008 : ((fits05.drop 8).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s012 : ((fits05.drop 12).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s016 : ((fits05.drop 16).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s020 : ((fits05.drop 20).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s024 : ((fits05.drop 24).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s028 : ((fits05.drop 28).take 4).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_s032 : ((fits05.drop 32).take 3).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05_end : (fits05.drop 35).all frame040test05=true := by
  decide +kernel

private theorem frame040scope05 : fits05.all frame040test05=true := by
  have h32 := stitchAt 32 3 frame040scope05_s032 frame040scope05_end
  have h28 := stitchAt 28 4 frame040scope05_s028 h32
  have h24 := stitchAt 24 4 frame040scope05_s024 h28
  have h20 := stitchAt 20 4 frame040scope05_s020 h24
  have h16 := stitchAt 16 4 frame040scope05_s016 h20
  have h12 := stitchAt 12 4 frame040scope05_s012 h16
  have h8 := stitchAt 8 4 frame040scope05_s008 h12
  have h4 := stitchAt 4 4 frame040scope05_s004 h8
  have h0 := stitchAt 0 4 frame040scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch05 : batch05.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope05

private abbrev frame040test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch06.stop,F)

private theorem frame040scope06_s000 : ((fits06.drop 0).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s004 : ((fits06.drop 4).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s008 : ((fits06.drop 8).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s012 : ((fits06.drop 12).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s016 : ((fits06.drop 16).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s020 : ((fits06.drop 20).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s024 : ((fits06.drop 24).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s028 : ((fits06.drop 28).take 4).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_s032 : ((fits06.drop 32).take 3).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06_end : (fits06.drop 35).all frame040test06=true := by
  decide +kernel

private theorem frame040scope06 : fits06.all frame040test06=true := by
  have h32 := stitchAt 32 3 frame040scope06_s032 frame040scope06_end
  have h28 := stitchAt 28 4 frame040scope06_s028 h32
  have h24 := stitchAt 24 4 frame040scope06_s024 h28
  have h20 := stitchAt 20 4 frame040scope06_s020 h24
  have h16 := stitchAt 16 4 frame040scope06_s016 h20
  have h12 := stitchAt 12 4 frame040scope06_s012 h16
  have h8 := stitchAt 8 4 frame040scope06_s008 h12
  have h4 := stitchAt 4 4 frame040scope06_s004 h8
  have h0 := stitchAt 0 4 frame040scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch06 : batch06.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope06

private abbrev frame040test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame84 (fun z => List.lookup (guideCode z) guide040)
    (batch07.stop,F)

private theorem frame040scope07_s000 : ((fits07.drop 0).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s004 : ((fits07.drop 4).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s008 : ((fits07.drop 8).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s012 : ((fits07.drop 12).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s016 : ((fits07.drop 16).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s020 : ((fits07.drop 20).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s024 : ((fits07.drop 24).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s028 : ((fits07.drop 28).take 4).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_s032 : ((fits07.drop 32).take 3).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07_end : (fits07.drop 35).all frame040test07=true := by
  decide +kernel

private theorem frame040scope07 : fits07.all frame040test07=true := by
  have h32 := stitchAt 32 3 frame040scope07_s032 frame040scope07_end
  have h28 := stitchAt 28 4 frame040scope07_s028 h32
  have h24 := stitchAt 24 4 frame040scope07_s024 h28
  have h20 := stitchAt 20 4 frame040scope07_s020 h24
  have h16 := stitchAt 16 4 frame040scope07_s016 h20
  have h12 := stitchAt 12 4 frame040scope07_s012 h16
  have h8 := stitchAt 8 4 frame040scope07_s008 h12
  have h4 := stitchAt 4 4 frame040scope07_s004 h8
  have h0 := stitchAt 0 4 frame040scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame040batch07 : batch07.pickTest original frame84=true :=
  FitBatch.pickTest_of_scoped scoped040 frame040scope07

private theorem frameBatches040 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame84)=true := by
  simp only [List.all_cons,List.all_nil,frame040batch00,frame040batch01,frame040batch02,frame040batch03,frame040batch04,frame040batch05,frame040batch06,frame040batch07,Bool.and_self]

theorem frameOK040 : frameRankTest original useStop frame84=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches040

theorem stripOK041 : stripTest frame85=true := by decide +kernel

theorem spanOK041 : checkChain 1744 1740 [frame85.span]=true := by decide +kernel

private theorem guideAt041 : List.lookup frame85.span.1 guideTable=some guide041 := by
  decide +kernel

private theorem scoped041 : original.guide frame85.span.1 =
    (fun z => List.lookup (guideCode z) guide041) := by
  funext z
  change (List.lookup frame85.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide041
  simp only [guideAt041,Option.bind_some]

private abbrev frame041test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch00.stop,F)

private theorem frame041scope00_s000 : ((fits00.drop 0).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s004 : ((fits00.drop 4).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s008 : ((fits00.drop 8).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s012 : ((fits00.drop 12).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s016 : ((fits00.drop 16).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s020 : ((fits00.drop 20).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s024 : ((fits00.drop 24).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s028 : ((fits00.drop 28).take 4).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_s032 : ((fits00.drop 32).take 3).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00_end : (fits00.drop 35).all frame041test00=true := by
  decide +kernel

private theorem frame041scope00 : fits00.all frame041test00=true := by
  have h32 := stitchAt 32 3 frame041scope00_s032 frame041scope00_end
  have h28 := stitchAt 28 4 frame041scope00_s028 h32
  have h24 := stitchAt 24 4 frame041scope00_s024 h28
  have h20 := stitchAt 20 4 frame041scope00_s020 h24
  have h16 := stitchAt 16 4 frame041scope00_s016 h20
  have h12 := stitchAt 12 4 frame041scope00_s012 h16
  have h8 := stitchAt 8 4 frame041scope00_s008 h12
  have h4 := stitchAt 4 4 frame041scope00_s004 h8
  have h0 := stitchAt 0 4 frame041scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch00 : batch00.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope00

private abbrev frame041test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch01.stop,F)

private theorem frame041scope01_s000 : ((fits01.drop 0).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s004 : ((fits01.drop 4).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s008 : ((fits01.drop 8).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s012 : ((fits01.drop 12).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s016 : ((fits01.drop 16).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s020 : ((fits01.drop 20).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s024 : ((fits01.drop 24).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s028 : ((fits01.drop 28).take 4).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_s032 : ((fits01.drop 32).take 3).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01_end : (fits01.drop 35).all frame041test01=true := by
  decide +kernel

private theorem frame041scope01 : fits01.all frame041test01=true := by
  have h32 := stitchAt 32 3 frame041scope01_s032 frame041scope01_end
  have h28 := stitchAt 28 4 frame041scope01_s028 h32
  have h24 := stitchAt 24 4 frame041scope01_s024 h28
  have h20 := stitchAt 20 4 frame041scope01_s020 h24
  have h16 := stitchAt 16 4 frame041scope01_s016 h20
  have h12 := stitchAt 12 4 frame041scope01_s012 h16
  have h8 := stitchAt 8 4 frame041scope01_s008 h12
  have h4 := stitchAt 4 4 frame041scope01_s004 h8
  have h0 := stitchAt 0 4 frame041scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch01 : batch01.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope01

private abbrev frame041test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch02.stop,F)

private theorem frame041scope02_s000 : ((fits02.drop 0).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s004 : ((fits02.drop 4).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s008 : ((fits02.drop 8).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s012 : ((fits02.drop 12).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s016 : ((fits02.drop 16).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s020 : ((fits02.drop 20).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s024 : ((fits02.drop 24).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s028 : ((fits02.drop 28).take 4).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_s032 : ((fits02.drop 32).take 3).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02_end : (fits02.drop 35).all frame041test02=true := by
  decide +kernel

private theorem frame041scope02 : fits02.all frame041test02=true := by
  have h32 := stitchAt 32 3 frame041scope02_s032 frame041scope02_end
  have h28 := stitchAt 28 4 frame041scope02_s028 h32
  have h24 := stitchAt 24 4 frame041scope02_s024 h28
  have h20 := stitchAt 20 4 frame041scope02_s020 h24
  have h16 := stitchAt 16 4 frame041scope02_s016 h20
  have h12 := stitchAt 12 4 frame041scope02_s012 h16
  have h8 := stitchAt 8 4 frame041scope02_s008 h12
  have h4 := stitchAt 4 4 frame041scope02_s004 h8
  have h0 := stitchAt 0 4 frame041scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch02 : batch02.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope02

private abbrev frame041test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch03.stop,F)

private theorem frame041scope03_s000 : ((fits03.drop 0).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s004 : ((fits03.drop 4).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s008 : ((fits03.drop 8).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s012 : ((fits03.drop 12).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s016 : ((fits03.drop 16).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s020 : ((fits03.drop 20).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s024 : ((fits03.drop 24).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s028 : ((fits03.drop 28).take 4).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_s032 : ((fits03.drop 32).take 3).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03_end : (fits03.drop 35).all frame041test03=true := by
  decide +kernel

private theorem frame041scope03 : fits03.all frame041test03=true := by
  have h32 := stitchAt 32 3 frame041scope03_s032 frame041scope03_end
  have h28 := stitchAt 28 4 frame041scope03_s028 h32
  have h24 := stitchAt 24 4 frame041scope03_s024 h28
  have h20 := stitchAt 20 4 frame041scope03_s020 h24
  have h16 := stitchAt 16 4 frame041scope03_s016 h20
  have h12 := stitchAt 12 4 frame041scope03_s012 h16
  have h8 := stitchAt 8 4 frame041scope03_s008 h12
  have h4 := stitchAt 4 4 frame041scope03_s004 h8
  have h0 := stitchAt 0 4 frame041scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch03 : batch03.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope03

private abbrev frame041test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch04.stop,F)

private theorem frame041scope04_s000 : ((fits04.drop 0).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s004 : ((fits04.drop 4).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s008 : ((fits04.drop 8).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s012 : ((fits04.drop 12).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s016 : ((fits04.drop 16).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s020 : ((fits04.drop 20).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s024 : ((fits04.drop 24).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s028 : ((fits04.drop 28).take 4).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_s032 : ((fits04.drop 32).take 3).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04_end : (fits04.drop 35).all frame041test04=true := by
  decide +kernel

private theorem frame041scope04 : fits04.all frame041test04=true := by
  have h32 := stitchAt 32 3 frame041scope04_s032 frame041scope04_end
  have h28 := stitchAt 28 4 frame041scope04_s028 h32
  have h24 := stitchAt 24 4 frame041scope04_s024 h28
  have h20 := stitchAt 20 4 frame041scope04_s020 h24
  have h16 := stitchAt 16 4 frame041scope04_s016 h20
  have h12 := stitchAt 12 4 frame041scope04_s012 h16
  have h8 := stitchAt 8 4 frame041scope04_s008 h12
  have h4 := stitchAt 4 4 frame041scope04_s004 h8
  have h0 := stitchAt 0 4 frame041scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch04 : batch04.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope04

private abbrev frame041test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch05.stop,F)

private theorem frame041scope05_s000 : ((fits05.drop 0).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s004 : ((fits05.drop 4).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s008 : ((fits05.drop 8).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s012 : ((fits05.drop 12).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s016 : ((fits05.drop 16).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s020 : ((fits05.drop 20).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s024 : ((fits05.drop 24).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s028 : ((fits05.drop 28).take 4).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_s032 : ((fits05.drop 32).take 3).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05_end : (fits05.drop 35).all frame041test05=true := by
  decide +kernel

private theorem frame041scope05 : fits05.all frame041test05=true := by
  have h32 := stitchAt 32 3 frame041scope05_s032 frame041scope05_end
  have h28 := stitchAt 28 4 frame041scope05_s028 h32
  have h24 := stitchAt 24 4 frame041scope05_s024 h28
  have h20 := stitchAt 20 4 frame041scope05_s020 h24
  have h16 := stitchAt 16 4 frame041scope05_s016 h20
  have h12 := stitchAt 12 4 frame041scope05_s012 h16
  have h8 := stitchAt 8 4 frame041scope05_s008 h12
  have h4 := stitchAt 4 4 frame041scope05_s004 h8
  have h0 := stitchAt 0 4 frame041scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch05 : batch05.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope05

private abbrev frame041test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch06.stop,F)

private theorem frame041scope06_s000 : ((fits06.drop 0).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s004 : ((fits06.drop 4).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s008 : ((fits06.drop 8).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s012 : ((fits06.drop 12).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s016 : ((fits06.drop 16).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s020 : ((fits06.drop 20).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s024 : ((fits06.drop 24).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s028 : ((fits06.drop 28).take 4).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_s032 : ((fits06.drop 32).take 3).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06_end : (fits06.drop 35).all frame041test06=true := by
  decide +kernel

private theorem frame041scope06 : fits06.all frame041test06=true := by
  have h32 := stitchAt 32 3 frame041scope06_s032 frame041scope06_end
  have h28 := stitchAt 28 4 frame041scope06_s028 h32
  have h24 := stitchAt 24 4 frame041scope06_s024 h28
  have h20 := stitchAt 20 4 frame041scope06_s020 h24
  have h16 := stitchAt 16 4 frame041scope06_s016 h20
  have h12 := stitchAt 12 4 frame041scope06_s012 h16
  have h8 := stitchAt 8 4 frame041scope06_s008 h12
  have h4 := stitchAt 4 4 frame041scope06_s004 h8
  have h0 := stitchAt 0 4 frame041scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch06 : batch06.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope06

private abbrev frame041test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame85 (fun z => List.lookup (guideCode z) guide041)
    (batch07.stop,F)

private theorem frame041scope07_s000 : ((fits07.drop 0).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s004 : ((fits07.drop 4).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s008 : ((fits07.drop 8).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s012 : ((fits07.drop 12).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s016 : ((fits07.drop 16).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s020 : ((fits07.drop 20).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s024 : ((fits07.drop 24).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s028 : ((fits07.drop 28).take 4).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_s032 : ((fits07.drop 32).take 3).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07_end : (fits07.drop 35).all frame041test07=true := by
  decide +kernel

private theorem frame041scope07 : fits07.all frame041test07=true := by
  have h32 := stitchAt 32 3 frame041scope07_s032 frame041scope07_end
  have h28 := stitchAt 28 4 frame041scope07_s028 h32
  have h24 := stitchAt 24 4 frame041scope07_s024 h28
  have h20 := stitchAt 20 4 frame041scope07_s020 h24
  have h16 := stitchAt 16 4 frame041scope07_s016 h20
  have h12 := stitchAt 12 4 frame041scope07_s012 h16
  have h8 := stitchAt 8 4 frame041scope07_s008 h12
  have h4 := stitchAt 4 4 frame041scope07_s004 h8
  have h0 := stitchAt 0 4 frame041scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame041batch07 : batch07.pickTest original frame85=true :=
  FitBatch.pickTest_of_scoped scoped041 frame041scope07

private theorem frameBatches041 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame85)=true := by
  simp only [List.all_cons,List.all_nil,frame041batch00,frame041batch01,frame041batch02,frame041batch03,frame041batch04,frame041batch05,frame041batch06,frame041batch07,Bool.and_self]

theorem frameOK041 : frameRankTest original useStop frame85=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches041


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
