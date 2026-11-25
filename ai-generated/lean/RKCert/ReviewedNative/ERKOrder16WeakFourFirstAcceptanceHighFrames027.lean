module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK054 : stripTest frame112=true := by decide +kernel

theorem spanOK054 : checkChain 1764 1763 [frame112.span]=true := by decide +kernel

private theorem guideAt054 : List.lookup frame112.span.1 guideTable=some guide054 := by
  decide +kernel

private theorem scoped054 : original.guide frame112.span.1 =
    (fun z => List.lookup (guideCode z) guide054) := by
  funext z
  change (List.lookup frame112.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide054
  simp only [guideAt054,Option.bind_some]

private abbrev frame054test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch00.stop,F)

private theorem frame054scope00_s000 : ((fits00.drop 0).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s004 : ((fits00.drop 4).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s008 : ((fits00.drop 8).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s012 : ((fits00.drop 12).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s016 : ((fits00.drop 16).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s020 : ((fits00.drop 20).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s024 : ((fits00.drop 24).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s028 : ((fits00.drop 28).take 4).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_s032 : ((fits00.drop 32).take 3).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00_end : (fits00.drop 35).all frame054test00=true := by
  decide +kernel

private theorem frame054scope00 : fits00.all frame054test00=true := by
  have h32 := stitchAt 32 3 frame054scope00_s032 frame054scope00_end
  have h28 := stitchAt 28 4 frame054scope00_s028 h32
  have h24 := stitchAt 24 4 frame054scope00_s024 h28
  have h20 := stitchAt 20 4 frame054scope00_s020 h24
  have h16 := stitchAt 16 4 frame054scope00_s016 h20
  have h12 := stitchAt 12 4 frame054scope00_s012 h16
  have h8 := stitchAt 8 4 frame054scope00_s008 h12
  have h4 := stitchAt 4 4 frame054scope00_s004 h8
  have h0 := stitchAt 0 4 frame054scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch00 : batch00.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope00

private abbrev frame054test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch01.stop,F)

private theorem frame054scope01_s000 : ((fits01.drop 0).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s004 : ((fits01.drop 4).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s008 : ((fits01.drop 8).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s012 : ((fits01.drop 12).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s016 : ((fits01.drop 16).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s020 : ((fits01.drop 20).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s024 : ((fits01.drop 24).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s028 : ((fits01.drop 28).take 4).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_s032 : ((fits01.drop 32).take 3).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01_end : (fits01.drop 35).all frame054test01=true := by
  decide +kernel

private theorem frame054scope01 : fits01.all frame054test01=true := by
  have h32 := stitchAt 32 3 frame054scope01_s032 frame054scope01_end
  have h28 := stitchAt 28 4 frame054scope01_s028 h32
  have h24 := stitchAt 24 4 frame054scope01_s024 h28
  have h20 := stitchAt 20 4 frame054scope01_s020 h24
  have h16 := stitchAt 16 4 frame054scope01_s016 h20
  have h12 := stitchAt 12 4 frame054scope01_s012 h16
  have h8 := stitchAt 8 4 frame054scope01_s008 h12
  have h4 := stitchAt 4 4 frame054scope01_s004 h8
  have h0 := stitchAt 0 4 frame054scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch01 : batch01.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope01

private abbrev frame054test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch02.stop,F)

private theorem frame054scope02_s000 : ((fits02.drop 0).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s004 : ((fits02.drop 4).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s008 : ((fits02.drop 8).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s012 : ((fits02.drop 12).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s016 : ((fits02.drop 16).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s020 : ((fits02.drop 20).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s024 : ((fits02.drop 24).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s028 : ((fits02.drop 28).take 4).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_s032 : ((fits02.drop 32).take 3).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02_end : (fits02.drop 35).all frame054test02=true := by
  decide +kernel

private theorem frame054scope02 : fits02.all frame054test02=true := by
  have h32 := stitchAt 32 3 frame054scope02_s032 frame054scope02_end
  have h28 := stitchAt 28 4 frame054scope02_s028 h32
  have h24 := stitchAt 24 4 frame054scope02_s024 h28
  have h20 := stitchAt 20 4 frame054scope02_s020 h24
  have h16 := stitchAt 16 4 frame054scope02_s016 h20
  have h12 := stitchAt 12 4 frame054scope02_s012 h16
  have h8 := stitchAt 8 4 frame054scope02_s008 h12
  have h4 := stitchAt 4 4 frame054scope02_s004 h8
  have h0 := stitchAt 0 4 frame054scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch02 : batch02.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope02

private abbrev frame054test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch03.stop,F)

private theorem frame054scope03_s000 : ((fits03.drop 0).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s004 : ((fits03.drop 4).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s008 : ((fits03.drop 8).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s012 : ((fits03.drop 12).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s016 : ((fits03.drop 16).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s020 : ((fits03.drop 20).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s024 : ((fits03.drop 24).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s028 : ((fits03.drop 28).take 4).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_s032 : ((fits03.drop 32).take 3).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03_end : (fits03.drop 35).all frame054test03=true := by
  decide +kernel

private theorem frame054scope03 : fits03.all frame054test03=true := by
  have h32 := stitchAt 32 3 frame054scope03_s032 frame054scope03_end
  have h28 := stitchAt 28 4 frame054scope03_s028 h32
  have h24 := stitchAt 24 4 frame054scope03_s024 h28
  have h20 := stitchAt 20 4 frame054scope03_s020 h24
  have h16 := stitchAt 16 4 frame054scope03_s016 h20
  have h12 := stitchAt 12 4 frame054scope03_s012 h16
  have h8 := stitchAt 8 4 frame054scope03_s008 h12
  have h4 := stitchAt 4 4 frame054scope03_s004 h8
  have h0 := stitchAt 0 4 frame054scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch03 : batch03.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope03

private abbrev frame054test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch04.stop,F)

private theorem frame054scope04_s000 : ((fits04.drop 0).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s004 : ((fits04.drop 4).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s008 : ((fits04.drop 8).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s012 : ((fits04.drop 12).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s016 : ((fits04.drop 16).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s020 : ((fits04.drop 20).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s024 : ((fits04.drop 24).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s028 : ((fits04.drop 28).take 4).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_s032 : ((fits04.drop 32).take 3).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04_end : (fits04.drop 35).all frame054test04=true := by
  decide +kernel

private theorem frame054scope04 : fits04.all frame054test04=true := by
  have h32 := stitchAt 32 3 frame054scope04_s032 frame054scope04_end
  have h28 := stitchAt 28 4 frame054scope04_s028 h32
  have h24 := stitchAt 24 4 frame054scope04_s024 h28
  have h20 := stitchAt 20 4 frame054scope04_s020 h24
  have h16 := stitchAt 16 4 frame054scope04_s016 h20
  have h12 := stitchAt 12 4 frame054scope04_s012 h16
  have h8 := stitchAt 8 4 frame054scope04_s008 h12
  have h4 := stitchAt 4 4 frame054scope04_s004 h8
  have h0 := stitchAt 0 4 frame054scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch04 : batch04.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope04

private abbrev frame054test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch05.stop,F)

private theorem frame054scope05_s000 : ((fits05.drop 0).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s004 : ((fits05.drop 4).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s008 : ((fits05.drop 8).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s012 : ((fits05.drop 12).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s016 : ((fits05.drop 16).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s020 : ((fits05.drop 20).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s024 : ((fits05.drop 24).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s028 : ((fits05.drop 28).take 4).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_s032 : ((fits05.drop 32).take 3).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05_end : (fits05.drop 35).all frame054test05=true := by
  decide +kernel

private theorem frame054scope05 : fits05.all frame054test05=true := by
  have h32 := stitchAt 32 3 frame054scope05_s032 frame054scope05_end
  have h28 := stitchAt 28 4 frame054scope05_s028 h32
  have h24 := stitchAt 24 4 frame054scope05_s024 h28
  have h20 := stitchAt 20 4 frame054scope05_s020 h24
  have h16 := stitchAt 16 4 frame054scope05_s016 h20
  have h12 := stitchAt 12 4 frame054scope05_s012 h16
  have h8 := stitchAt 8 4 frame054scope05_s008 h12
  have h4 := stitchAt 4 4 frame054scope05_s004 h8
  have h0 := stitchAt 0 4 frame054scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch05 : batch05.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope05

private abbrev frame054test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch06.stop,F)

private theorem frame054scope06_s000 : ((fits06.drop 0).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s004 : ((fits06.drop 4).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s008 : ((fits06.drop 8).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s012 : ((fits06.drop 12).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s016 : ((fits06.drop 16).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s020 : ((fits06.drop 20).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s024 : ((fits06.drop 24).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s028 : ((fits06.drop 28).take 4).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_s032 : ((fits06.drop 32).take 3).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06_end : (fits06.drop 35).all frame054test06=true := by
  decide +kernel

private theorem frame054scope06 : fits06.all frame054test06=true := by
  have h32 := stitchAt 32 3 frame054scope06_s032 frame054scope06_end
  have h28 := stitchAt 28 4 frame054scope06_s028 h32
  have h24 := stitchAt 24 4 frame054scope06_s024 h28
  have h20 := stitchAt 20 4 frame054scope06_s020 h24
  have h16 := stitchAt 16 4 frame054scope06_s016 h20
  have h12 := stitchAt 12 4 frame054scope06_s012 h16
  have h8 := stitchAt 8 4 frame054scope06_s008 h12
  have h4 := stitchAt 4 4 frame054scope06_s004 h8
  have h0 := stitchAt 0 4 frame054scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch06 : batch06.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope06

private abbrev frame054test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame112 (fun z => List.lookup (guideCode z) guide054)
    (batch07.stop,F)

private theorem frame054scope07_s000 : ((fits07.drop 0).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s004 : ((fits07.drop 4).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s008 : ((fits07.drop 8).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s012 : ((fits07.drop 12).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s016 : ((fits07.drop 16).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s020 : ((fits07.drop 20).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s024 : ((fits07.drop 24).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s028 : ((fits07.drop 28).take 4).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_s032 : ((fits07.drop 32).take 3).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07_end : (fits07.drop 35).all frame054test07=true := by
  decide +kernel

private theorem frame054scope07 : fits07.all frame054test07=true := by
  have h32 := stitchAt 32 3 frame054scope07_s032 frame054scope07_end
  have h28 := stitchAt 28 4 frame054scope07_s028 h32
  have h24 := stitchAt 24 4 frame054scope07_s024 h28
  have h20 := stitchAt 20 4 frame054scope07_s020 h24
  have h16 := stitchAt 16 4 frame054scope07_s016 h20
  have h12 := stitchAt 12 4 frame054scope07_s012 h16
  have h8 := stitchAt 8 4 frame054scope07_s008 h12
  have h4 := stitchAt 4 4 frame054scope07_s004 h8
  have h0 := stitchAt 0 4 frame054scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame054batch07 : batch07.pickTest original frame112=true :=
  FitBatch.pickTest_of_scoped scoped054 frame054scope07

private theorem frameBatches054 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame112)=true := by
  simp only [List.all_cons,List.all_nil,frame054batch00,frame054batch01,frame054batch02,frame054batch03,frame054batch04,frame054batch05,frame054batch06,frame054batch07,Bool.and_self]

theorem frameOK054 : frameRankTest original useStop frame112=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches054

theorem stripOK055 : stripTest frame115=true := by decide +kernel

theorem spanOK055 : checkChain 1765 1764 [frame115.span]=true := by decide +kernel

private theorem guideAt055 : List.lookup frame115.span.1 guideTable=some guide055 := by
  decide +kernel

private theorem scoped055 : original.guide frame115.span.1 =
    (fun z => List.lookup (guideCode z) guide055) := by
  funext z
  change (List.lookup frame115.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide055
  simp only [guideAt055,Option.bind_some]

private abbrev frame055test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch00.stop,F)

private theorem frame055scope00_s000 : ((fits00.drop 0).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s004 : ((fits00.drop 4).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s008 : ((fits00.drop 8).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s012 : ((fits00.drop 12).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s016 : ((fits00.drop 16).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s020 : ((fits00.drop 20).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s024 : ((fits00.drop 24).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s028 : ((fits00.drop 28).take 4).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_s032 : ((fits00.drop 32).take 3).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00_end : (fits00.drop 35).all frame055test00=true := by
  decide +kernel

private theorem frame055scope00 : fits00.all frame055test00=true := by
  have h32 := stitchAt 32 3 frame055scope00_s032 frame055scope00_end
  have h28 := stitchAt 28 4 frame055scope00_s028 h32
  have h24 := stitchAt 24 4 frame055scope00_s024 h28
  have h20 := stitchAt 20 4 frame055scope00_s020 h24
  have h16 := stitchAt 16 4 frame055scope00_s016 h20
  have h12 := stitchAt 12 4 frame055scope00_s012 h16
  have h8 := stitchAt 8 4 frame055scope00_s008 h12
  have h4 := stitchAt 4 4 frame055scope00_s004 h8
  have h0 := stitchAt 0 4 frame055scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch00 : batch00.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope00

private abbrev frame055test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch01.stop,F)

private theorem frame055scope01_s000 : ((fits01.drop 0).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s004 : ((fits01.drop 4).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s008 : ((fits01.drop 8).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s012 : ((fits01.drop 12).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s016 : ((fits01.drop 16).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s020 : ((fits01.drop 20).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s024 : ((fits01.drop 24).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s028 : ((fits01.drop 28).take 4).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_s032 : ((fits01.drop 32).take 3).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01_end : (fits01.drop 35).all frame055test01=true := by
  decide +kernel

private theorem frame055scope01 : fits01.all frame055test01=true := by
  have h32 := stitchAt 32 3 frame055scope01_s032 frame055scope01_end
  have h28 := stitchAt 28 4 frame055scope01_s028 h32
  have h24 := stitchAt 24 4 frame055scope01_s024 h28
  have h20 := stitchAt 20 4 frame055scope01_s020 h24
  have h16 := stitchAt 16 4 frame055scope01_s016 h20
  have h12 := stitchAt 12 4 frame055scope01_s012 h16
  have h8 := stitchAt 8 4 frame055scope01_s008 h12
  have h4 := stitchAt 4 4 frame055scope01_s004 h8
  have h0 := stitchAt 0 4 frame055scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch01 : batch01.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope01

private abbrev frame055test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch02.stop,F)

private theorem frame055scope02_s000 : ((fits02.drop 0).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s004 : ((fits02.drop 4).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s008 : ((fits02.drop 8).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s012 : ((fits02.drop 12).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s016 : ((fits02.drop 16).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s020 : ((fits02.drop 20).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s024 : ((fits02.drop 24).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s028 : ((fits02.drop 28).take 4).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_s032 : ((fits02.drop 32).take 3).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02_end : (fits02.drop 35).all frame055test02=true := by
  decide +kernel

private theorem frame055scope02 : fits02.all frame055test02=true := by
  have h32 := stitchAt 32 3 frame055scope02_s032 frame055scope02_end
  have h28 := stitchAt 28 4 frame055scope02_s028 h32
  have h24 := stitchAt 24 4 frame055scope02_s024 h28
  have h20 := stitchAt 20 4 frame055scope02_s020 h24
  have h16 := stitchAt 16 4 frame055scope02_s016 h20
  have h12 := stitchAt 12 4 frame055scope02_s012 h16
  have h8 := stitchAt 8 4 frame055scope02_s008 h12
  have h4 := stitchAt 4 4 frame055scope02_s004 h8
  have h0 := stitchAt 0 4 frame055scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch02 : batch02.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope02

private abbrev frame055test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch03.stop,F)

private theorem frame055scope03_s000 : ((fits03.drop 0).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s004 : ((fits03.drop 4).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s008 : ((fits03.drop 8).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s012 : ((fits03.drop 12).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s016 : ((fits03.drop 16).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s020 : ((fits03.drop 20).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s024 : ((fits03.drop 24).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s028 : ((fits03.drop 28).take 4).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_s032 : ((fits03.drop 32).take 3).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03_end : (fits03.drop 35).all frame055test03=true := by
  decide +kernel

private theorem frame055scope03 : fits03.all frame055test03=true := by
  have h32 := stitchAt 32 3 frame055scope03_s032 frame055scope03_end
  have h28 := stitchAt 28 4 frame055scope03_s028 h32
  have h24 := stitchAt 24 4 frame055scope03_s024 h28
  have h20 := stitchAt 20 4 frame055scope03_s020 h24
  have h16 := stitchAt 16 4 frame055scope03_s016 h20
  have h12 := stitchAt 12 4 frame055scope03_s012 h16
  have h8 := stitchAt 8 4 frame055scope03_s008 h12
  have h4 := stitchAt 4 4 frame055scope03_s004 h8
  have h0 := stitchAt 0 4 frame055scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch03 : batch03.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope03

private abbrev frame055test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch04.stop,F)

private theorem frame055scope04_s000 : ((fits04.drop 0).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s004 : ((fits04.drop 4).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s008 : ((fits04.drop 8).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s012 : ((fits04.drop 12).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s016 : ((fits04.drop 16).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s020 : ((fits04.drop 20).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s024 : ((fits04.drop 24).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s028 : ((fits04.drop 28).take 4).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_s032 : ((fits04.drop 32).take 3).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04_end : (fits04.drop 35).all frame055test04=true := by
  decide +kernel

private theorem frame055scope04 : fits04.all frame055test04=true := by
  have h32 := stitchAt 32 3 frame055scope04_s032 frame055scope04_end
  have h28 := stitchAt 28 4 frame055scope04_s028 h32
  have h24 := stitchAt 24 4 frame055scope04_s024 h28
  have h20 := stitchAt 20 4 frame055scope04_s020 h24
  have h16 := stitchAt 16 4 frame055scope04_s016 h20
  have h12 := stitchAt 12 4 frame055scope04_s012 h16
  have h8 := stitchAt 8 4 frame055scope04_s008 h12
  have h4 := stitchAt 4 4 frame055scope04_s004 h8
  have h0 := stitchAt 0 4 frame055scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch04 : batch04.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope04

private abbrev frame055test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch05.stop,F)

private theorem frame055scope05_s000 : ((fits05.drop 0).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s004 : ((fits05.drop 4).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s008 : ((fits05.drop 8).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s012 : ((fits05.drop 12).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s016 : ((fits05.drop 16).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s020 : ((fits05.drop 20).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s024 : ((fits05.drop 24).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s028 : ((fits05.drop 28).take 4).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_s032 : ((fits05.drop 32).take 3).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05_end : (fits05.drop 35).all frame055test05=true := by
  decide +kernel

private theorem frame055scope05 : fits05.all frame055test05=true := by
  have h32 := stitchAt 32 3 frame055scope05_s032 frame055scope05_end
  have h28 := stitchAt 28 4 frame055scope05_s028 h32
  have h24 := stitchAt 24 4 frame055scope05_s024 h28
  have h20 := stitchAt 20 4 frame055scope05_s020 h24
  have h16 := stitchAt 16 4 frame055scope05_s016 h20
  have h12 := stitchAt 12 4 frame055scope05_s012 h16
  have h8 := stitchAt 8 4 frame055scope05_s008 h12
  have h4 := stitchAt 4 4 frame055scope05_s004 h8
  have h0 := stitchAt 0 4 frame055scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch05 : batch05.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope05

private abbrev frame055test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch06.stop,F)

private theorem frame055scope06_s000 : ((fits06.drop 0).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s004 : ((fits06.drop 4).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s008 : ((fits06.drop 8).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s012 : ((fits06.drop 12).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s016 : ((fits06.drop 16).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s020 : ((fits06.drop 20).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s024 : ((fits06.drop 24).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s028 : ((fits06.drop 28).take 4).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_s032 : ((fits06.drop 32).take 3).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06_end : (fits06.drop 35).all frame055test06=true := by
  decide +kernel

private theorem frame055scope06 : fits06.all frame055test06=true := by
  have h32 := stitchAt 32 3 frame055scope06_s032 frame055scope06_end
  have h28 := stitchAt 28 4 frame055scope06_s028 h32
  have h24 := stitchAt 24 4 frame055scope06_s024 h28
  have h20 := stitchAt 20 4 frame055scope06_s020 h24
  have h16 := stitchAt 16 4 frame055scope06_s016 h20
  have h12 := stitchAt 12 4 frame055scope06_s012 h16
  have h8 := stitchAt 8 4 frame055scope06_s008 h12
  have h4 := stitchAt 4 4 frame055scope06_s004 h8
  have h0 := stitchAt 0 4 frame055scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch06 : batch06.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope06

private abbrev frame055test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame115 (fun z => List.lookup (guideCode z) guide055)
    (batch07.stop,F)

private theorem frame055scope07_s000 : ((fits07.drop 0).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s004 : ((fits07.drop 4).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s008 : ((fits07.drop 8).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s012 : ((fits07.drop 12).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s016 : ((fits07.drop 16).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s020 : ((fits07.drop 20).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s024 : ((fits07.drop 24).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s028 : ((fits07.drop 28).take 4).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_s032 : ((fits07.drop 32).take 3).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07_end : (fits07.drop 35).all frame055test07=true := by
  decide +kernel

private theorem frame055scope07 : fits07.all frame055test07=true := by
  have h32 := stitchAt 32 3 frame055scope07_s032 frame055scope07_end
  have h28 := stitchAt 28 4 frame055scope07_s028 h32
  have h24 := stitchAt 24 4 frame055scope07_s024 h28
  have h20 := stitchAt 20 4 frame055scope07_s020 h24
  have h16 := stitchAt 16 4 frame055scope07_s016 h20
  have h12 := stitchAt 12 4 frame055scope07_s012 h16
  have h8 := stitchAt 8 4 frame055scope07_s008 h12
  have h4 := stitchAt 4 4 frame055scope07_s004 h8
  have h0 := stitchAt 0 4 frame055scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame055batch07 : batch07.pickTest original frame115=true :=
  FitBatch.pickTest_of_scoped scoped055 frame055scope07

private theorem frameBatches055 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame115)=true := by
  simp only [List.all_cons,List.all_nil,frame055batch00,frame055batch01,frame055batch02,frame055batch03,frame055batch04,frame055batch05,frame055batch06,frame055batch07,Bool.and_self]

theorem frameOK055 : frameRankTest original useStop frame115=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches055


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
