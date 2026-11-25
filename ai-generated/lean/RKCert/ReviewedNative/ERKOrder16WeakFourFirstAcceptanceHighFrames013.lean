module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK026 : stripTest frame55=true := by decide +kernel

theorem spanOK026 : checkChain 1632 1624 [frame55.span]=true := by decide +kernel

private theorem guideAt026 : List.lookup frame55.span.1 guideTable=some guide026 := by
  decide +kernel

private theorem scoped026 : original.guide frame55.span.1 =
    (fun z => List.lookup (guideCode z) guide026) := by
  funext z
  change (List.lookup frame55.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide026
  simp only [guideAt026,Option.bind_some]

private abbrev frame026test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch00.stop,F)

private theorem frame026scope00_s000 : ((fits00.drop 0).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s004 : ((fits00.drop 4).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s008 : ((fits00.drop 8).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s012 : ((fits00.drop 12).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s016 : ((fits00.drop 16).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s020 : ((fits00.drop 20).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s024 : ((fits00.drop 24).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s028 : ((fits00.drop 28).take 4).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_s032 : ((fits00.drop 32).take 3).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00_end : (fits00.drop 35).all frame026test00=true := by
  decide +kernel

private theorem frame026scope00 : fits00.all frame026test00=true := by
  have h32 := stitchAt 32 3 frame026scope00_s032 frame026scope00_end
  have h28 := stitchAt 28 4 frame026scope00_s028 h32
  have h24 := stitchAt 24 4 frame026scope00_s024 h28
  have h20 := stitchAt 20 4 frame026scope00_s020 h24
  have h16 := stitchAt 16 4 frame026scope00_s016 h20
  have h12 := stitchAt 12 4 frame026scope00_s012 h16
  have h8 := stitchAt 8 4 frame026scope00_s008 h12
  have h4 := stitchAt 4 4 frame026scope00_s004 h8
  have h0 := stitchAt 0 4 frame026scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch00 : batch00.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope00

private abbrev frame026test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch01.stop,F)

private theorem frame026scope01_s000 : ((fits01.drop 0).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s004 : ((fits01.drop 4).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s008 : ((fits01.drop 8).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s012 : ((fits01.drop 12).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s016 : ((fits01.drop 16).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s020 : ((fits01.drop 20).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s024 : ((fits01.drop 24).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s028 : ((fits01.drop 28).take 4).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_s032 : ((fits01.drop 32).take 3).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01_end : (fits01.drop 35).all frame026test01=true := by
  decide +kernel

private theorem frame026scope01 : fits01.all frame026test01=true := by
  have h32 := stitchAt 32 3 frame026scope01_s032 frame026scope01_end
  have h28 := stitchAt 28 4 frame026scope01_s028 h32
  have h24 := stitchAt 24 4 frame026scope01_s024 h28
  have h20 := stitchAt 20 4 frame026scope01_s020 h24
  have h16 := stitchAt 16 4 frame026scope01_s016 h20
  have h12 := stitchAt 12 4 frame026scope01_s012 h16
  have h8 := stitchAt 8 4 frame026scope01_s008 h12
  have h4 := stitchAt 4 4 frame026scope01_s004 h8
  have h0 := stitchAt 0 4 frame026scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch01 : batch01.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope01

private abbrev frame026test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch02.stop,F)

private theorem frame026scope02_s000 : ((fits02.drop 0).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s004 : ((fits02.drop 4).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s008 : ((fits02.drop 8).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s012 : ((fits02.drop 12).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s016 : ((fits02.drop 16).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s020 : ((fits02.drop 20).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s024 : ((fits02.drop 24).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s028 : ((fits02.drop 28).take 4).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_s032 : ((fits02.drop 32).take 3).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02_end : (fits02.drop 35).all frame026test02=true := by
  decide +kernel

private theorem frame026scope02 : fits02.all frame026test02=true := by
  have h32 := stitchAt 32 3 frame026scope02_s032 frame026scope02_end
  have h28 := stitchAt 28 4 frame026scope02_s028 h32
  have h24 := stitchAt 24 4 frame026scope02_s024 h28
  have h20 := stitchAt 20 4 frame026scope02_s020 h24
  have h16 := stitchAt 16 4 frame026scope02_s016 h20
  have h12 := stitchAt 12 4 frame026scope02_s012 h16
  have h8 := stitchAt 8 4 frame026scope02_s008 h12
  have h4 := stitchAt 4 4 frame026scope02_s004 h8
  have h0 := stitchAt 0 4 frame026scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch02 : batch02.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope02

private abbrev frame026test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch03.stop,F)

private theorem frame026scope03_s000 : ((fits03.drop 0).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s004 : ((fits03.drop 4).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s008 : ((fits03.drop 8).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s012 : ((fits03.drop 12).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s016 : ((fits03.drop 16).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s020 : ((fits03.drop 20).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s024 : ((fits03.drop 24).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s028 : ((fits03.drop 28).take 4).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_s032 : ((fits03.drop 32).take 3).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03_end : (fits03.drop 35).all frame026test03=true := by
  decide +kernel

private theorem frame026scope03 : fits03.all frame026test03=true := by
  have h32 := stitchAt 32 3 frame026scope03_s032 frame026scope03_end
  have h28 := stitchAt 28 4 frame026scope03_s028 h32
  have h24 := stitchAt 24 4 frame026scope03_s024 h28
  have h20 := stitchAt 20 4 frame026scope03_s020 h24
  have h16 := stitchAt 16 4 frame026scope03_s016 h20
  have h12 := stitchAt 12 4 frame026scope03_s012 h16
  have h8 := stitchAt 8 4 frame026scope03_s008 h12
  have h4 := stitchAt 4 4 frame026scope03_s004 h8
  have h0 := stitchAt 0 4 frame026scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch03 : batch03.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope03

private abbrev frame026test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch04.stop,F)

private theorem frame026scope04_s000 : ((fits04.drop 0).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s004 : ((fits04.drop 4).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s008 : ((fits04.drop 8).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s012 : ((fits04.drop 12).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s016 : ((fits04.drop 16).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s020 : ((fits04.drop 20).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s024 : ((fits04.drop 24).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s028 : ((fits04.drop 28).take 4).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_s032 : ((fits04.drop 32).take 3).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04_end : (fits04.drop 35).all frame026test04=true := by
  decide +kernel

private theorem frame026scope04 : fits04.all frame026test04=true := by
  have h32 := stitchAt 32 3 frame026scope04_s032 frame026scope04_end
  have h28 := stitchAt 28 4 frame026scope04_s028 h32
  have h24 := stitchAt 24 4 frame026scope04_s024 h28
  have h20 := stitchAt 20 4 frame026scope04_s020 h24
  have h16 := stitchAt 16 4 frame026scope04_s016 h20
  have h12 := stitchAt 12 4 frame026scope04_s012 h16
  have h8 := stitchAt 8 4 frame026scope04_s008 h12
  have h4 := stitchAt 4 4 frame026scope04_s004 h8
  have h0 := stitchAt 0 4 frame026scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch04 : batch04.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope04

private abbrev frame026test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch05.stop,F)

private theorem frame026scope05_s000 : ((fits05.drop 0).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s004 : ((fits05.drop 4).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s008 : ((fits05.drop 8).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s012 : ((fits05.drop 12).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s016 : ((fits05.drop 16).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s020 : ((fits05.drop 20).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s024 : ((fits05.drop 24).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s028 : ((fits05.drop 28).take 4).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_s032 : ((fits05.drop 32).take 3).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05_end : (fits05.drop 35).all frame026test05=true := by
  decide +kernel

private theorem frame026scope05 : fits05.all frame026test05=true := by
  have h32 := stitchAt 32 3 frame026scope05_s032 frame026scope05_end
  have h28 := stitchAt 28 4 frame026scope05_s028 h32
  have h24 := stitchAt 24 4 frame026scope05_s024 h28
  have h20 := stitchAt 20 4 frame026scope05_s020 h24
  have h16 := stitchAt 16 4 frame026scope05_s016 h20
  have h12 := stitchAt 12 4 frame026scope05_s012 h16
  have h8 := stitchAt 8 4 frame026scope05_s008 h12
  have h4 := stitchAt 4 4 frame026scope05_s004 h8
  have h0 := stitchAt 0 4 frame026scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch05 : batch05.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope05

private abbrev frame026test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch06.stop,F)

private theorem frame026scope06_s000 : ((fits06.drop 0).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s004 : ((fits06.drop 4).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s008 : ((fits06.drop 8).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s012 : ((fits06.drop 12).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s016 : ((fits06.drop 16).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s020 : ((fits06.drop 20).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s024 : ((fits06.drop 24).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s028 : ((fits06.drop 28).take 4).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_s032 : ((fits06.drop 32).take 3).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06_end : (fits06.drop 35).all frame026test06=true := by
  decide +kernel

private theorem frame026scope06 : fits06.all frame026test06=true := by
  have h32 := stitchAt 32 3 frame026scope06_s032 frame026scope06_end
  have h28 := stitchAt 28 4 frame026scope06_s028 h32
  have h24 := stitchAt 24 4 frame026scope06_s024 h28
  have h20 := stitchAt 20 4 frame026scope06_s020 h24
  have h16 := stitchAt 16 4 frame026scope06_s016 h20
  have h12 := stitchAt 12 4 frame026scope06_s012 h16
  have h8 := stitchAt 8 4 frame026scope06_s008 h12
  have h4 := stitchAt 4 4 frame026scope06_s004 h8
  have h0 := stitchAt 0 4 frame026scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch06 : batch06.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope06

private abbrev frame026test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame55 (fun z => List.lookup (guideCode z) guide026)
    (batch07.stop,F)

private theorem frame026scope07_s000 : ((fits07.drop 0).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s004 : ((fits07.drop 4).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s008 : ((fits07.drop 8).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s012 : ((fits07.drop 12).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s016 : ((fits07.drop 16).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s020 : ((fits07.drop 20).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s024 : ((fits07.drop 24).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s028 : ((fits07.drop 28).take 4).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_s032 : ((fits07.drop 32).take 3).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07_end : (fits07.drop 35).all frame026test07=true := by
  decide +kernel

private theorem frame026scope07 : fits07.all frame026test07=true := by
  have h32 := stitchAt 32 3 frame026scope07_s032 frame026scope07_end
  have h28 := stitchAt 28 4 frame026scope07_s028 h32
  have h24 := stitchAt 24 4 frame026scope07_s024 h28
  have h20 := stitchAt 20 4 frame026scope07_s020 h24
  have h16 := stitchAt 16 4 frame026scope07_s016 h20
  have h12 := stitchAt 12 4 frame026scope07_s012 h16
  have h8 := stitchAt 8 4 frame026scope07_s008 h12
  have h4 := stitchAt 4 4 frame026scope07_s004 h8
  have h0 := stitchAt 0 4 frame026scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame026batch07 : batch07.pickTest original frame55=true :=
  FitBatch.pickTest_of_scoped scoped026 frame026scope07

private theorem frameBatches026 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame55)=true := by
  simp only [List.all_cons,List.all_nil,frame026batch00,frame026batch01,frame026batch02,frame026batch03,frame026batch04,frame026batch05,frame026batch06,frame026batch07,Bool.and_self]

theorem frameOK026 : frameRankTest original useStop frame55=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches026

theorem stripOK027 : stripTest frame58=true := by decide +kernel

theorem spanOK027 : checkChain 1640 1632 [frame58.span]=true := by decide +kernel

private theorem guideAt027 : List.lookup frame58.span.1 guideTable=some guide027 := by
  decide +kernel

private theorem scoped027 : original.guide frame58.span.1 =
    (fun z => List.lookup (guideCode z) guide027) := by
  funext z
  change (List.lookup frame58.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide027
  simp only [guideAt027,Option.bind_some]

private abbrev frame027test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch00.stop,F)

private theorem frame027scope00_s000 : ((fits00.drop 0).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s004 : ((fits00.drop 4).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s008 : ((fits00.drop 8).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s012 : ((fits00.drop 12).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s016 : ((fits00.drop 16).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s020 : ((fits00.drop 20).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s024 : ((fits00.drop 24).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s028 : ((fits00.drop 28).take 4).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_s032 : ((fits00.drop 32).take 3).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00_end : (fits00.drop 35).all frame027test00=true := by
  decide +kernel

private theorem frame027scope00 : fits00.all frame027test00=true := by
  have h32 := stitchAt 32 3 frame027scope00_s032 frame027scope00_end
  have h28 := stitchAt 28 4 frame027scope00_s028 h32
  have h24 := stitchAt 24 4 frame027scope00_s024 h28
  have h20 := stitchAt 20 4 frame027scope00_s020 h24
  have h16 := stitchAt 16 4 frame027scope00_s016 h20
  have h12 := stitchAt 12 4 frame027scope00_s012 h16
  have h8 := stitchAt 8 4 frame027scope00_s008 h12
  have h4 := stitchAt 4 4 frame027scope00_s004 h8
  have h0 := stitchAt 0 4 frame027scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch00 : batch00.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope00

private abbrev frame027test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch01.stop,F)

private theorem frame027scope01_s000 : ((fits01.drop 0).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s004 : ((fits01.drop 4).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s008 : ((fits01.drop 8).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s012 : ((fits01.drop 12).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s016 : ((fits01.drop 16).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s020 : ((fits01.drop 20).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s024 : ((fits01.drop 24).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s028 : ((fits01.drop 28).take 4).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_s032 : ((fits01.drop 32).take 3).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01_end : (fits01.drop 35).all frame027test01=true := by
  decide +kernel

private theorem frame027scope01 : fits01.all frame027test01=true := by
  have h32 := stitchAt 32 3 frame027scope01_s032 frame027scope01_end
  have h28 := stitchAt 28 4 frame027scope01_s028 h32
  have h24 := stitchAt 24 4 frame027scope01_s024 h28
  have h20 := stitchAt 20 4 frame027scope01_s020 h24
  have h16 := stitchAt 16 4 frame027scope01_s016 h20
  have h12 := stitchAt 12 4 frame027scope01_s012 h16
  have h8 := stitchAt 8 4 frame027scope01_s008 h12
  have h4 := stitchAt 4 4 frame027scope01_s004 h8
  have h0 := stitchAt 0 4 frame027scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch01 : batch01.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope01

private abbrev frame027test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch02.stop,F)

private theorem frame027scope02_s000 : ((fits02.drop 0).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s004 : ((fits02.drop 4).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s008 : ((fits02.drop 8).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s012 : ((fits02.drop 12).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s016 : ((fits02.drop 16).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s020 : ((fits02.drop 20).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s024 : ((fits02.drop 24).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s028 : ((fits02.drop 28).take 4).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_s032 : ((fits02.drop 32).take 3).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02_end : (fits02.drop 35).all frame027test02=true := by
  decide +kernel

private theorem frame027scope02 : fits02.all frame027test02=true := by
  have h32 := stitchAt 32 3 frame027scope02_s032 frame027scope02_end
  have h28 := stitchAt 28 4 frame027scope02_s028 h32
  have h24 := stitchAt 24 4 frame027scope02_s024 h28
  have h20 := stitchAt 20 4 frame027scope02_s020 h24
  have h16 := stitchAt 16 4 frame027scope02_s016 h20
  have h12 := stitchAt 12 4 frame027scope02_s012 h16
  have h8 := stitchAt 8 4 frame027scope02_s008 h12
  have h4 := stitchAt 4 4 frame027scope02_s004 h8
  have h0 := stitchAt 0 4 frame027scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch02 : batch02.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope02

private abbrev frame027test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch03.stop,F)

private theorem frame027scope03_s000 : ((fits03.drop 0).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s004 : ((fits03.drop 4).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s008 : ((fits03.drop 8).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s012 : ((fits03.drop 12).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s016 : ((fits03.drop 16).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s020 : ((fits03.drop 20).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s024 : ((fits03.drop 24).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s028 : ((fits03.drop 28).take 4).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_s032 : ((fits03.drop 32).take 3).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03_end : (fits03.drop 35).all frame027test03=true := by
  decide +kernel

private theorem frame027scope03 : fits03.all frame027test03=true := by
  have h32 := stitchAt 32 3 frame027scope03_s032 frame027scope03_end
  have h28 := stitchAt 28 4 frame027scope03_s028 h32
  have h24 := stitchAt 24 4 frame027scope03_s024 h28
  have h20 := stitchAt 20 4 frame027scope03_s020 h24
  have h16 := stitchAt 16 4 frame027scope03_s016 h20
  have h12 := stitchAt 12 4 frame027scope03_s012 h16
  have h8 := stitchAt 8 4 frame027scope03_s008 h12
  have h4 := stitchAt 4 4 frame027scope03_s004 h8
  have h0 := stitchAt 0 4 frame027scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch03 : batch03.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope03

private abbrev frame027test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch04.stop,F)

private theorem frame027scope04_s000 : ((fits04.drop 0).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s004 : ((fits04.drop 4).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s008 : ((fits04.drop 8).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s012 : ((fits04.drop 12).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s016 : ((fits04.drop 16).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s020 : ((fits04.drop 20).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s024 : ((fits04.drop 24).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s028 : ((fits04.drop 28).take 4).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_s032 : ((fits04.drop 32).take 3).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04_end : (fits04.drop 35).all frame027test04=true := by
  decide +kernel

private theorem frame027scope04 : fits04.all frame027test04=true := by
  have h32 := stitchAt 32 3 frame027scope04_s032 frame027scope04_end
  have h28 := stitchAt 28 4 frame027scope04_s028 h32
  have h24 := stitchAt 24 4 frame027scope04_s024 h28
  have h20 := stitchAt 20 4 frame027scope04_s020 h24
  have h16 := stitchAt 16 4 frame027scope04_s016 h20
  have h12 := stitchAt 12 4 frame027scope04_s012 h16
  have h8 := stitchAt 8 4 frame027scope04_s008 h12
  have h4 := stitchAt 4 4 frame027scope04_s004 h8
  have h0 := stitchAt 0 4 frame027scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch04 : batch04.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope04

private abbrev frame027test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch05.stop,F)

private theorem frame027scope05_s000 : ((fits05.drop 0).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s004 : ((fits05.drop 4).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s008 : ((fits05.drop 8).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s012 : ((fits05.drop 12).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s016 : ((fits05.drop 16).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s020 : ((fits05.drop 20).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s024 : ((fits05.drop 24).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s028 : ((fits05.drop 28).take 4).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_s032 : ((fits05.drop 32).take 3).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05_end : (fits05.drop 35).all frame027test05=true := by
  decide +kernel

private theorem frame027scope05 : fits05.all frame027test05=true := by
  have h32 := stitchAt 32 3 frame027scope05_s032 frame027scope05_end
  have h28 := stitchAt 28 4 frame027scope05_s028 h32
  have h24 := stitchAt 24 4 frame027scope05_s024 h28
  have h20 := stitchAt 20 4 frame027scope05_s020 h24
  have h16 := stitchAt 16 4 frame027scope05_s016 h20
  have h12 := stitchAt 12 4 frame027scope05_s012 h16
  have h8 := stitchAt 8 4 frame027scope05_s008 h12
  have h4 := stitchAt 4 4 frame027scope05_s004 h8
  have h0 := stitchAt 0 4 frame027scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch05 : batch05.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope05

private abbrev frame027test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch06.stop,F)

private theorem frame027scope06_s000 : ((fits06.drop 0).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s004 : ((fits06.drop 4).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s008 : ((fits06.drop 8).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s012 : ((fits06.drop 12).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s016 : ((fits06.drop 16).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s020 : ((fits06.drop 20).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s024 : ((fits06.drop 24).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s028 : ((fits06.drop 28).take 4).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_s032 : ((fits06.drop 32).take 3).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06_end : (fits06.drop 35).all frame027test06=true := by
  decide +kernel

private theorem frame027scope06 : fits06.all frame027test06=true := by
  have h32 := stitchAt 32 3 frame027scope06_s032 frame027scope06_end
  have h28 := stitchAt 28 4 frame027scope06_s028 h32
  have h24 := stitchAt 24 4 frame027scope06_s024 h28
  have h20 := stitchAt 20 4 frame027scope06_s020 h24
  have h16 := stitchAt 16 4 frame027scope06_s016 h20
  have h12 := stitchAt 12 4 frame027scope06_s012 h16
  have h8 := stitchAt 8 4 frame027scope06_s008 h12
  have h4 := stitchAt 4 4 frame027scope06_s004 h8
  have h0 := stitchAt 0 4 frame027scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch06 : batch06.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope06

private abbrev frame027test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame58 (fun z => List.lookup (guideCode z) guide027)
    (batch07.stop,F)

private theorem frame027scope07_s000 : ((fits07.drop 0).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s004 : ((fits07.drop 4).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s008 : ((fits07.drop 8).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s012 : ((fits07.drop 12).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s016 : ((fits07.drop 16).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s020 : ((fits07.drop 20).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s024 : ((fits07.drop 24).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s028 : ((fits07.drop 28).take 4).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_s032 : ((fits07.drop 32).take 3).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07_end : (fits07.drop 35).all frame027test07=true := by
  decide +kernel

private theorem frame027scope07 : fits07.all frame027test07=true := by
  have h32 := stitchAt 32 3 frame027scope07_s032 frame027scope07_end
  have h28 := stitchAt 28 4 frame027scope07_s028 h32
  have h24 := stitchAt 24 4 frame027scope07_s024 h28
  have h20 := stitchAt 20 4 frame027scope07_s020 h24
  have h16 := stitchAt 16 4 frame027scope07_s016 h20
  have h12 := stitchAt 12 4 frame027scope07_s012 h16
  have h8 := stitchAt 8 4 frame027scope07_s008 h12
  have h4 := stitchAt 4 4 frame027scope07_s004 h8
  have h0 := stitchAt 0 4 frame027scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame027batch07 : batch07.pickTest original frame58=true :=
  FitBatch.pickTest_of_scoped scoped027 frame027scope07

private theorem frameBatches027 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame58)=true := by
  simp only [List.all_cons,List.all_nil,frame027batch00,frame027batch01,frame027batch02,frame027batch03,frame027batch04,frame027batch05,frame027batch06,frame027batch07,Bool.and_self]

theorem frameOK027 : frameRankTest original useStop frame58=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches027


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
