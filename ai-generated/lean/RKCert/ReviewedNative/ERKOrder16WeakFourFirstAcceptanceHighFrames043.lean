module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK086 : stripTest frame174=true := by decide +kernel

theorem spanOK086 : checkChain 1968 1952 [frame174.span]=true := by decide +kernel

private theorem guideAt086 : List.lookup frame174.span.1 guideTable=some guide086 := by
  decide +kernel

private theorem scoped086 : original.guide frame174.span.1 =
    (fun z => List.lookup (guideCode z) guide086) := by
  funext z
  change (List.lookup frame174.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide086
  simp only [guideAt086,Option.bind_some]

private abbrev frame086test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch00.stop,F)

private theorem frame086scope00_s000 : ((fits00.drop 0).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s004 : ((fits00.drop 4).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s008 : ((fits00.drop 8).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s012 : ((fits00.drop 12).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s016 : ((fits00.drop 16).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s020 : ((fits00.drop 20).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s024 : ((fits00.drop 24).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s028 : ((fits00.drop 28).take 4).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_s032 : ((fits00.drop 32).take 3).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00_end : (fits00.drop 35).all frame086test00=true := by
  decide +kernel

private theorem frame086scope00 : fits00.all frame086test00=true := by
  have h32 := stitchAt 32 3 frame086scope00_s032 frame086scope00_end
  have h28 := stitchAt 28 4 frame086scope00_s028 h32
  have h24 := stitchAt 24 4 frame086scope00_s024 h28
  have h20 := stitchAt 20 4 frame086scope00_s020 h24
  have h16 := stitchAt 16 4 frame086scope00_s016 h20
  have h12 := stitchAt 12 4 frame086scope00_s012 h16
  have h8 := stitchAt 8 4 frame086scope00_s008 h12
  have h4 := stitchAt 4 4 frame086scope00_s004 h8
  have h0 := stitchAt 0 4 frame086scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch00 : batch00.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope00

private abbrev frame086test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch01.stop,F)

private theorem frame086scope01_s000 : ((fits01.drop 0).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s004 : ((fits01.drop 4).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s008 : ((fits01.drop 8).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s012 : ((fits01.drop 12).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s016 : ((fits01.drop 16).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s020 : ((fits01.drop 20).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s024 : ((fits01.drop 24).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s028 : ((fits01.drop 28).take 4).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_s032 : ((fits01.drop 32).take 3).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01_end : (fits01.drop 35).all frame086test01=true := by
  decide +kernel

private theorem frame086scope01 : fits01.all frame086test01=true := by
  have h32 := stitchAt 32 3 frame086scope01_s032 frame086scope01_end
  have h28 := stitchAt 28 4 frame086scope01_s028 h32
  have h24 := stitchAt 24 4 frame086scope01_s024 h28
  have h20 := stitchAt 20 4 frame086scope01_s020 h24
  have h16 := stitchAt 16 4 frame086scope01_s016 h20
  have h12 := stitchAt 12 4 frame086scope01_s012 h16
  have h8 := stitchAt 8 4 frame086scope01_s008 h12
  have h4 := stitchAt 4 4 frame086scope01_s004 h8
  have h0 := stitchAt 0 4 frame086scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch01 : batch01.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope01

private abbrev frame086test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch02.stop,F)

private theorem frame086scope02_s000 : ((fits02.drop 0).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s004 : ((fits02.drop 4).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s008 : ((fits02.drop 8).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s012 : ((fits02.drop 12).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s016 : ((fits02.drop 16).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s020 : ((fits02.drop 20).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s024 : ((fits02.drop 24).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s028 : ((fits02.drop 28).take 4).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_s032 : ((fits02.drop 32).take 3).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02_end : (fits02.drop 35).all frame086test02=true := by
  decide +kernel

private theorem frame086scope02 : fits02.all frame086test02=true := by
  have h32 := stitchAt 32 3 frame086scope02_s032 frame086scope02_end
  have h28 := stitchAt 28 4 frame086scope02_s028 h32
  have h24 := stitchAt 24 4 frame086scope02_s024 h28
  have h20 := stitchAt 20 4 frame086scope02_s020 h24
  have h16 := stitchAt 16 4 frame086scope02_s016 h20
  have h12 := stitchAt 12 4 frame086scope02_s012 h16
  have h8 := stitchAt 8 4 frame086scope02_s008 h12
  have h4 := stitchAt 4 4 frame086scope02_s004 h8
  have h0 := stitchAt 0 4 frame086scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch02 : batch02.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope02

private abbrev frame086test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch03.stop,F)

private theorem frame086scope03_s000 : ((fits03.drop 0).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s004 : ((fits03.drop 4).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s008 : ((fits03.drop 8).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s012 : ((fits03.drop 12).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s016 : ((fits03.drop 16).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s020 : ((fits03.drop 20).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s024 : ((fits03.drop 24).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s028 : ((fits03.drop 28).take 4).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_s032 : ((fits03.drop 32).take 3).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03_end : (fits03.drop 35).all frame086test03=true := by
  decide +kernel

private theorem frame086scope03 : fits03.all frame086test03=true := by
  have h32 := stitchAt 32 3 frame086scope03_s032 frame086scope03_end
  have h28 := stitchAt 28 4 frame086scope03_s028 h32
  have h24 := stitchAt 24 4 frame086scope03_s024 h28
  have h20 := stitchAt 20 4 frame086scope03_s020 h24
  have h16 := stitchAt 16 4 frame086scope03_s016 h20
  have h12 := stitchAt 12 4 frame086scope03_s012 h16
  have h8 := stitchAt 8 4 frame086scope03_s008 h12
  have h4 := stitchAt 4 4 frame086scope03_s004 h8
  have h0 := stitchAt 0 4 frame086scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch03 : batch03.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope03

private abbrev frame086test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch04.stop,F)

private theorem frame086scope04_s000 : ((fits04.drop 0).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s004 : ((fits04.drop 4).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s008 : ((fits04.drop 8).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s012 : ((fits04.drop 12).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s016 : ((fits04.drop 16).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s020 : ((fits04.drop 20).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s024 : ((fits04.drop 24).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s028 : ((fits04.drop 28).take 4).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_s032 : ((fits04.drop 32).take 3).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04_end : (fits04.drop 35).all frame086test04=true := by
  decide +kernel

private theorem frame086scope04 : fits04.all frame086test04=true := by
  have h32 := stitchAt 32 3 frame086scope04_s032 frame086scope04_end
  have h28 := stitchAt 28 4 frame086scope04_s028 h32
  have h24 := stitchAt 24 4 frame086scope04_s024 h28
  have h20 := stitchAt 20 4 frame086scope04_s020 h24
  have h16 := stitchAt 16 4 frame086scope04_s016 h20
  have h12 := stitchAt 12 4 frame086scope04_s012 h16
  have h8 := stitchAt 8 4 frame086scope04_s008 h12
  have h4 := stitchAt 4 4 frame086scope04_s004 h8
  have h0 := stitchAt 0 4 frame086scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch04 : batch04.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope04

private abbrev frame086test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch05.stop,F)

private theorem frame086scope05_s000 : ((fits05.drop 0).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s004 : ((fits05.drop 4).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s008 : ((fits05.drop 8).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s012 : ((fits05.drop 12).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s016 : ((fits05.drop 16).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s020 : ((fits05.drop 20).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s024 : ((fits05.drop 24).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s028 : ((fits05.drop 28).take 4).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_s032 : ((fits05.drop 32).take 3).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05_end : (fits05.drop 35).all frame086test05=true := by
  decide +kernel

private theorem frame086scope05 : fits05.all frame086test05=true := by
  have h32 := stitchAt 32 3 frame086scope05_s032 frame086scope05_end
  have h28 := stitchAt 28 4 frame086scope05_s028 h32
  have h24 := stitchAt 24 4 frame086scope05_s024 h28
  have h20 := stitchAt 20 4 frame086scope05_s020 h24
  have h16 := stitchAt 16 4 frame086scope05_s016 h20
  have h12 := stitchAt 12 4 frame086scope05_s012 h16
  have h8 := stitchAt 8 4 frame086scope05_s008 h12
  have h4 := stitchAt 4 4 frame086scope05_s004 h8
  have h0 := stitchAt 0 4 frame086scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch05 : batch05.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope05

private abbrev frame086test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch06.stop,F)

private theorem frame086scope06_s000 : ((fits06.drop 0).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s004 : ((fits06.drop 4).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s008 : ((fits06.drop 8).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s012 : ((fits06.drop 12).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s016 : ((fits06.drop 16).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s020 : ((fits06.drop 20).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s024 : ((fits06.drop 24).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s028 : ((fits06.drop 28).take 4).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_s032 : ((fits06.drop 32).take 3).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06_end : (fits06.drop 35).all frame086test06=true := by
  decide +kernel

private theorem frame086scope06 : fits06.all frame086test06=true := by
  have h32 := stitchAt 32 3 frame086scope06_s032 frame086scope06_end
  have h28 := stitchAt 28 4 frame086scope06_s028 h32
  have h24 := stitchAt 24 4 frame086scope06_s024 h28
  have h20 := stitchAt 20 4 frame086scope06_s020 h24
  have h16 := stitchAt 16 4 frame086scope06_s016 h20
  have h12 := stitchAt 12 4 frame086scope06_s012 h16
  have h8 := stitchAt 8 4 frame086scope06_s008 h12
  have h4 := stitchAt 4 4 frame086scope06_s004 h8
  have h0 := stitchAt 0 4 frame086scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch06 : batch06.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope06

private abbrev frame086test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame174 (fun z => List.lookup (guideCode z) guide086)
    (batch07.stop,F)

private theorem frame086scope07_s000 : ((fits07.drop 0).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s004 : ((fits07.drop 4).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s008 : ((fits07.drop 8).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s012 : ((fits07.drop 12).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s016 : ((fits07.drop 16).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s020 : ((fits07.drop 20).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s024 : ((fits07.drop 24).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s028 : ((fits07.drop 28).take 4).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_s032 : ((fits07.drop 32).take 3).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07_end : (fits07.drop 35).all frame086test07=true := by
  decide +kernel

private theorem frame086scope07 : fits07.all frame086test07=true := by
  have h32 := stitchAt 32 3 frame086scope07_s032 frame086scope07_end
  have h28 := stitchAt 28 4 frame086scope07_s028 h32
  have h24 := stitchAt 24 4 frame086scope07_s024 h28
  have h20 := stitchAt 20 4 frame086scope07_s020 h24
  have h16 := stitchAt 16 4 frame086scope07_s016 h20
  have h12 := stitchAt 12 4 frame086scope07_s012 h16
  have h8 := stitchAt 8 4 frame086scope07_s008 h12
  have h4 := stitchAt 4 4 frame086scope07_s004 h8
  have h0 := stitchAt 0 4 frame086scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame086batch07 : batch07.pickTest original frame174=true :=
  FitBatch.pickTest_of_scoped scoped086 frame086scope07

private theorem frameBatches086 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame174)=true := by
  simp only [List.all_cons,List.all_nil,frame086batch00,frame086batch01,frame086batch02,frame086batch03,frame086batch04,frame086batch05,frame086batch06,frame086batch07,Bool.and_self]

theorem frameOK086 : frameRankTest original useStop frame174=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches086

theorem stripOK087 : stripTest frame175=true := by decide +kernel

theorem spanOK087 : checkChain 1984 1968 [frame175.span]=true := by decide +kernel

private theorem guideAt087 : List.lookup frame175.span.1 guideTable=some guide087 := by
  decide +kernel

private theorem scoped087 : original.guide frame175.span.1 =
    (fun z => List.lookup (guideCode z) guide087) := by
  funext z
  change (List.lookup frame175.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide087
  simp only [guideAt087,Option.bind_some]

private abbrev frame087test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch00.stop,F)

private theorem frame087scope00_s000 : ((fits00.drop 0).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s004 : ((fits00.drop 4).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s008 : ((fits00.drop 8).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s012 : ((fits00.drop 12).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s016 : ((fits00.drop 16).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s020 : ((fits00.drop 20).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s024 : ((fits00.drop 24).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s028 : ((fits00.drop 28).take 4).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_s032 : ((fits00.drop 32).take 3).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00_end : (fits00.drop 35).all frame087test00=true := by
  decide +kernel

private theorem frame087scope00 : fits00.all frame087test00=true := by
  have h32 := stitchAt 32 3 frame087scope00_s032 frame087scope00_end
  have h28 := stitchAt 28 4 frame087scope00_s028 h32
  have h24 := stitchAt 24 4 frame087scope00_s024 h28
  have h20 := stitchAt 20 4 frame087scope00_s020 h24
  have h16 := stitchAt 16 4 frame087scope00_s016 h20
  have h12 := stitchAt 12 4 frame087scope00_s012 h16
  have h8 := stitchAt 8 4 frame087scope00_s008 h12
  have h4 := stitchAt 4 4 frame087scope00_s004 h8
  have h0 := stitchAt 0 4 frame087scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch00 : batch00.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope00

private abbrev frame087test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch01.stop,F)

private theorem frame087scope01_s000 : ((fits01.drop 0).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s004 : ((fits01.drop 4).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s008 : ((fits01.drop 8).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s012 : ((fits01.drop 12).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s016 : ((fits01.drop 16).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s020 : ((fits01.drop 20).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s024 : ((fits01.drop 24).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s028 : ((fits01.drop 28).take 4).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_s032 : ((fits01.drop 32).take 3).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01_end : (fits01.drop 35).all frame087test01=true := by
  decide +kernel

private theorem frame087scope01 : fits01.all frame087test01=true := by
  have h32 := stitchAt 32 3 frame087scope01_s032 frame087scope01_end
  have h28 := stitchAt 28 4 frame087scope01_s028 h32
  have h24 := stitchAt 24 4 frame087scope01_s024 h28
  have h20 := stitchAt 20 4 frame087scope01_s020 h24
  have h16 := stitchAt 16 4 frame087scope01_s016 h20
  have h12 := stitchAt 12 4 frame087scope01_s012 h16
  have h8 := stitchAt 8 4 frame087scope01_s008 h12
  have h4 := stitchAt 4 4 frame087scope01_s004 h8
  have h0 := stitchAt 0 4 frame087scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch01 : batch01.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope01

private abbrev frame087test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch02.stop,F)

private theorem frame087scope02_s000 : ((fits02.drop 0).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s004 : ((fits02.drop 4).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s008 : ((fits02.drop 8).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s012 : ((fits02.drop 12).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s016 : ((fits02.drop 16).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s020 : ((fits02.drop 20).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s024 : ((fits02.drop 24).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s028 : ((fits02.drop 28).take 4).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_s032 : ((fits02.drop 32).take 3).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02_end : (fits02.drop 35).all frame087test02=true := by
  decide +kernel

private theorem frame087scope02 : fits02.all frame087test02=true := by
  have h32 := stitchAt 32 3 frame087scope02_s032 frame087scope02_end
  have h28 := stitchAt 28 4 frame087scope02_s028 h32
  have h24 := stitchAt 24 4 frame087scope02_s024 h28
  have h20 := stitchAt 20 4 frame087scope02_s020 h24
  have h16 := stitchAt 16 4 frame087scope02_s016 h20
  have h12 := stitchAt 12 4 frame087scope02_s012 h16
  have h8 := stitchAt 8 4 frame087scope02_s008 h12
  have h4 := stitchAt 4 4 frame087scope02_s004 h8
  have h0 := stitchAt 0 4 frame087scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch02 : batch02.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope02

private abbrev frame087test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch03.stop,F)

private theorem frame087scope03_s000 : ((fits03.drop 0).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s004 : ((fits03.drop 4).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s008 : ((fits03.drop 8).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s012 : ((fits03.drop 12).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s016 : ((fits03.drop 16).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s020 : ((fits03.drop 20).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s024 : ((fits03.drop 24).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s028 : ((fits03.drop 28).take 4).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_s032 : ((fits03.drop 32).take 3).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03_end : (fits03.drop 35).all frame087test03=true := by
  decide +kernel

private theorem frame087scope03 : fits03.all frame087test03=true := by
  have h32 := stitchAt 32 3 frame087scope03_s032 frame087scope03_end
  have h28 := stitchAt 28 4 frame087scope03_s028 h32
  have h24 := stitchAt 24 4 frame087scope03_s024 h28
  have h20 := stitchAt 20 4 frame087scope03_s020 h24
  have h16 := stitchAt 16 4 frame087scope03_s016 h20
  have h12 := stitchAt 12 4 frame087scope03_s012 h16
  have h8 := stitchAt 8 4 frame087scope03_s008 h12
  have h4 := stitchAt 4 4 frame087scope03_s004 h8
  have h0 := stitchAt 0 4 frame087scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch03 : batch03.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope03

private abbrev frame087test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch04.stop,F)

private theorem frame087scope04_s000 : ((fits04.drop 0).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s004 : ((fits04.drop 4).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s008 : ((fits04.drop 8).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s012 : ((fits04.drop 12).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s016 : ((fits04.drop 16).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s020 : ((fits04.drop 20).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s024 : ((fits04.drop 24).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s028 : ((fits04.drop 28).take 4).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_s032 : ((fits04.drop 32).take 3).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04_end : (fits04.drop 35).all frame087test04=true := by
  decide +kernel

private theorem frame087scope04 : fits04.all frame087test04=true := by
  have h32 := stitchAt 32 3 frame087scope04_s032 frame087scope04_end
  have h28 := stitchAt 28 4 frame087scope04_s028 h32
  have h24 := stitchAt 24 4 frame087scope04_s024 h28
  have h20 := stitchAt 20 4 frame087scope04_s020 h24
  have h16 := stitchAt 16 4 frame087scope04_s016 h20
  have h12 := stitchAt 12 4 frame087scope04_s012 h16
  have h8 := stitchAt 8 4 frame087scope04_s008 h12
  have h4 := stitchAt 4 4 frame087scope04_s004 h8
  have h0 := stitchAt 0 4 frame087scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch04 : batch04.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope04

private abbrev frame087test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch05.stop,F)

private theorem frame087scope05_s000 : ((fits05.drop 0).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s004 : ((fits05.drop 4).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s008 : ((fits05.drop 8).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s012 : ((fits05.drop 12).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s016 : ((fits05.drop 16).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s020 : ((fits05.drop 20).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s024 : ((fits05.drop 24).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s028 : ((fits05.drop 28).take 4).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_s032 : ((fits05.drop 32).take 3).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05_end : (fits05.drop 35).all frame087test05=true := by
  decide +kernel

private theorem frame087scope05 : fits05.all frame087test05=true := by
  have h32 := stitchAt 32 3 frame087scope05_s032 frame087scope05_end
  have h28 := stitchAt 28 4 frame087scope05_s028 h32
  have h24 := stitchAt 24 4 frame087scope05_s024 h28
  have h20 := stitchAt 20 4 frame087scope05_s020 h24
  have h16 := stitchAt 16 4 frame087scope05_s016 h20
  have h12 := stitchAt 12 4 frame087scope05_s012 h16
  have h8 := stitchAt 8 4 frame087scope05_s008 h12
  have h4 := stitchAt 4 4 frame087scope05_s004 h8
  have h0 := stitchAt 0 4 frame087scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch05 : batch05.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope05

private abbrev frame087test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch06.stop,F)

private theorem frame087scope06_s000 : ((fits06.drop 0).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s004 : ((fits06.drop 4).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s008 : ((fits06.drop 8).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s012 : ((fits06.drop 12).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s016 : ((fits06.drop 16).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s020 : ((fits06.drop 20).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s024 : ((fits06.drop 24).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s028 : ((fits06.drop 28).take 4).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_s032 : ((fits06.drop 32).take 3).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06_end : (fits06.drop 35).all frame087test06=true := by
  decide +kernel

private theorem frame087scope06 : fits06.all frame087test06=true := by
  have h32 := stitchAt 32 3 frame087scope06_s032 frame087scope06_end
  have h28 := stitchAt 28 4 frame087scope06_s028 h32
  have h24 := stitchAt 24 4 frame087scope06_s024 h28
  have h20 := stitchAt 20 4 frame087scope06_s020 h24
  have h16 := stitchAt 16 4 frame087scope06_s016 h20
  have h12 := stitchAt 12 4 frame087scope06_s012 h16
  have h8 := stitchAt 8 4 frame087scope06_s008 h12
  have h4 := stitchAt 4 4 frame087scope06_s004 h8
  have h0 := stitchAt 0 4 frame087scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch06 : batch06.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope06

private abbrev frame087test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame175 (fun z => List.lookup (guideCode z) guide087)
    (batch07.stop,F)

private theorem frame087scope07_s000 : ((fits07.drop 0).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s004 : ((fits07.drop 4).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s008 : ((fits07.drop 8).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s012 : ((fits07.drop 12).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s016 : ((fits07.drop 16).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s020 : ((fits07.drop 20).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s024 : ((fits07.drop 24).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s028 : ((fits07.drop 28).take 4).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_s032 : ((fits07.drop 32).take 3).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07_end : (fits07.drop 35).all frame087test07=true := by
  decide +kernel

private theorem frame087scope07 : fits07.all frame087test07=true := by
  have h32 := stitchAt 32 3 frame087scope07_s032 frame087scope07_end
  have h28 := stitchAt 28 4 frame087scope07_s028 h32
  have h24 := stitchAt 24 4 frame087scope07_s024 h28
  have h20 := stitchAt 20 4 frame087scope07_s020 h24
  have h16 := stitchAt 16 4 frame087scope07_s016 h20
  have h12 := stitchAt 12 4 frame087scope07_s012 h16
  have h8 := stitchAt 8 4 frame087scope07_s008 h12
  have h4 := stitchAt 4 4 frame087scope07_s004 h8
  have h0 := stitchAt 0 4 frame087scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame087batch07 : batch07.pickTest original frame175=true :=
  FitBatch.pickTest_of_scoped scoped087 frame087scope07

private theorem frameBatches087 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame175)=true := by
  simp only [List.all_cons,List.all_nil,frame087batch00,frame087batch01,frame087batch02,frame087batch03,frame087batch04,frame087batch05,frame087batch06,frame087batch07,Bool.and_self]

theorem frameOK087 : frameRankTest original useStop frame175=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches087


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
