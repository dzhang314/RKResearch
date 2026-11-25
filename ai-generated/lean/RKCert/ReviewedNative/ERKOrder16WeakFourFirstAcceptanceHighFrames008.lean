module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK016 : stripTest frame34=true := by decide +kernel

theorem spanOK016 : checkChain 1520 1504 [frame34.span]=true := by decide +kernel

private theorem guideAt016 : List.lookup frame34.span.1 guideTable=some guide016 := by
  decide +kernel

private theorem scoped016 : original.guide frame34.span.1 =
    (fun z => List.lookup (guideCode z) guide016) := by
  funext z
  change (List.lookup frame34.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide016
  simp only [guideAt016,Option.bind_some]

private abbrev frame016test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch00.stop,F)

private theorem frame016scope00_s000 : ((fits00.drop 0).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s004 : ((fits00.drop 4).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s008 : ((fits00.drop 8).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s012 : ((fits00.drop 12).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s016 : ((fits00.drop 16).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s020 : ((fits00.drop 20).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s024 : ((fits00.drop 24).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s028 : ((fits00.drop 28).take 4).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_s032 : ((fits00.drop 32).take 3).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00_end : (fits00.drop 35).all frame016test00=true := by
  decide +kernel

private theorem frame016scope00 : fits00.all frame016test00=true := by
  have h32 := stitchAt 32 3 frame016scope00_s032 frame016scope00_end
  have h28 := stitchAt 28 4 frame016scope00_s028 h32
  have h24 := stitchAt 24 4 frame016scope00_s024 h28
  have h20 := stitchAt 20 4 frame016scope00_s020 h24
  have h16 := stitchAt 16 4 frame016scope00_s016 h20
  have h12 := stitchAt 12 4 frame016scope00_s012 h16
  have h8 := stitchAt 8 4 frame016scope00_s008 h12
  have h4 := stitchAt 4 4 frame016scope00_s004 h8
  have h0 := stitchAt 0 4 frame016scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch00 : batch00.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope00

private abbrev frame016test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch01.stop,F)

private theorem frame016scope01_s000 : ((fits01.drop 0).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s004 : ((fits01.drop 4).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s008 : ((fits01.drop 8).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s012 : ((fits01.drop 12).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s016 : ((fits01.drop 16).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s020 : ((fits01.drop 20).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s024 : ((fits01.drop 24).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s028 : ((fits01.drop 28).take 4).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_s032 : ((fits01.drop 32).take 3).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01_end : (fits01.drop 35).all frame016test01=true := by
  decide +kernel

private theorem frame016scope01 : fits01.all frame016test01=true := by
  have h32 := stitchAt 32 3 frame016scope01_s032 frame016scope01_end
  have h28 := stitchAt 28 4 frame016scope01_s028 h32
  have h24 := stitchAt 24 4 frame016scope01_s024 h28
  have h20 := stitchAt 20 4 frame016scope01_s020 h24
  have h16 := stitchAt 16 4 frame016scope01_s016 h20
  have h12 := stitchAt 12 4 frame016scope01_s012 h16
  have h8 := stitchAt 8 4 frame016scope01_s008 h12
  have h4 := stitchAt 4 4 frame016scope01_s004 h8
  have h0 := stitchAt 0 4 frame016scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch01 : batch01.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope01

private abbrev frame016test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch02.stop,F)

private theorem frame016scope02_s000 : ((fits02.drop 0).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s004 : ((fits02.drop 4).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s008 : ((fits02.drop 8).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s012 : ((fits02.drop 12).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s016 : ((fits02.drop 16).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s020 : ((fits02.drop 20).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s024 : ((fits02.drop 24).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s028 : ((fits02.drop 28).take 4).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_s032 : ((fits02.drop 32).take 3).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02_end : (fits02.drop 35).all frame016test02=true := by
  decide +kernel

private theorem frame016scope02 : fits02.all frame016test02=true := by
  have h32 := stitchAt 32 3 frame016scope02_s032 frame016scope02_end
  have h28 := stitchAt 28 4 frame016scope02_s028 h32
  have h24 := stitchAt 24 4 frame016scope02_s024 h28
  have h20 := stitchAt 20 4 frame016scope02_s020 h24
  have h16 := stitchAt 16 4 frame016scope02_s016 h20
  have h12 := stitchAt 12 4 frame016scope02_s012 h16
  have h8 := stitchAt 8 4 frame016scope02_s008 h12
  have h4 := stitchAt 4 4 frame016scope02_s004 h8
  have h0 := stitchAt 0 4 frame016scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch02 : batch02.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope02

private abbrev frame016test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch03.stop,F)

private theorem frame016scope03_s000 : ((fits03.drop 0).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s004 : ((fits03.drop 4).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s008 : ((fits03.drop 8).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s012 : ((fits03.drop 12).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s016 : ((fits03.drop 16).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s020 : ((fits03.drop 20).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s024 : ((fits03.drop 24).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s028 : ((fits03.drop 28).take 4).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_s032 : ((fits03.drop 32).take 3).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03_end : (fits03.drop 35).all frame016test03=true := by
  decide +kernel

private theorem frame016scope03 : fits03.all frame016test03=true := by
  have h32 := stitchAt 32 3 frame016scope03_s032 frame016scope03_end
  have h28 := stitchAt 28 4 frame016scope03_s028 h32
  have h24 := stitchAt 24 4 frame016scope03_s024 h28
  have h20 := stitchAt 20 4 frame016scope03_s020 h24
  have h16 := stitchAt 16 4 frame016scope03_s016 h20
  have h12 := stitchAt 12 4 frame016scope03_s012 h16
  have h8 := stitchAt 8 4 frame016scope03_s008 h12
  have h4 := stitchAt 4 4 frame016scope03_s004 h8
  have h0 := stitchAt 0 4 frame016scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch03 : batch03.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope03

private abbrev frame016test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch04.stop,F)

private theorem frame016scope04_s000 : ((fits04.drop 0).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s004 : ((fits04.drop 4).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s008 : ((fits04.drop 8).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s012 : ((fits04.drop 12).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s016 : ((fits04.drop 16).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s020 : ((fits04.drop 20).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s024 : ((fits04.drop 24).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s028 : ((fits04.drop 28).take 4).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_s032 : ((fits04.drop 32).take 3).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04_end : (fits04.drop 35).all frame016test04=true := by
  decide +kernel

private theorem frame016scope04 : fits04.all frame016test04=true := by
  have h32 := stitchAt 32 3 frame016scope04_s032 frame016scope04_end
  have h28 := stitchAt 28 4 frame016scope04_s028 h32
  have h24 := stitchAt 24 4 frame016scope04_s024 h28
  have h20 := stitchAt 20 4 frame016scope04_s020 h24
  have h16 := stitchAt 16 4 frame016scope04_s016 h20
  have h12 := stitchAt 12 4 frame016scope04_s012 h16
  have h8 := stitchAt 8 4 frame016scope04_s008 h12
  have h4 := stitchAt 4 4 frame016scope04_s004 h8
  have h0 := stitchAt 0 4 frame016scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch04 : batch04.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope04

private abbrev frame016test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch05.stop,F)

private theorem frame016scope05_s000 : ((fits05.drop 0).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s004 : ((fits05.drop 4).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s008 : ((fits05.drop 8).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s012 : ((fits05.drop 12).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s016 : ((fits05.drop 16).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s020 : ((fits05.drop 20).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s024 : ((fits05.drop 24).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s028 : ((fits05.drop 28).take 4).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_s032 : ((fits05.drop 32).take 3).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05_end : (fits05.drop 35).all frame016test05=true := by
  decide +kernel

private theorem frame016scope05 : fits05.all frame016test05=true := by
  have h32 := stitchAt 32 3 frame016scope05_s032 frame016scope05_end
  have h28 := stitchAt 28 4 frame016scope05_s028 h32
  have h24 := stitchAt 24 4 frame016scope05_s024 h28
  have h20 := stitchAt 20 4 frame016scope05_s020 h24
  have h16 := stitchAt 16 4 frame016scope05_s016 h20
  have h12 := stitchAt 12 4 frame016scope05_s012 h16
  have h8 := stitchAt 8 4 frame016scope05_s008 h12
  have h4 := stitchAt 4 4 frame016scope05_s004 h8
  have h0 := stitchAt 0 4 frame016scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch05 : batch05.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope05

private abbrev frame016test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch06.stop,F)

private theorem frame016scope06_s000 : ((fits06.drop 0).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s004 : ((fits06.drop 4).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s008 : ((fits06.drop 8).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s012 : ((fits06.drop 12).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s016 : ((fits06.drop 16).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s020 : ((fits06.drop 20).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s024 : ((fits06.drop 24).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s028 : ((fits06.drop 28).take 4).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_s032 : ((fits06.drop 32).take 3).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06_end : (fits06.drop 35).all frame016test06=true := by
  decide +kernel

private theorem frame016scope06 : fits06.all frame016test06=true := by
  have h32 := stitchAt 32 3 frame016scope06_s032 frame016scope06_end
  have h28 := stitchAt 28 4 frame016scope06_s028 h32
  have h24 := stitchAt 24 4 frame016scope06_s024 h28
  have h20 := stitchAt 20 4 frame016scope06_s020 h24
  have h16 := stitchAt 16 4 frame016scope06_s016 h20
  have h12 := stitchAt 12 4 frame016scope06_s012 h16
  have h8 := stitchAt 8 4 frame016scope06_s008 h12
  have h4 := stitchAt 4 4 frame016scope06_s004 h8
  have h0 := stitchAt 0 4 frame016scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch06 : batch06.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope06

private abbrev frame016test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame34 (fun z => List.lookup (guideCode z) guide016)
    (batch07.stop,F)

private theorem frame016scope07_s000 : ((fits07.drop 0).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s004 : ((fits07.drop 4).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s008 : ((fits07.drop 8).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s012 : ((fits07.drop 12).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s016 : ((fits07.drop 16).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s020 : ((fits07.drop 20).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s024 : ((fits07.drop 24).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s028 : ((fits07.drop 28).take 4).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_s032 : ((fits07.drop 32).take 3).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07_end : (fits07.drop 35).all frame016test07=true := by
  decide +kernel

private theorem frame016scope07 : fits07.all frame016test07=true := by
  have h32 := stitchAt 32 3 frame016scope07_s032 frame016scope07_end
  have h28 := stitchAt 28 4 frame016scope07_s028 h32
  have h24 := stitchAt 24 4 frame016scope07_s024 h28
  have h20 := stitchAt 20 4 frame016scope07_s020 h24
  have h16 := stitchAt 16 4 frame016scope07_s016 h20
  have h12 := stitchAt 12 4 frame016scope07_s012 h16
  have h8 := stitchAt 8 4 frame016scope07_s008 h12
  have h4 := stitchAt 4 4 frame016scope07_s004 h8
  have h0 := stitchAt 0 4 frame016scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame016batch07 : batch07.pickTest original frame34=true :=
  FitBatch.pickTest_of_scoped scoped016 frame016scope07

private theorem frameBatches016 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame34)=true := by
  simp only [List.all_cons,List.all_nil,frame016batch00,frame016batch01,frame016batch02,frame016batch03,frame016batch04,frame016batch05,frame016batch06,frame016batch07,Bool.and_self]

theorem frameOK016 : frameRankTest original useStop frame34=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches016

theorem stripOK017 : stripTest frame36=true := by decide +kernel

theorem spanOK017 : checkChain 1528 1520 [frame36.span]=true := by decide +kernel

private theorem guideAt017 : List.lookup frame36.span.1 guideTable=some guide017 := by
  decide +kernel

private theorem scoped017 : original.guide frame36.span.1 =
    (fun z => List.lookup (guideCode z) guide017) := by
  funext z
  change (List.lookup frame36.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide017
  simp only [guideAt017,Option.bind_some]

private abbrev frame017test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch00.stop,F)

private theorem frame017scope00_s000 : ((fits00.drop 0).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s004 : ((fits00.drop 4).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s008 : ((fits00.drop 8).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s012 : ((fits00.drop 12).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s016 : ((fits00.drop 16).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s020 : ((fits00.drop 20).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s024 : ((fits00.drop 24).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s028 : ((fits00.drop 28).take 4).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_s032 : ((fits00.drop 32).take 3).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00_end : (fits00.drop 35).all frame017test00=true := by
  decide +kernel

private theorem frame017scope00 : fits00.all frame017test00=true := by
  have h32 := stitchAt 32 3 frame017scope00_s032 frame017scope00_end
  have h28 := stitchAt 28 4 frame017scope00_s028 h32
  have h24 := stitchAt 24 4 frame017scope00_s024 h28
  have h20 := stitchAt 20 4 frame017scope00_s020 h24
  have h16 := stitchAt 16 4 frame017scope00_s016 h20
  have h12 := stitchAt 12 4 frame017scope00_s012 h16
  have h8 := stitchAt 8 4 frame017scope00_s008 h12
  have h4 := stitchAt 4 4 frame017scope00_s004 h8
  have h0 := stitchAt 0 4 frame017scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch00 : batch00.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope00

private abbrev frame017test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch01.stop,F)

private theorem frame017scope01_s000 : ((fits01.drop 0).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s004 : ((fits01.drop 4).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s008 : ((fits01.drop 8).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s012 : ((fits01.drop 12).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s016 : ((fits01.drop 16).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s020 : ((fits01.drop 20).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s024 : ((fits01.drop 24).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s028 : ((fits01.drop 28).take 4).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_s032 : ((fits01.drop 32).take 3).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01_end : (fits01.drop 35).all frame017test01=true := by
  decide +kernel

private theorem frame017scope01 : fits01.all frame017test01=true := by
  have h32 := stitchAt 32 3 frame017scope01_s032 frame017scope01_end
  have h28 := stitchAt 28 4 frame017scope01_s028 h32
  have h24 := stitchAt 24 4 frame017scope01_s024 h28
  have h20 := stitchAt 20 4 frame017scope01_s020 h24
  have h16 := stitchAt 16 4 frame017scope01_s016 h20
  have h12 := stitchAt 12 4 frame017scope01_s012 h16
  have h8 := stitchAt 8 4 frame017scope01_s008 h12
  have h4 := stitchAt 4 4 frame017scope01_s004 h8
  have h0 := stitchAt 0 4 frame017scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch01 : batch01.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope01

private abbrev frame017test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch02.stop,F)

private theorem frame017scope02_s000 : ((fits02.drop 0).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s004 : ((fits02.drop 4).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s008 : ((fits02.drop 8).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s012 : ((fits02.drop 12).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s016 : ((fits02.drop 16).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s020 : ((fits02.drop 20).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s024 : ((fits02.drop 24).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s028 : ((fits02.drop 28).take 4).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_s032 : ((fits02.drop 32).take 3).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02_end : (fits02.drop 35).all frame017test02=true := by
  decide +kernel

private theorem frame017scope02 : fits02.all frame017test02=true := by
  have h32 := stitchAt 32 3 frame017scope02_s032 frame017scope02_end
  have h28 := stitchAt 28 4 frame017scope02_s028 h32
  have h24 := stitchAt 24 4 frame017scope02_s024 h28
  have h20 := stitchAt 20 4 frame017scope02_s020 h24
  have h16 := stitchAt 16 4 frame017scope02_s016 h20
  have h12 := stitchAt 12 4 frame017scope02_s012 h16
  have h8 := stitchAt 8 4 frame017scope02_s008 h12
  have h4 := stitchAt 4 4 frame017scope02_s004 h8
  have h0 := stitchAt 0 4 frame017scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch02 : batch02.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope02

private abbrev frame017test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch03.stop,F)

private theorem frame017scope03_s000 : ((fits03.drop 0).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s004 : ((fits03.drop 4).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s008 : ((fits03.drop 8).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s012 : ((fits03.drop 12).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s016 : ((fits03.drop 16).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s020 : ((fits03.drop 20).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s024 : ((fits03.drop 24).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s028 : ((fits03.drop 28).take 4).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_s032 : ((fits03.drop 32).take 3).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03_end : (fits03.drop 35).all frame017test03=true := by
  decide +kernel

private theorem frame017scope03 : fits03.all frame017test03=true := by
  have h32 := stitchAt 32 3 frame017scope03_s032 frame017scope03_end
  have h28 := stitchAt 28 4 frame017scope03_s028 h32
  have h24 := stitchAt 24 4 frame017scope03_s024 h28
  have h20 := stitchAt 20 4 frame017scope03_s020 h24
  have h16 := stitchAt 16 4 frame017scope03_s016 h20
  have h12 := stitchAt 12 4 frame017scope03_s012 h16
  have h8 := stitchAt 8 4 frame017scope03_s008 h12
  have h4 := stitchAt 4 4 frame017scope03_s004 h8
  have h0 := stitchAt 0 4 frame017scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch03 : batch03.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope03

private abbrev frame017test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch04.stop,F)

private theorem frame017scope04_s000 : ((fits04.drop 0).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s004 : ((fits04.drop 4).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s008 : ((fits04.drop 8).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s012 : ((fits04.drop 12).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s016 : ((fits04.drop 16).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s020 : ((fits04.drop 20).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s024 : ((fits04.drop 24).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s028 : ((fits04.drop 28).take 4).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_s032 : ((fits04.drop 32).take 3).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04_end : (fits04.drop 35).all frame017test04=true := by
  decide +kernel

private theorem frame017scope04 : fits04.all frame017test04=true := by
  have h32 := stitchAt 32 3 frame017scope04_s032 frame017scope04_end
  have h28 := stitchAt 28 4 frame017scope04_s028 h32
  have h24 := stitchAt 24 4 frame017scope04_s024 h28
  have h20 := stitchAt 20 4 frame017scope04_s020 h24
  have h16 := stitchAt 16 4 frame017scope04_s016 h20
  have h12 := stitchAt 12 4 frame017scope04_s012 h16
  have h8 := stitchAt 8 4 frame017scope04_s008 h12
  have h4 := stitchAt 4 4 frame017scope04_s004 h8
  have h0 := stitchAt 0 4 frame017scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch04 : batch04.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope04

private abbrev frame017test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch05.stop,F)

private theorem frame017scope05_s000 : ((fits05.drop 0).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s004 : ((fits05.drop 4).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s008 : ((fits05.drop 8).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s012 : ((fits05.drop 12).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s016 : ((fits05.drop 16).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s020 : ((fits05.drop 20).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s024 : ((fits05.drop 24).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s028 : ((fits05.drop 28).take 4).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_s032 : ((fits05.drop 32).take 3).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05_end : (fits05.drop 35).all frame017test05=true := by
  decide +kernel

private theorem frame017scope05 : fits05.all frame017test05=true := by
  have h32 := stitchAt 32 3 frame017scope05_s032 frame017scope05_end
  have h28 := stitchAt 28 4 frame017scope05_s028 h32
  have h24 := stitchAt 24 4 frame017scope05_s024 h28
  have h20 := stitchAt 20 4 frame017scope05_s020 h24
  have h16 := stitchAt 16 4 frame017scope05_s016 h20
  have h12 := stitchAt 12 4 frame017scope05_s012 h16
  have h8 := stitchAt 8 4 frame017scope05_s008 h12
  have h4 := stitchAt 4 4 frame017scope05_s004 h8
  have h0 := stitchAt 0 4 frame017scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch05 : batch05.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope05

private abbrev frame017test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch06.stop,F)

private theorem frame017scope06_s000 : ((fits06.drop 0).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s004 : ((fits06.drop 4).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s008 : ((fits06.drop 8).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s012 : ((fits06.drop 12).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s016 : ((fits06.drop 16).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s020 : ((fits06.drop 20).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s024 : ((fits06.drop 24).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s028 : ((fits06.drop 28).take 4).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_s032 : ((fits06.drop 32).take 3).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06_end : (fits06.drop 35).all frame017test06=true := by
  decide +kernel

private theorem frame017scope06 : fits06.all frame017test06=true := by
  have h32 := stitchAt 32 3 frame017scope06_s032 frame017scope06_end
  have h28 := stitchAt 28 4 frame017scope06_s028 h32
  have h24 := stitchAt 24 4 frame017scope06_s024 h28
  have h20 := stitchAt 20 4 frame017scope06_s020 h24
  have h16 := stitchAt 16 4 frame017scope06_s016 h20
  have h12 := stitchAt 12 4 frame017scope06_s012 h16
  have h8 := stitchAt 8 4 frame017scope06_s008 h12
  have h4 := stitchAt 4 4 frame017scope06_s004 h8
  have h0 := stitchAt 0 4 frame017scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch06 : batch06.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope06

private abbrev frame017test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame36 (fun z => List.lookup (guideCode z) guide017)
    (batch07.stop,F)

private theorem frame017scope07_s000 : ((fits07.drop 0).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s004 : ((fits07.drop 4).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s008 : ((fits07.drop 8).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s012 : ((fits07.drop 12).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s016 : ((fits07.drop 16).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s020 : ((fits07.drop 20).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s024 : ((fits07.drop 24).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s028 : ((fits07.drop 28).take 4).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_s032 : ((fits07.drop 32).take 3).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07_end : (fits07.drop 35).all frame017test07=true := by
  decide +kernel

private theorem frame017scope07 : fits07.all frame017test07=true := by
  have h32 := stitchAt 32 3 frame017scope07_s032 frame017scope07_end
  have h28 := stitchAt 28 4 frame017scope07_s028 h32
  have h24 := stitchAt 24 4 frame017scope07_s024 h28
  have h20 := stitchAt 20 4 frame017scope07_s020 h24
  have h16 := stitchAt 16 4 frame017scope07_s016 h20
  have h12 := stitchAt 12 4 frame017scope07_s012 h16
  have h8 := stitchAt 8 4 frame017scope07_s008 h12
  have h4 := stitchAt 4 4 frame017scope07_s004 h8
  have h0 := stitchAt 0 4 frame017scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame017batch07 : batch07.pickTest original frame36=true :=
  FitBatch.pickTest_of_scoped scoped017 frame017scope07

private theorem frameBatches017 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame36)=true := by
  simp only [List.all_cons,List.all_nil,frame017batch00,frame017batch01,frame017batch02,frame017batch03,frame017batch04,frame017batch05,frame017batch06,frame017batch07,Bool.and_self]

theorem frameOK017 : frameRankTest original useStop frame36=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches017


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
