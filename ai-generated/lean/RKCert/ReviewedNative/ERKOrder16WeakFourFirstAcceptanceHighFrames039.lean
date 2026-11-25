module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK078 : stripTest frame160=true := by decide +kernel

theorem spanOK078 : checkChain 1864 1856 [frame160.span]=true := by decide +kernel

private theorem guideAt078 : List.lookup frame160.span.1 guideTable=some guide078 := by
  decide +kernel

private theorem scoped078 : original.guide frame160.span.1 =
    (fun z => List.lookup (guideCode z) guide078) := by
  funext z
  change (List.lookup frame160.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide078
  simp only [guideAt078,Option.bind_some]

private abbrev frame078test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch00.stop,F)

private theorem frame078scope00_s000 : ((fits00.drop 0).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s004 : ((fits00.drop 4).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s008 : ((fits00.drop 8).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s012 : ((fits00.drop 12).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s016 : ((fits00.drop 16).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s020 : ((fits00.drop 20).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s024 : ((fits00.drop 24).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s028 : ((fits00.drop 28).take 4).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_s032 : ((fits00.drop 32).take 3).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00_end : (fits00.drop 35).all frame078test00=true := by
  decide +kernel

private theorem frame078scope00 : fits00.all frame078test00=true := by
  have h32 := stitchAt 32 3 frame078scope00_s032 frame078scope00_end
  have h28 := stitchAt 28 4 frame078scope00_s028 h32
  have h24 := stitchAt 24 4 frame078scope00_s024 h28
  have h20 := stitchAt 20 4 frame078scope00_s020 h24
  have h16 := stitchAt 16 4 frame078scope00_s016 h20
  have h12 := stitchAt 12 4 frame078scope00_s012 h16
  have h8 := stitchAt 8 4 frame078scope00_s008 h12
  have h4 := stitchAt 4 4 frame078scope00_s004 h8
  have h0 := stitchAt 0 4 frame078scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch00 : batch00.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope00

private abbrev frame078test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch01.stop,F)

private theorem frame078scope01_s000 : ((fits01.drop 0).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s004 : ((fits01.drop 4).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s008 : ((fits01.drop 8).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s012 : ((fits01.drop 12).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s016 : ((fits01.drop 16).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s020 : ((fits01.drop 20).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s024 : ((fits01.drop 24).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s028 : ((fits01.drop 28).take 4).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_s032 : ((fits01.drop 32).take 3).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01_end : (fits01.drop 35).all frame078test01=true := by
  decide +kernel

private theorem frame078scope01 : fits01.all frame078test01=true := by
  have h32 := stitchAt 32 3 frame078scope01_s032 frame078scope01_end
  have h28 := stitchAt 28 4 frame078scope01_s028 h32
  have h24 := stitchAt 24 4 frame078scope01_s024 h28
  have h20 := stitchAt 20 4 frame078scope01_s020 h24
  have h16 := stitchAt 16 4 frame078scope01_s016 h20
  have h12 := stitchAt 12 4 frame078scope01_s012 h16
  have h8 := stitchAt 8 4 frame078scope01_s008 h12
  have h4 := stitchAt 4 4 frame078scope01_s004 h8
  have h0 := stitchAt 0 4 frame078scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch01 : batch01.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope01

private abbrev frame078test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch02.stop,F)

private theorem frame078scope02_s000 : ((fits02.drop 0).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s004 : ((fits02.drop 4).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s008 : ((fits02.drop 8).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s012 : ((fits02.drop 12).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s016 : ((fits02.drop 16).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s020 : ((fits02.drop 20).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s024 : ((fits02.drop 24).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s028 : ((fits02.drop 28).take 4).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_s032 : ((fits02.drop 32).take 3).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02_end : (fits02.drop 35).all frame078test02=true := by
  decide +kernel

private theorem frame078scope02 : fits02.all frame078test02=true := by
  have h32 := stitchAt 32 3 frame078scope02_s032 frame078scope02_end
  have h28 := stitchAt 28 4 frame078scope02_s028 h32
  have h24 := stitchAt 24 4 frame078scope02_s024 h28
  have h20 := stitchAt 20 4 frame078scope02_s020 h24
  have h16 := stitchAt 16 4 frame078scope02_s016 h20
  have h12 := stitchAt 12 4 frame078scope02_s012 h16
  have h8 := stitchAt 8 4 frame078scope02_s008 h12
  have h4 := stitchAt 4 4 frame078scope02_s004 h8
  have h0 := stitchAt 0 4 frame078scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch02 : batch02.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope02

private abbrev frame078test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch03.stop,F)

private theorem frame078scope03_s000 : ((fits03.drop 0).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s004 : ((fits03.drop 4).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s008 : ((fits03.drop 8).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s012 : ((fits03.drop 12).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s016 : ((fits03.drop 16).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s020 : ((fits03.drop 20).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s024 : ((fits03.drop 24).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s028 : ((fits03.drop 28).take 4).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_s032 : ((fits03.drop 32).take 3).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03_end : (fits03.drop 35).all frame078test03=true := by
  decide +kernel

private theorem frame078scope03 : fits03.all frame078test03=true := by
  have h32 := stitchAt 32 3 frame078scope03_s032 frame078scope03_end
  have h28 := stitchAt 28 4 frame078scope03_s028 h32
  have h24 := stitchAt 24 4 frame078scope03_s024 h28
  have h20 := stitchAt 20 4 frame078scope03_s020 h24
  have h16 := stitchAt 16 4 frame078scope03_s016 h20
  have h12 := stitchAt 12 4 frame078scope03_s012 h16
  have h8 := stitchAt 8 4 frame078scope03_s008 h12
  have h4 := stitchAt 4 4 frame078scope03_s004 h8
  have h0 := stitchAt 0 4 frame078scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch03 : batch03.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope03

private abbrev frame078test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch04.stop,F)

private theorem frame078scope04_s000 : ((fits04.drop 0).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s004 : ((fits04.drop 4).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s008 : ((fits04.drop 8).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s012 : ((fits04.drop 12).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s016 : ((fits04.drop 16).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s020 : ((fits04.drop 20).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s024 : ((fits04.drop 24).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s028 : ((fits04.drop 28).take 4).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_s032 : ((fits04.drop 32).take 3).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04_end : (fits04.drop 35).all frame078test04=true := by
  decide +kernel

private theorem frame078scope04 : fits04.all frame078test04=true := by
  have h32 := stitchAt 32 3 frame078scope04_s032 frame078scope04_end
  have h28 := stitchAt 28 4 frame078scope04_s028 h32
  have h24 := stitchAt 24 4 frame078scope04_s024 h28
  have h20 := stitchAt 20 4 frame078scope04_s020 h24
  have h16 := stitchAt 16 4 frame078scope04_s016 h20
  have h12 := stitchAt 12 4 frame078scope04_s012 h16
  have h8 := stitchAt 8 4 frame078scope04_s008 h12
  have h4 := stitchAt 4 4 frame078scope04_s004 h8
  have h0 := stitchAt 0 4 frame078scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch04 : batch04.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope04

private abbrev frame078test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch05.stop,F)

private theorem frame078scope05_s000 : ((fits05.drop 0).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s004 : ((fits05.drop 4).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s008 : ((fits05.drop 8).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s012 : ((fits05.drop 12).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s016 : ((fits05.drop 16).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s020 : ((fits05.drop 20).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s024 : ((fits05.drop 24).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s028 : ((fits05.drop 28).take 4).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_s032 : ((fits05.drop 32).take 3).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05_end : (fits05.drop 35).all frame078test05=true := by
  decide +kernel

private theorem frame078scope05 : fits05.all frame078test05=true := by
  have h32 := stitchAt 32 3 frame078scope05_s032 frame078scope05_end
  have h28 := stitchAt 28 4 frame078scope05_s028 h32
  have h24 := stitchAt 24 4 frame078scope05_s024 h28
  have h20 := stitchAt 20 4 frame078scope05_s020 h24
  have h16 := stitchAt 16 4 frame078scope05_s016 h20
  have h12 := stitchAt 12 4 frame078scope05_s012 h16
  have h8 := stitchAt 8 4 frame078scope05_s008 h12
  have h4 := stitchAt 4 4 frame078scope05_s004 h8
  have h0 := stitchAt 0 4 frame078scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch05 : batch05.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope05

private abbrev frame078test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch06.stop,F)

private theorem frame078scope06_s000 : ((fits06.drop 0).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s004 : ((fits06.drop 4).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s008 : ((fits06.drop 8).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s012 : ((fits06.drop 12).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s016 : ((fits06.drop 16).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s020 : ((fits06.drop 20).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s024 : ((fits06.drop 24).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s028 : ((fits06.drop 28).take 4).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_s032 : ((fits06.drop 32).take 3).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06_end : (fits06.drop 35).all frame078test06=true := by
  decide +kernel

private theorem frame078scope06 : fits06.all frame078test06=true := by
  have h32 := stitchAt 32 3 frame078scope06_s032 frame078scope06_end
  have h28 := stitchAt 28 4 frame078scope06_s028 h32
  have h24 := stitchAt 24 4 frame078scope06_s024 h28
  have h20 := stitchAt 20 4 frame078scope06_s020 h24
  have h16 := stitchAt 16 4 frame078scope06_s016 h20
  have h12 := stitchAt 12 4 frame078scope06_s012 h16
  have h8 := stitchAt 8 4 frame078scope06_s008 h12
  have h4 := stitchAt 4 4 frame078scope06_s004 h8
  have h0 := stitchAt 0 4 frame078scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch06 : batch06.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope06

private abbrev frame078test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame160 (fun z => List.lookup (guideCode z) guide078)
    (batch07.stop,F)

private theorem frame078scope07_s000 : ((fits07.drop 0).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s004 : ((fits07.drop 4).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s008 : ((fits07.drop 8).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s012 : ((fits07.drop 12).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s016 : ((fits07.drop 16).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s020 : ((fits07.drop 20).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s024 : ((fits07.drop 24).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s028 : ((fits07.drop 28).take 4).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_s032 : ((fits07.drop 32).take 3).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07_end : (fits07.drop 35).all frame078test07=true := by
  decide +kernel

private theorem frame078scope07 : fits07.all frame078test07=true := by
  have h32 := stitchAt 32 3 frame078scope07_s032 frame078scope07_end
  have h28 := stitchAt 28 4 frame078scope07_s028 h32
  have h24 := stitchAt 24 4 frame078scope07_s024 h28
  have h20 := stitchAt 20 4 frame078scope07_s020 h24
  have h16 := stitchAt 16 4 frame078scope07_s016 h20
  have h12 := stitchAt 12 4 frame078scope07_s012 h16
  have h8 := stitchAt 8 4 frame078scope07_s008 h12
  have h4 := stitchAt 4 4 frame078scope07_s004 h8
  have h0 := stitchAt 0 4 frame078scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame078batch07 : batch07.pickTest original frame160=true :=
  FitBatch.pickTest_of_scoped scoped078 frame078scope07

private theorem frameBatches078 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame160)=true := by
  simp only [List.all_cons,List.all_nil,frame078batch00,frame078batch01,frame078batch02,frame078batch03,frame078batch04,frame078batch05,frame078batch06,frame078batch07,Bool.and_self]

theorem frameOK078 : frameRankTest original useStop frame160=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches078

theorem stripOK079 : stripTest frame161=true := by decide +kernel

theorem spanOK079 : checkChain 1872 1864 [frame161.span]=true := by decide +kernel

private theorem guideAt079 : List.lookup frame161.span.1 guideTable=some guide079 := by
  decide +kernel

private theorem scoped079 : original.guide frame161.span.1 =
    (fun z => List.lookup (guideCode z) guide079) := by
  funext z
  change (List.lookup frame161.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide079
  simp only [guideAt079,Option.bind_some]

private abbrev frame079test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch00.stop,F)

private theorem frame079scope00_s000 : ((fits00.drop 0).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s004 : ((fits00.drop 4).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s008 : ((fits00.drop 8).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s012 : ((fits00.drop 12).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s016 : ((fits00.drop 16).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s020 : ((fits00.drop 20).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s024 : ((fits00.drop 24).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s028 : ((fits00.drop 28).take 4).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_s032 : ((fits00.drop 32).take 3).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00_end : (fits00.drop 35).all frame079test00=true := by
  decide +kernel

private theorem frame079scope00 : fits00.all frame079test00=true := by
  have h32 := stitchAt 32 3 frame079scope00_s032 frame079scope00_end
  have h28 := stitchAt 28 4 frame079scope00_s028 h32
  have h24 := stitchAt 24 4 frame079scope00_s024 h28
  have h20 := stitchAt 20 4 frame079scope00_s020 h24
  have h16 := stitchAt 16 4 frame079scope00_s016 h20
  have h12 := stitchAt 12 4 frame079scope00_s012 h16
  have h8 := stitchAt 8 4 frame079scope00_s008 h12
  have h4 := stitchAt 4 4 frame079scope00_s004 h8
  have h0 := stitchAt 0 4 frame079scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch00 : batch00.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope00

private abbrev frame079test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch01.stop,F)

private theorem frame079scope01_s000 : ((fits01.drop 0).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s004 : ((fits01.drop 4).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s008 : ((fits01.drop 8).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s012 : ((fits01.drop 12).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s016 : ((fits01.drop 16).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s020 : ((fits01.drop 20).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s024 : ((fits01.drop 24).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s028 : ((fits01.drop 28).take 4).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_s032 : ((fits01.drop 32).take 3).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01_end : (fits01.drop 35).all frame079test01=true := by
  decide +kernel

private theorem frame079scope01 : fits01.all frame079test01=true := by
  have h32 := stitchAt 32 3 frame079scope01_s032 frame079scope01_end
  have h28 := stitchAt 28 4 frame079scope01_s028 h32
  have h24 := stitchAt 24 4 frame079scope01_s024 h28
  have h20 := stitchAt 20 4 frame079scope01_s020 h24
  have h16 := stitchAt 16 4 frame079scope01_s016 h20
  have h12 := stitchAt 12 4 frame079scope01_s012 h16
  have h8 := stitchAt 8 4 frame079scope01_s008 h12
  have h4 := stitchAt 4 4 frame079scope01_s004 h8
  have h0 := stitchAt 0 4 frame079scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch01 : batch01.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope01

private abbrev frame079test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch02.stop,F)

private theorem frame079scope02_s000 : ((fits02.drop 0).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s004 : ((fits02.drop 4).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s008 : ((fits02.drop 8).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s012 : ((fits02.drop 12).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s016 : ((fits02.drop 16).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s020 : ((fits02.drop 20).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s024 : ((fits02.drop 24).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s028 : ((fits02.drop 28).take 4).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_s032 : ((fits02.drop 32).take 3).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02_end : (fits02.drop 35).all frame079test02=true := by
  decide +kernel

private theorem frame079scope02 : fits02.all frame079test02=true := by
  have h32 := stitchAt 32 3 frame079scope02_s032 frame079scope02_end
  have h28 := stitchAt 28 4 frame079scope02_s028 h32
  have h24 := stitchAt 24 4 frame079scope02_s024 h28
  have h20 := stitchAt 20 4 frame079scope02_s020 h24
  have h16 := stitchAt 16 4 frame079scope02_s016 h20
  have h12 := stitchAt 12 4 frame079scope02_s012 h16
  have h8 := stitchAt 8 4 frame079scope02_s008 h12
  have h4 := stitchAt 4 4 frame079scope02_s004 h8
  have h0 := stitchAt 0 4 frame079scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch02 : batch02.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope02

private abbrev frame079test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch03.stop,F)

private theorem frame079scope03_s000 : ((fits03.drop 0).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s004 : ((fits03.drop 4).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s008 : ((fits03.drop 8).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s012 : ((fits03.drop 12).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s016 : ((fits03.drop 16).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s020 : ((fits03.drop 20).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s024 : ((fits03.drop 24).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s028 : ((fits03.drop 28).take 4).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_s032 : ((fits03.drop 32).take 3).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03_end : (fits03.drop 35).all frame079test03=true := by
  decide +kernel

private theorem frame079scope03 : fits03.all frame079test03=true := by
  have h32 := stitchAt 32 3 frame079scope03_s032 frame079scope03_end
  have h28 := stitchAt 28 4 frame079scope03_s028 h32
  have h24 := stitchAt 24 4 frame079scope03_s024 h28
  have h20 := stitchAt 20 4 frame079scope03_s020 h24
  have h16 := stitchAt 16 4 frame079scope03_s016 h20
  have h12 := stitchAt 12 4 frame079scope03_s012 h16
  have h8 := stitchAt 8 4 frame079scope03_s008 h12
  have h4 := stitchAt 4 4 frame079scope03_s004 h8
  have h0 := stitchAt 0 4 frame079scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch03 : batch03.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope03

private abbrev frame079test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch04.stop,F)

private theorem frame079scope04_s000 : ((fits04.drop 0).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s004 : ((fits04.drop 4).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s008 : ((fits04.drop 8).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s012 : ((fits04.drop 12).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s016 : ((fits04.drop 16).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s020 : ((fits04.drop 20).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s024 : ((fits04.drop 24).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s028 : ((fits04.drop 28).take 4).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_s032 : ((fits04.drop 32).take 3).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04_end : (fits04.drop 35).all frame079test04=true := by
  decide +kernel

private theorem frame079scope04 : fits04.all frame079test04=true := by
  have h32 := stitchAt 32 3 frame079scope04_s032 frame079scope04_end
  have h28 := stitchAt 28 4 frame079scope04_s028 h32
  have h24 := stitchAt 24 4 frame079scope04_s024 h28
  have h20 := stitchAt 20 4 frame079scope04_s020 h24
  have h16 := stitchAt 16 4 frame079scope04_s016 h20
  have h12 := stitchAt 12 4 frame079scope04_s012 h16
  have h8 := stitchAt 8 4 frame079scope04_s008 h12
  have h4 := stitchAt 4 4 frame079scope04_s004 h8
  have h0 := stitchAt 0 4 frame079scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch04 : batch04.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope04

private abbrev frame079test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch05.stop,F)

private theorem frame079scope05_s000 : ((fits05.drop 0).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s004 : ((fits05.drop 4).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s008 : ((fits05.drop 8).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s012 : ((fits05.drop 12).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s016 : ((fits05.drop 16).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s020 : ((fits05.drop 20).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s024 : ((fits05.drop 24).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s028 : ((fits05.drop 28).take 4).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_s032 : ((fits05.drop 32).take 3).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05_end : (fits05.drop 35).all frame079test05=true := by
  decide +kernel

private theorem frame079scope05 : fits05.all frame079test05=true := by
  have h32 := stitchAt 32 3 frame079scope05_s032 frame079scope05_end
  have h28 := stitchAt 28 4 frame079scope05_s028 h32
  have h24 := stitchAt 24 4 frame079scope05_s024 h28
  have h20 := stitchAt 20 4 frame079scope05_s020 h24
  have h16 := stitchAt 16 4 frame079scope05_s016 h20
  have h12 := stitchAt 12 4 frame079scope05_s012 h16
  have h8 := stitchAt 8 4 frame079scope05_s008 h12
  have h4 := stitchAt 4 4 frame079scope05_s004 h8
  have h0 := stitchAt 0 4 frame079scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch05 : batch05.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope05

private abbrev frame079test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch06.stop,F)

private theorem frame079scope06_s000 : ((fits06.drop 0).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s004 : ((fits06.drop 4).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s008 : ((fits06.drop 8).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s012 : ((fits06.drop 12).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s016 : ((fits06.drop 16).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s020 : ((fits06.drop 20).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s024 : ((fits06.drop 24).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s028 : ((fits06.drop 28).take 4).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_s032 : ((fits06.drop 32).take 3).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06_end : (fits06.drop 35).all frame079test06=true := by
  decide +kernel

private theorem frame079scope06 : fits06.all frame079test06=true := by
  have h32 := stitchAt 32 3 frame079scope06_s032 frame079scope06_end
  have h28 := stitchAt 28 4 frame079scope06_s028 h32
  have h24 := stitchAt 24 4 frame079scope06_s024 h28
  have h20 := stitchAt 20 4 frame079scope06_s020 h24
  have h16 := stitchAt 16 4 frame079scope06_s016 h20
  have h12 := stitchAt 12 4 frame079scope06_s012 h16
  have h8 := stitchAt 8 4 frame079scope06_s008 h12
  have h4 := stitchAt 4 4 frame079scope06_s004 h8
  have h0 := stitchAt 0 4 frame079scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch06 : batch06.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope06

private abbrev frame079test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame161 (fun z => List.lookup (guideCode z) guide079)
    (batch07.stop,F)

private theorem frame079scope07_s000 : ((fits07.drop 0).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s004 : ((fits07.drop 4).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s008 : ((fits07.drop 8).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s012 : ((fits07.drop 12).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s016 : ((fits07.drop 16).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s020 : ((fits07.drop 20).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s024 : ((fits07.drop 24).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s028 : ((fits07.drop 28).take 4).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_s032 : ((fits07.drop 32).take 3).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07_end : (fits07.drop 35).all frame079test07=true := by
  decide +kernel

private theorem frame079scope07 : fits07.all frame079test07=true := by
  have h32 := stitchAt 32 3 frame079scope07_s032 frame079scope07_end
  have h28 := stitchAt 28 4 frame079scope07_s028 h32
  have h24 := stitchAt 24 4 frame079scope07_s024 h28
  have h20 := stitchAt 20 4 frame079scope07_s020 h24
  have h16 := stitchAt 16 4 frame079scope07_s016 h20
  have h12 := stitchAt 12 4 frame079scope07_s012 h16
  have h8 := stitchAt 8 4 frame079scope07_s008 h12
  have h4 := stitchAt 4 4 frame079scope07_s004 h8
  have h0 := stitchAt 0 4 frame079scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame079batch07 : batch07.pickTest original frame161=true :=
  FitBatch.pickTest_of_scoped scoped079 frame079scope07

private theorem frameBatches079 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame161)=true := by
  simp only [List.all_cons,List.all_nil,frame079batch00,frame079batch01,frame079batch02,frame079batch03,frame079batch04,frame079batch05,frame079batch06,frame079batch07,Bool.and_self]

theorem frameOK079 : frameRankTest original useStop frame161=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches079


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
