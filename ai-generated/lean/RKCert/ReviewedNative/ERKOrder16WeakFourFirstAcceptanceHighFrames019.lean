module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK038 : stripTest frame81=true := by decide +kernel

theorem spanOK038 : checkChain 1732 1728 [frame81.span]=true := by decide +kernel

private theorem guideAt038 : List.lookup frame81.span.1 guideTable=some guide038 := by
  decide +kernel

private theorem scoped038 : original.guide frame81.span.1 =
    (fun z => List.lookup (guideCode z) guide038) := by
  funext z
  change (List.lookup frame81.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide038
  simp only [guideAt038,Option.bind_some]

private abbrev frame038test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch00.stop,F)

private theorem frame038scope00_s000 : ((fits00.drop 0).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s004 : ((fits00.drop 4).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s008 : ((fits00.drop 8).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s012 : ((fits00.drop 12).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s016 : ((fits00.drop 16).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s020 : ((fits00.drop 20).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s024 : ((fits00.drop 24).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s028 : ((fits00.drop 28).take 4).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_s032 : ((fits00.drop 32).take 3).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00_end : (fits00.drop 35).all frame038test00=true := by
  decide +kernel

private theorem frame038scope00 : fits00.all frame038test00=true := by
  have h32 := stitchAt 32 3 frame038scope00_s032 frame038scope00_end
  have h28 := stitchAt 28 4 frame038scope00_s028 h32
  have h24 := stitchAt 24 4 frame038scope00_s024 h28
  have h20 := stitchAt 20 4 frame038scope00_s020 h24
  have h16 := stitchAt 16 4 frame038scope00_s016 h20
  have h12 := stitchAt 12 4 frame038scope00_s012 h16
  have h8 := stitchAt 8 4 frame038scope00_s008 h12
  have h4 := stitchAt 4 4 frame038scope00_s004 h8
  have h0 := stitchAt 0 4 frame038scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch00 : batch00.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope00

private abbrev frame038test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch01.stop,F)

private theorem frame038scope01_s000 : ((fits01.drop 0).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s004 : ((fits01.drop 4).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s008 : ((fits01.drop 8).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s012 : ((fits01.drop 12).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s016 : ((fits01.drop 16).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s020 : ((fits01.drop 20).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s024 : ((fits01.drop 24).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s028 : ((fits01.drop 28).take 4).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_s032 : ((fits01.drop 32).take 3).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01_end : (fits01.drop 35).all frame038test01=true := by
  decide +kernel

private theorem frame038scope01 : fits01.all frame038test01=true := by
  have h32 := stitchAt 32 3 frame038scope01_s032 frame038scope01_end
  have h28 := stitchAt 28 4 frame038scope01_s028 h32
  have h24 := stitchAt 24 4 frame038scope01_s024 h28
  have h20 := stitchAt 20 4 frame038scope01_s020 h24
  have h16 := stitchAt 16 4 frame038scope01_s016 h20
  have h12 := stitchAt 12 4 frame038scope01_s012 h16
  have h8 := stitchAt 8 4 frame038scope01_s008 h12
  have h4 := stitchAt 4 4 frame038scope01_s004 h8
  have h0 := stitchAt 0 4 frame038scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch01 : batch01.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope01

private abbrev frame038test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch02.stop,F)

private theorem frame038scope02_s000 : ((fits02.drop 0).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s004 : ((fits02.drop 4).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s008 : ((fits02.drop 8).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s012 : ((fits02.drop 12).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s016 : ((fits02.drop 16).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s020 : ((fits02.drop 20).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s024 : ((fits02.drop 24).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s028 : ((fits02.drop 28).take 4).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_s032 : ((fits02.drop 32).take 3).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02_end : (fits02.drop 35).all frame038test02=true := by
  decide +kernel

private theorem frame038scope02 : fits02.all frame038test02=true := by
  have h32 := stitchAt 32 3 frame038scope02_s032 frame038scope02_end
  have h28 := stitchAt 28 4 frame038scope02_s028 h32
  have h24 := stitchAt 24 4 frame038scope02_s024 h28
  have h20 := stitchAt 20 4 frame038scope02_s020 h24
  have h16 := stitchAt 16 4 frame038scope02_s016 h20
  have h12 := stitchAt 12 4 frame038scope02_s012 h16
  have h8 := stitchAt 8 4 frame038scope02_s008 h12
  have h4 := stitchAt 4 4 frame038scope02_s004 h8
  have h0 := stitchAt 0 4 frame038scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch02 : batch02.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope02

private abbrev frame038test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch03.stop,F)

private theorem frame038scope03_s000 : ((fits03.drop 0).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s004 : ((fits03.drop 4).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s008 : ((fits03.drop 8).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s012 : ((fits03.drop 12).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s016 : ((fits03.drop 16).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s020 : ((fits03.drop 20).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s024 : ((fits03.drop 24).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s028 : ((fits03.drop 28).take 4).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_s032 : ((fits03.drop 32).take 3).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03_end : (fits03.drop 35).all frame038test03=true := by
  decide +kernel

private theorem frame038scope03 : fits03.all frame038test03=true := by
  have h32 := stitchAt 32 3 frame038scope03_s032 frame038scope03_end
  have h28 := stitchAt 28 4 frame038scope03_s028 h32
  have h24 := stitchAt 24 4 frame038scope03_s024 h28
  have h20 := stitchAt 20 4 frame038scope03_s020 h24
  have h16 := stitchAt 16 4 frame038scope03_s016 h20
  have h12 := stitchAt 12 4 frame038scope03_s012 h16
  have h8 := stitchAt 8 4 frame038scope03_s008 h12
  have h4 := stitchAt 4 4 frame038scope03_s004 h8
  have h0 := stitchAt 0 4 frame038scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch03 : batch03.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope03

private abbrev frame038test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch04.stop,F)

private theorem frame038scope04_s000 : ((fits04.drop 0).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s004 : ((fits04.drop 4).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s008 : ((fits04.drop 8).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s012 : ((fits04.drop 12).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s016 : ((fits04.drop 16).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s020 : ((fits04.drop 20).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s024 : ((fits04.drop 24).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s028 : ((fits04.drop 28).take 4).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_s032 : ((fits04.drop 32).take 3).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04_end : (fits04.drop 35).all frame038test04=true := by
  decide +kernel

private theorem frame038scope04 : fits04.all frame038test04=true := by
  have h32 := stitchAt 32 3 frame038scope04_s032 frame038scope04_end
  have h28 := stitchAt 28 4 frame038scope04_s028 h32
  have h24 := stitchAt 24 4 frame038scope04_s024 h28
  have h20 := stitchAt 20 4 frame038scope04_s020 h24
  have h16 := stitchAt 16 4 frame038scope04_s016 h20
  have h12 := stitchAt 12 4 frame038scope04_s012 h16
  have h8 := stitchAt 8 4 frame038scope04_s008 h12
  have h4 := stitchAt 4 4 frame038scope04_s004 h8
  have h0 := stitchAt 0 4 frame038scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch04 : batch04.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope04

private abbrev frame038test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch05.stop,F)

private theorem frame038scope05_s000 : ((fits05.drop 0).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s004 : ((fits05.drop 4).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s008 : ((fits05.drop 8).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s012 : ((fits05.drop 12).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s016 : ((fits05.drop 16).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s020 : ((fits05.drop 20).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s024 : ((fits05.drop 24).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s028 : ((fits05.drop 28).take 4).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_s032 : ((fits05.drop 32).take 3).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05_end : (fits05.drop 35).all frame038test05=true := by
  decide +kernel

private theorem frame038scope05 : fits05.all frame038test05=true := by
  have h32 := stitchAt 32 3 frame038scope05_s032 frame038scope05_end
  have h28 := stitchAt 28 4 frame038scope05_s028 h32
  have h24 := stitchAt 24 4 frame038scope05_s024 h28
  have h20 := stitchAt 20 4 frame038scope05_s020 h24
  have h16 := stitchAt 16 4 frame038scope05_s016 h20
  have h12 := stitchAt 12 4 frame038scope05_s012 h16
  have h8 := stitchAt 8 4 frame038scope05_s008 h12
  have h4 := stitchAt 4 4 frame038scope05_s004 h8
  have h0 := stitchAt 0 4 frame038scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch05 : batch05.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope05

private abbrev frame038test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch06.stop,F)

private theorem frame038scope06_s000 : ((fits06.drop 0).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s004 : ((fits06.drop 4).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s008 : ((fits06.drop 8).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s012 : ((fits06.drop 12).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s016 : ((fits06.drop 16).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s020 : ((fits06.drop 20).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s024 : ((fits06.drop 24).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s028 : ((fits06.drop 28).take 4).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_s032 : ((fits06.drop 32).take 3).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06_end : (fits06.drop 35).all frame038test06=true := by
  decide +kernel

private theorem frame038scope06 : fits06.all frame038test06=true := by
  have h32 := stitchAt 32 3 frame038scope06_s032 frame038scope06_end
  have h28 := stitchAt 28 4 frame038scope06_s028 h32
  have h24 := stitchAt 24 4 frame038scope06_s024 h28
  have h20 := stitchAt 20 4 frame038scope06_s020 h24
  have h16 := stitchAt 16 4 frame038scope06_s016 h20
  have h12 := stitchAt 12 4 frame038scope06_s012 h16
  have h8 := stitchAt 8 4 frame038scope06_s008 h12
  have h4 := stitchAt 4 4 frame038scope06_s004 h8
  have h0 := stitchAt 0 4 frame038scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch06 : batch06.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope06

private abbrev frame038test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame81 (fun z => List.lookup (guideCode z) guide038)
    (batch07.stop,F)

private theorem frame038scope07_s000 : ((fits07.drop 0).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s004 : ((fits07.drop 4).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s008 : ((fits07.drop 8).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s012 : ((fits07.drop 12).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s016 : ((fits07.drop 16).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s020 : ((fits07.drop 20).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s024 : ((fits07.drop 24).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s028 : ((fits07.drop 28).take 4).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_s032 : ((fits07.drop 32).take 3).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07_end : (fits07.drop 35).all frame038test07=true := by
  decide +kernel

private theorem frame038scope07 : fits07.all frame038test07=true := by
  have h32 := stitchAt 32 3 frame038scope07_s032 frame038scope07_end
  have h28 := stitchAt 28 4 frame038scope07_s028 h32
  have h24 := stitchAt 24 4 frame038scope07_s024 h28
  have h20 := stitchAt 20 4 frame038scope07_s020 h24
  have h16 := stitchAt 16 4 frame038scope07_s016 h20
  have h12 := stitchAt 12 4 frame038scope07_s012 h16
  have h8 := stitchAt 8 4 frame038scope07_s008 h12
  have h4 := stitchAt 4 4 frame038scope07_s004 h8
  have h0 := stitchAt 0 4 frame038scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame038batch07 : batch07.pickTest original frame81=true :=
  FitBatch.pickTest_of_scoped scoped038 frame038scope07

private theorem frameBatches038 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame81)=true := by
  simp only [List.all_cons,List.all_nil,frame038batch00,frame038batch01,frame038batch02,frame038batch03,frame038batch04,frame038batch05,frame038batch06,frame038batch07,Bool.and_self]

theorem frameOK038 : frameRankTest original useStop frame81=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches038

theorem stripOK039 : stripTest frame82=true := by decide +kernel

theorem spanOK039 : checkChain 1736 1732 [frame82.span]=true := by decide +kernel

private theorem guideAt039 : List.lookup frame82.span.1 guideTable=some guide039 := by
  decide +kernel

private theorem scoped039 : original.guide frame82.span.1 =
    (fun z => List.lookup (guideCode z) guide039) := by
  funext z
  change (List.lookup frame82.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide039
  simp only [guideAt039,Option.bind_some]

private abbrev frame039test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch00.stop,F)

private theorem frame039scope00_s000 : ((fits00.drop 0).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s004 : ((fits00.drop 4).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s008 : ((fits00.drop 8).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s012 : ((fits00.drop 12).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s016 : ((fits00.drop 16).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s020 : ((fits00.drop 20).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s024 : ((fits00.drop 24).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s028 : ((fits00.drop 28).take 4).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_s032 : ((fits00.drop 32).take 3).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00_end : (fits00.drop 35).all frame039test00=true := by
  decide +kernel

private theorem frame039scope00 : fits00.all frame039test00=true := by
  have h32 := stitchAt 32 3 frame039scope00_s032 frame039scope00_end
  have h28 := stitchAt 28 4 frame039scope00_s028 h32
  have h24 := stitchAt 24 4 frame039scope00_s024 h28
  have h20 := stitchAt 20 4 frame039scope00_s020 h24
  have h16 := stitchAt 16 4 frame039scope00_s016 h20
  have h12 := stitchAt 12 4 frame039scope00_s012 h16
  have h8 := stitchAt 8 4 frame039scope00_s008 h12
  have h4 := stitchAt 4 4 frame039scope00_s004 h8
  have h0 := stitchAt 0 4 frame039scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch00 : batch00.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope00

private abbrev frame039test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch01.stop,F)

private theorem frame039scope01_s000 : ((fits01.drop 0).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s004 : ((fits01.drop 4).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s008 : ((fits01.drop 8).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s012 : ((fits01.drop 12).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s016 : ((fits01.drop 16).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s020 : ((fits01.drop 20).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s024 : ((fits01.drop 24).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s028 : ((fits01.drop 28).take 4).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_s032 : ((fits01.drop 32).take 3).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01_end : (fits01.drop 35).all frame039test01=true := by
  decide +kernel

private theorem frame039scope01 : fits01.all frame039test01=true := by
  have h32 := stitchAt 32 3 frame039scope01_s032 frame039scope01_end
  have h28 := stitchAt 28 4 frame039scope01_s028 h32
  have h24 := stitchAt 24 4 frame039scope01_s024 h28
  have h20 := stitchAt 20 4 frame039scope01_s020 h24
  have h16 := stitchAt 16 4 frame039scope01_s016 h20
  have h12 := stitchAt 12 4 frame039scope01_s012 h16
  have h8 := stitchAt 8 4 frame039scope01_s008 h12
  have h4 := stitchAt 4 4 frame039scope01_s004 h8
  have h0 := stitchAt 0 4 frame039scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch01 : batch01.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope01

private abbrev frame039test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch02.stop,F)

private theorem frame039scope02_s000 : ((fits02.drop 0).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s004 : ((fits02.drop 4).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s008 : ((fits02.drop 8).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s012 : ((fits02.drop 12).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s016 : ((fits02.drop 16).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s020 : ((fits02.drop 20).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s024 : ((fits02.drop 24).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s028 : ((fits02.drop 28).take 4).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_s032 : ((fits02.drop 32).take 3).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02_end : (fits02.drop 35).all frame039test02=true := by
  decide +kernel

private theorem frame039scope02 : fits02.all frame039test02=true := by
  have h32 := stitchAt 32 3 frame039scope02_s032 frame039scope02_end
  have h28 := stitchAt 28 4 frame039scope02_s028 h32
  have h24 := stitchAt 24 4 frame039scope02_s024 h28
  have h20 := stitchAt 20 4 frame039scope02_s020 h24
  have h16 := stitchAt 16 4 frame039scope02_s016 h20
  have h12 := stitchAt 12 4 frame039scope02_s012 h16
  have h8 := stitchAt 8 4 frame039scope02_s008 h12
  have h4 := stitchAt 4 4 frame039scope02_s004 h8
  have h0 := stitchAt 0 4 frame039scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch02 : batch02.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope02

private abbrev frame039test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch03.stop,F)

private theorem frame039scope03_s000 : ((fits03.drop 0).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s004 : ((fits03.drop 4).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s008 : ((fits03.drop 8).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s012 : ((fits03.drop 12).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s016 : ((fits03.drop 16).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s020 : ((fits03.drop 20).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s024 : ((fits03.drop 24).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s028 : ((fits03.drop 28).take 4).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_s032 : ((fits03.drop 32).take 3).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03_end : (fits03.drop 35).all frame039test03=true := by
  decide +kernel

private theorem frame039scope03 : fits03.all frame039test03=true := by
  have h32 := stitchAt 32 3 frame039scope03_s032 frame039scope03_end
  have h28 := stitchAt 28 4 frame039scope03_s028 h32
  have h24 := stitchAt 24 4 frame039scope03_s024 h28
  have h20 := stitchAt 20 4 frame039scope03_s020 h24
  have h16 := stitchAt 16 4 frame039scope03_s016 h20
  have h12 := stitchAt 12 4 frame039scope03_s012 h16
  have h8 := stitchAt 8 4 frame039scope03_s008 h12
  have h4 := stitchAt 4 4 frame039scope03_s004 h8
  have h0 := stitchAt 0 4 frame039scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch03 : batch03.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope03

private abbrev frame039test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch04.stop,F)

private theorem frame039scope04_s000 : ((fits04.drop 0).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s004 : ((fits04.drop 4).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s008 : ((fits04.drop 8).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s012 : ((fits04.drop 12).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s016 : ((fits04.drop 16).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s020 : ((fits04.drop 20).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s024 : ((fits04.drop 24).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s028 : ((fits04.drop 28).take 4).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_s032 : ((fits04.drop 32).take 3).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04_end : (fits04.drop 35).all frame039test04=true := by
  decide +kernel

private theorem frame039scope04 : fits04.all frame039test04=true := by
  have h32 := stitchAt 32 3 frame039scope04_s032 frame039scope04_end
  have h28 := stitchAt 28 4 frame039scope04_s028 h32
  have h24 := stitchAt 24 4 frame039scope04_s024 h28
  have h20 := stitchAt 20 4 frame039scope04_s020 h24
  have h16 := stitchAt 16 4 frame039scope04_s016 h20
  have h12 := stitchAt 12 4 frame039scope04_s012 h16
  have h8 := stitchAt 8 4 frame039scope04_s008 h12
  have h4 := stitchAt 4 4 frame039scope04_s004 h8
  have h0 := stitchAt 0 4 frame039scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch04 : batch04.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope04

private abbrev frame039test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch05.stop,F)

private theorem frame039scope05_s000 : ((fits05.drop 0).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s004 : ((fits05.drop 4).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s008 : ((fits05.drop 8).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s012 : ((fits05.drop 12).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s016 : ((fits05.drop 16).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s020 : ((fits05.drop 20).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s024 : ((fits05.drop 24).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s028 : ((fits05.drop 28).take 4).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_s032 : ((fits05.drop 32).take 3).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05_end : (fits05.drop 35).all frame039test05=true := by
  decide +kernel

private theorem frame039scope05 : fits05.all frame039test05=true := by
  have h32 := stitchAt 32 3 frame039scope05_s032 frame039scope05_end
  have h28 := stitchAt 28 4 frame039scope05_s028 h32
  have h24 := stitchAt 24 4 frame039scope05_s024 h28
  have h20 := stitchAt 20 4 frame039scope05_s020 h24
  have h16 := stitchAt 16 4 frame039scope05_s016 h20
  have h12 := stitchAt 12 4 frame039scope05_s012 h16
  have h8 := stitchAt 8 4 frame039scope05_s008 h12
  have h4 := stitchAt 4 4 frame039scope05_s004 h8
  have h0 := stitchAt 0 4 frame039scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch05 : batch05.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope05

private abbrev frame039test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch06.stop,F)

private theorem frame039scope06_s000 : ((fits06.drop 0).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s004 : ((fits06.drop 4).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s008 : ((fits06.drop 8).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s012 : ((fits06.drop 12).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s016 : ((fits06.drop 16).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s020 : ((fits06.drop 20).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s024 : ((fits06.drop 24).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s028 : ((fits06.drop 28).take 4).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_s032 : ((fits06.drop 32).take 3).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06_end : (fits06.drop 35).all frame039test06=true := by
  decide +kernel

private theorem frame039scope06 : fits06.all frame039test06=true := by
  have h32 := stitchAt 32 3 frame039scope06_s032 frame039scope06_end
  have h28 := stitchAt 28 4 frame039scope06_s028 h32
  have h24 := stitchAt 24 4 frame039scope06_s024 h28
  have h20 := stitchAt 20 4 frame039scope06_s020 h24
  have h16 := stitchAt 16 4 frame039scope06_s016 h20
  have h12 := stitchAt 12 4 frame039scope06_s012 h16
  have h8 := stitchAt 8 4 frame039scope06_s008 h12
  have h4 := stitchAt 4 4 frame039scope06_s004 h8
  have h0 := stitchAt 0 4 frame039scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch06 : batch06.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope06

private abbrev frame039test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame82 (fun z => List.lookup (guideCode z) guide039)
    (batch07.stop,F)

private theorem frame039scope07_s000 : ((fits07.drop 0).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s004 : ((fits07.drop 4).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s008 : ((fits07.drop 8).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s012 : ((fits07.drop 12).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s016 : ((fits07.drop 16).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s020 : ((fits07.drop 20).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s024 : ((fits07.drop 24).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s028 : ((fits07.drop 28).take 4).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_s032 : ((fits07.drop 32).take 3).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07_end : (fits07.drop 35).all frame039test07=true := by
  decide +kernel

private theorem frame039scope07 : fits07.all frame039test07=true := by
  have h32 := stitchAt 32 3 frame039scope07_s032 frame039scope07_end
  have h28 := stitchAt 28 4 frame039scope07_s028 h32
  have h24 := stitchAt 24 4 frame039scope07_s024 h28
  have h20 := stitchAt 20 4 frame039scope07_s020 h24
  have h16 := stitchAt 16 4 frame039scope07_s016 h20
  have h12 := stitchAt 12 4 frame039scope07_s012 h16
  have h8 := stitchAt 8 4 frame039scope07_s008 h12
  have h4 := stitchAt 4 4 frame039scope07_s004 h8
  have h0 := stitchAt 0 4 frame039scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame039batch07 : batch07.pickTest original frame82=true :=
  FitBatch.pickTest_of_scoped scoped039 frame039scope07

private theorem frameBatches039 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame82)=true := by
  simp only [List.all_cons,List.all_nil,frame039batch00,frame039batch01,frame039batch02,frame039batch03,frame039batch04,frame039batch05,frame039batch06,frame039batch07,Bool.and_self]

theorem frameOK039 : frameRankTest original useStop frame82=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches039


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
