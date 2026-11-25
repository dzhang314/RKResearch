module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksUnit

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
open RKCert.ReviewedNative.WeakFourFirstOnly.DataUnit
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK000 : stripTest frame3=true := by decide +kernel

theorem spanOK000 : checkChain 256 0 [frame3.span]=true := by decide +kernel

private theorem guideAt000 : List.lookup frame3.span.1 guideTable=some guide000 := by
  decide +kernel

private theorem scoped000 : original.guide frame3.span.1 =
    (fun z => List.lookup (guideCode z) guide000) := by
  funext z
  change (List.lookup frame3.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide000
  simp only [guideAt000,Option.bind_some]

private abbrev frame000test00 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch00.stop,F)

private theorem frame000scope00_s000 : ((fits00.drop 0).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s004 : ((fits00.drop 4).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s008 : ((fits00.drop 8).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s012 : ((fits00.drop 12).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s016 : ((fits00.drop 16).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s020 : ((fits00.drop 20).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s024 : ((fits00.drop 24).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s028 : ((fits00.drop 28).take 4).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_s032 : ((fits00.drop 32).take 3).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00_end : (fits00.drop 35).all frame000test00=true := by
  decide +kernel

private theorem frame000scope00 : fits00.all frame000test00=true := by
  have h32 := stitchAt 32 3 frame000scope00_s032 frame000scope00_end
  have h28 := stitchAt 28 4 frame000scope00_s028 h32
  have h24 := stitchAt 24 4 frame000scope00_s024 h28
  have h20 := stitchAt 20 4 frame000scope00_s020 h24
  have h16 := stitchAt 16 4 frame000scope00_s016 h20
  have h12 := stitchAt 12 4 frame000scope00_s012 h16
  have h8 := stitchAt 8 4 frame000scope00_s008 h12
  have h4 := stitchAt 4 4 frame000scope00_s004 h8
  have h0 := stitchAt 0 4 frame000scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch00 : batch00.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope00

private abbrev frame000test01 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch01.stop,F)

private theorem frame000scope01_s000 : ((fits01.drop 0).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s004 : ((fits01.drop 4).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s008 : ((fits01.drop 8).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s012 : ((fits01.drop 12).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s016 : ((fits01.drop 16).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s020 : ((fits01.drop 20).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s024 : ((fits01.drop 24).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s028 : ((fits01.drop 28).take 4).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_s032 : ((fits01.drop 32).take 3).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01_end : (fits01.drop 35).all frame000test01=true := by
  decide +kernel

private theorem frame000scope01 : fits01.all frame000test01=true := by
  have h32 := stitchAt 32 3 frame000scope01_s032 frame000scope01_end
  have h28 := stitchAt 28 4 frame000scope01_s028 h32
  have h24 := stitchAt 24 4 frame000scope01_s024 h28
  have h20 := stitchAt 20 4 frame000scope01_s020 h24
  have h16 := stitchAt 16 4 frame000scope01_s016 h20
  have h12 := stitchAt 12 4 frame000scope01_s012 h16
  have h8 := stitchAt 8 4 frame000scope01_s008 h12
  have h4 := stitchAt 4 4 frame000scope01_s004 h8
  have h0 := stitchAt 0 4 frame000scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch01 : batch01.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope01

private abbrev frame000test02 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch02.stop,F)

private theorem frame000scope02_s000 : ((fits02.drop 0).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s004 : ((fits02.drop 4).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s008 : ((fits02.drop 8).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s012 : ((fits02.drop 12).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s016 : ((fits02.drop 16).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s020 : ((fits02.drop 20).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s024 : ((fits02.drop 24).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s028 : ((fits02.drop 28).take 4).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_s032 : ((fits02.drop 32).take 3).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02_end : (fits02.drop 35).all frame000test02=true := by
  decide +kernel

private theorem frame000scope02 : fits02.all frame000test02=true := by
  have h32 := stitchAt 32 3 frame000scope02_s032 frame000scope02_end
  have h28 := stitchAt 28 4 frame000scope02_s028 h32
  have h24 := stitchAt 24 4 frame000scope02_s024 h28
  have h20 := stitchAt 20 4 frame000scope02_s020 h24
  have h16 := stitchAt 16 4 frame000scope02_s016 h20
  have h12 := stitchAt 12 4 frame000scope02_s012 h16
  have h8 := stitchAt 8 4 frame000scope02_s008 h12
  have h4 := stitchAt 4 4 frame000scope02_s004 h8
  have h0 := stitchAt 0 4 frame000scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch02 : batch02.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope02

private abbrev frame000test03 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch03.stop,F)

private theorem frame000scope03_s000 : ((fits03.drop 0).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s004 : ((fits03.drop 4).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s008 : ((fits03.drop 8).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s012 : ((fits03.drop 12).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s016 : ((fits03.drop 16).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s020 : ((fits03.drop 20).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s024 : ((fits03.drop 24).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s028 : ((fits03.drop 28).take 4).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_s032 : ((fits03.drop 32).take 3).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03_end : (fits03.drop 35).all frame000test03=true := by
  decide +kernel

private theorem frame000scope03 : fits03.all frame000test03=true := by
  have h32 := stitchAt 32 3 frame000scope03_s032 frame000scope03_end
  have h28 := stitchAt 28 4 frame000scope03_s028 h32
  have h24 := stitchAt 24 4 frame000scope03_s024 h28
  have h20 := stitchAt 20 4 frame000scope03_s020 h24
  have h16 := stitchAt 16 4 frame000scope03_s016 h20
  have h12 := stitchAt 12 4 frame000scope03_s012 h16
  have h8 := stitchAt 8 4 frame000scope03_s008 h12
  have h4 := stitchAt 4 4 frame000scope03_s004 h8
  have h0 := stitchAt 0 4 frame000scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch03 : batch03.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope03

private abbrev frame000test04 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch04.stop,F)

private theorem frame000scope04_s000 : ((fits04.drop 0).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s004 : ((fits04.drop 4).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s008 : ((fits04.drop 8).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s012 : ((fits04.drop 12).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s016 : ((fits04.drop 16).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s020 : ((fits04.drop 20).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s024 : ((fits04.drop 24).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s028 : ((fits04.drop 28).take 4).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_s032 : ((fits04.drop 32).take 3).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04_end : (fits04.drop 35).all frame000test04=true := by
  decide +kernel

private theorem frame000scope04 : fits04.all frame000test04=true := by
  have h32 := stitchAt 32 3 frame000scope04_s032 frame000scope04_end
  have h28 := stitchAt 28 4 frame000scope04_s028 h32
  have h24 := stitchAt 24 4 frame000scope04_s024 h28
  have h20 := stitchAt 20 4 frame000scope04_s020 h24
  have h16 := stitchAt 16 4 frame000scope04_s016 h20
  have h12 := stitchAt 12 4 frame000scope04_s012 h16
  have h8 := stitchAt 8 4 frame000scope04_s008 h12
  have h4 := stitchAt 4 4 frame000scope04_s004 h8
  have h0 := stitchAt 0 4 frame000scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch04 : batch04.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope04

private abbrev frame000test05 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch05.stop,F)

private theorem frame000scope05_s000 : ((fits05.drop 0).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s004 : ((fits05.drop 4).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s008 : ((fits05.drop 8).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s012 : ((fits05.drop 12).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s016 : ((fits05.drop 16).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s020 : ((fits05.drop 20).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s024 : ((fits05.drop 24).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s028 : ((fits05.drop 28).take 4).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_s032 : ((fits05.drop 32).take 3).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05_end : (fits05.drop 35).all frame000test05=true := by
  decide +kernel

private theorem frame000scope05 : fits05.all frame000test05=true := by
  have h32 := stitchAt 32 3 frame000scope05_s032 frame000scope05_end
  have h28 := stitchAt 28 4 frame000scope05_s028 h32
  have h24 := stitchAt 24 4 frame000scope05_s024 h28
  have h20 := stitchAt 20 4 frame000scope05_s020 h24
  have h16 := stitchAt 16 4 frame000scope05_s016 h20
  have h12 := stitchAt 12 4 frame000scope05_s012 h16
  have h8 := stitchAt 8 4 frame000scope05_s008 h12
  have h4 := stitchAt 4 4 frame000scope05_s004 h8
  have h0 := stitchAt 0 4 frame000scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch05 : batch05.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope05

private abbrev frame000test06 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch06.stop,F)

private theorem frame000scope06_s000 : ((fits06.drop 0).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s004 : ((fits06.drop 4).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s008 : ((fits06.drop 8).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s012 : ((fits06.drop 12).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s016 : ((fits06.drop 16).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s020 : ((fits06.drop 20).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s024 : ((fits06.drop 24).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s028 : ((fits06.drop 28).take 4).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_s032 : ((fits06.drop 32).take 3).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06_end : (fits06.drop 35).all frame000test06=true := by
  decide +kernel

private theorem frame000scope06 : fits06.all frame000test06=true := by
  have h32 := stitchAt 32 3 frame000scope06_s032 frame000scope06_end
  have h28 := stitchAt 28 4 frame000scope06_s028 h32
  have h24 := stitchAt 24 4 frame000scope06_s024 h28
  have h20 := stitchAt 20 4 frame000scope06_s020 h24
  have h16 := stitchAt 16 4 frame000scope06_s016 h20
  have h12 := stitchAt 12 4 frame000scope06_s012 h16
  have h8 := stitchAt 8 4 frame000scope06_s008 h12
  have h4 := stitchAt 4 4 frame000scope06_s004 h8
  have h0 := stitchAt 0 4 frame000scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch06 : batch06.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope06

private abbrev frame000test07 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame3 (fun z => List.lookup (guideCode z) guide000)
    (batch07.stop,F)

private theorem frame000scope07_s000 : ((fits07.drop 0).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s004 : ((fits07.drop 4).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s008 : ((fits07.drop 8).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s012 : ((fits07.drop 12).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s016 : ((fits07.drop 16).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s020 : ((fits07.drop 20).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s024 : ((fits07.drop 24).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s028 : ((fits07.drop 28).take 4).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_s032 : ((fits07.drop 32).take 3).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07_end : (fits07.drop 35).all frame000test07=true := by
  decide +kernel

private theorem frame000scope07 : fits07.all frame000test07=true := by
  have h32 := stitchAt 32 3 frame000scope07_s032 frame000scope07_end
  have h28 := stitchAt 28 4 frame000scope07_s028 h32
  have h24 := stitchAt 24 4 frame000scope07_s024 h28
  have h20 := stitchAt 20 4 frame000scope07_s020 h24
  have h16 := stitchAt 16 4 frame000scope07_s016 h20
  have h12 := stitchAt 12 4 frame000scope07_s012 h16
  have h8 := stitchAt 8 4 frame000scope07_s008 h12
  have h4 := stitchAt 4 4 frame000scope07_s004 h8
  have h0 := stitchAt 0 4 frame000scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame000batch07 : batch07.pickTest original frame3=true :=
  FitBatch.pickTest_of_scoped scoped000 frame000scope07

private theorem frameBatches000 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame3)=true := by
  simp only [List.all_cons,List.all_nil,frame000batch00,frame000batch01,frame000batch02,frame000batch03,frame000batch04,frame000batch05,frame000batch06,frame000batch07,Bool.and_self]

theorem frameOK000 : frameRankTest original useStop frame3=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches000

theorem stripOK001 : stripTest frame5=true := by decide +kernel

theorem spanOK001 : checkChain 384 256 [frame5.span]=true := by decide +kernel

private theorem guideAt001 : List.lookup frame5.span.1 guideTable=some guide001 := by
  decide +kernel

private theorem scoped001 : original.guide frame5.span.1 =
    (fun z => List.lookup (guideCode z) guide001) := by
  funext z
  change (List.lookup frame5.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide001
  simp only [guideAt001,Option.bind_some]

private abbrev frame001test00 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch00.stop,F)

private theorem frame001scope00_s000 : ((fits00.drop 0).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s004 : ((fits00.drop 4).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s008 : ((fits00.drop 8).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s012 : ((fits00.drop 12).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s016 : ((fits00.drop 16).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s020 : ((fits00.drop 20).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s024 : ((fits00.drop 24).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s028 : ((fits00.drop 28).take 4).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_s032 : ((fits00.drop 32).take 3).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00_end : (fits00.drop 35).all frame001test00=true := by
  decide +kernel

private theorem frame001scope00 : fits00.all frame001test00=true := by
  have h32 := stitchAt 32 3 frame001scope00_s032 frame001scope00_end
  have h28 := stitchAt 28 4 frame001scope00_s028 h32
  have h24 := stitchAt 24 4 frame001scope00_s024 h28
  have h20 := stitchAt 20 4 frame001scope00_s020 h24
  have h16 := stitchAt 16 4 frame001scope00_s016 h20
  have h12 := stitchAt 12 4 frame001scope00_s012 h16
  have h8 := stitchAt 8 4 frame001scope00_s008 h12
  have h4 := stitchAt 4 4 frame001scope00_s004 h8
  have h0 := stitchAt 0 4 frame001scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch00 : batch00.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope00

private abbrev frame001test01 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch01.stop,F)

private theorem frame001scope01_s000 : ((fits01.drop 0).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s004 : ((fits01.drop 4).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s008 : ((fits01.drop 8).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s012 : ((fits01.drop 12).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s016 : ((fits01.drop 16).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s020 : ((fits01.drop 20).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s024 : ((fits01.drop 24).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s028 : ((fits01.drop 28).take 4).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_s032 : ((fits01.drop 32).take 3).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01_end : (fits01.drop 35).all frame001test01=true := by
  decide +kernel

private theorem frame001scope01 : fits01.all frame001test01=true := by
  have h32 := stitchAt 32 3 frame001scope01_s032 frame001scope01_end
  have h28 := stitchAt 28 4 frame001scope01_s028 h32
  have h24 := stitchAt 24 4 frame001scope01_s024 h28
  have h20 := stitchAt 20 4 frame001scope01_s020 h24
  have h16 := stitchAt 16 4 frame001scope01_s016 h20
  have h12 := stitchAt 12 4 frame001scope01_s012 h16
  have h8 := stitchAt 8 4 frame001scope01_s008 h12
  have h4 := stitchAt 4 4 frame001scope01_s004 h8
  have h0 := stitchAt 0 4 frame001scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch01 : batch01.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope01

private abbrev frame001test02 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch02.stop,F)

private theorem frame001scope02_s000 : ((fits02.drop 0).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s004 : ((fits02.drop 4).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s008 : ((fits02.drop 8).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s012 : ((fits02.drop 12).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s016 : ((fits02.drop 16).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s020 : ((fits02.drop 20).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s024 : ((fits02.drop 24).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s028 : ((fits02.drop 28).take 4).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_s032 : ((fits02.drop 32).take 3).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02_end : (fits02.drop 35).all frame001test02=true := by
  decide +kernel

private theorem frame001scope02 : fits02.all frame001test02=true := by
  have h32 := stitchAt 32 3 frame001scope02_s032 frame001scope02_end
  have h28 := stitchAt 28 4 frame001scope02_s028 h32
  have h24 := stitchAt 24 4 frame001scope02_s024 h28
  have h20 := stitchAt 20 4 frame001scope02_s020 h24
  have h16 := stitchAt 16 4 frame001scope02_s016 h20
  have h12 := stitchAt 12 4 frame001scope02_s012 h16
  have h8 := stitchAt 8 4 frame001scope02_s008 h12
  have h4 := stitchAt 4 4 frame001scope02_s004 h8
  have h0 := stitchAt 0 4 frame001scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch02 : batch02.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope02

private abbrev frame001test03 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch03.stop,F)

private theorem frame001scope03_s000 : ((fits03.drop 0).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s004 : ((fits03.drop 4).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s008 : ((fits03.drop 8).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s012 : ((fits03.drop 12).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s016 : ((fits03.drop 16).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s020 : ((fits03.drop 20).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s024 : ((fits03.drop 24).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s028 : ((fits03.drop 28).take 4).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_s032 : ((fits03.drop 32).take 3).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03_end : (fits03.drop 35).all frame001test03=true := by
  decide +kernel

private theorem frame001scope03 : fits03.all frame001test03=true := by
  have h32 := stitchAt 32 3 frame001scope03_s032 frame001scope03_end
  have h28 := stitchAt 28 4 frame001scope03_s028 h32
  have h24 := stitchAt 24 4 frame001scope03_s024 h28
  have h20 := stitchAt 20 4 frame001scope03_s020 h24
  have h16 := stitchAt 16 4 frame001scope03_s016 h20
  have h12 := stitchAt 12 4 frame001scope03_s012 h16
  have h8 := stitchAt 8 4 frame001scope03_s008 h12
  have h4 := stitchAt 4 4 frame001scope03_s004 h8
  have h0 := stitchAt 0 4 frame001scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch03 : batch03.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope03

private abbrev frame001test04 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch04.stop,F)

private theorem frame001scope04_s000 : ((fits04.drop 0).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s004 : ((fits04.drop 4).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s008 : ((fits04.drop 8).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s012 : ((fits04.drop 12).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s016 : ((fits04.drop 16).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s020 : ((fits04.drop 20).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s024 : ((fits04.drop 24).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s028 : ((fits04.drop 28).take 4).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_s032 : ((fits04.drop 32).take 3).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04_end : (fits04.drop 35).all frame001test04=true := by
  decide +kernel

private theorem frame001scope04 : fits04.all frame001test04=true := by
  have h32 := stitchAt 32 3 frame001scope04_s032 frame001scope04_end
  have h28 := stitchAt 28 4 frame001scope04_s028 h32
  have h24 := stitchAt 24 4 frame001scope04_s024 h28
  have h20 := stitchAt 20 4 frame001scope04_s020 h24
  have h16 := stitchAt 16 4 frame001scope04_s016 h20
  have h12 := stitchAt 12 4 frame001scope04_s012 h16
  have h8 := stitchAt 8 4 frame001scope04_s008 h12
  have h4 := stitchAt 4 4 frame001scope04_s004 h8
  have h0 := stitchAt 0 4 frame001scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch04 : batch04.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope04

private abbrev frame001test05 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch05.stop,F)

private theorem frame001scope05_s000 : ((fits05.drop 0).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s004 : ((fits05.drop 4).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s008 : ((fits05.drop 8).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s012 : ((fits05.drop 12).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s016 : ((fits05.drop 16).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s020 : ((fits05.drop 20).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s024 : ((fits05.drop 24).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s028 : ((fits05.drop 28).take 4).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_s032 : ((fits05.drop 32).take 3).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05_end : (fits05.drop 35).all frame001test05=true := by
  decide +kernel

private theorem frame001scope05 : fits05.all frame001test05=true := by
  have h32 := stitchAt 32 3 frame001scope05_s032 frame001scope05_end
  have h28 := stitchAt 28 4 frame001scope05_s028 h32
  have h24 := stitchAt 24 4 frame001scope05_s024 h28
  have h20 := stitchAt 20 4 frame001scope05_s020 h24
  have h16 := stitchAt 16 4 frame001scope05_s016 h20
  have h12 := stitchAt 12 4 frame001scope05_s012 h16
  have h8 := stitchAt 8 4 frame001scope05_s008 h12
  have h4 := stitchAt 4 4 frame001scope05_s004 h8
  have h0 := stitchAt 0 4 frame001scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch05 : batch05.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope05

private abbrev frame001test06 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch06.stop,F)

private theorem frame001scope06_s000 : ((fits06.drop 0).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s004 : ((fits06.drop 4).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s008 : ((fits06.drop 8).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s012 : ((fits06.drop 12).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s016 : ((fits06.drop 16).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s020 : ((fits06.drop 20).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s024 : ((fits06.drop 24).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s028 : ((fits06.drop 28).take 4).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_s032 : ((fits06.drop 32).take 3).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06_end : (fits06.drop 35).all frame001test06=true := by
  decide +kernel

private theorem frame001scope06 : fits06.all frame001test06=true := by
  have h32 := stitchAt 32 3 frame001scope06_s032 frame001scope06_end
  have h28 := stitchAt 28 4 frame001scope06_s028 h32
  have h24 := stitchAt 24 4 frame001scope06_s024 h28
  have h20 := stitchAt 20 4 frame001scope06_s020 h24
  have h16 := stitchAt 16 4 frame001scope06_s016 h20
  have h12 := stitchAt 12 4 frame001scope06_s012 h16
  have h8 := stitchAt 8 4 frame001scope06_s008 h12
  have h4 := stitchAt 4 4 frame001scope06_s004 h8
  have h0 := stitchAt 0 4 frame001scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch06 : batch06.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope06

private abbrev frame001test07 (F : Finset (Fin 8)) : Bool :=
  scopedPickTest original frame5 (fun z => List.lookup (guideCode z) guide001)
    (batch07.stop,F)

private theorem frame001scope07_s000 : ((fits07.drop 0).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s004 : ((fits07.drop 4).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s008 : ((fits07.drop 8).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s012 : ((fits07.drop 12).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s016 : ((fits07.drop 16).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s020 : ((fits07.drop 20).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s024 : ((fits07.drop 24).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s028 : ((fits07.drop 28).take 4).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_s032 : ((fits07.drop 32).take 3).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07_end : (fits07.drop 35).all frame001test07=true := by
  decide +kernel

private theorem frame001scope07 : fits07.all frame001test07=true := by
  have h32 := stitchAt 32 3 frame001scope07_s032 frame001scope07_end
  have h28 := stitchAt 28 4 frame001scope07_s028 h32
  have h24 := stitchAt 24 4 frame001scope07_s024 h28
  have h20 := stitchAt 20 4 frame001scope07_s020 h24
  have h16 := stitchAt 16 4 frame001scope07_s016 h20
  have h12 := stitchAt 12 4 frame001scope07_s012 h16
  have h8 := stitchAt 8 4 frame001scope07_s008 h12
  have h4 := stitchAt 4 4 frame001scope07_s004 h8
  have h0 := stitchAt 0 4 frame001scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame001batch07 : batch07.pickTest original frame5=true :=
  FitBatch.pickTest_of_scoped scoped001 frame001scope07

private theorem frameBatches001 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame5)=true := by
  simp only [List.all_cons,List.all_nil,frame001batch00,frame001batch01,frame001batch02,frame001batch03,frame001batch04,frame001batch05,frame001batch06,frame001batch07,Bool.and_self]

theorem frameOK001 : frameRankTest original useStop frame5=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches001


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
