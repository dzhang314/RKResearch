module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK030 : stripTest frame64=true := by decide +kernel

theorem spanOK030 : checkChain 1680 1664 [frame64.span]=true := by decide +kernel

private theorem guideAt030 : List.lookup frame64.span.1 guideTable=some guide030 := by
  decide +kernel

private theorem scoped030 : original.guide frame64.span.1 =
    (fun z => List.lookup (guideCode z) guide030) := by
  funext z
  change (List.lookup frame64.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide030
  simp only [guideAt030,Option.bind_some]

private abbrev frame030test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch00.stop,F)

private theorem frame030scope00_s000 : ((fits00.drop 0).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s004 : ((fits00.drop 4).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s008 : ((fits00.drop 8).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s012 : ((fits00.drop 12).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s016 : ((fits00.drop 16).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s020 : ((fits00.drop 20).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s024 : ((fits00.drop 24).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s028 : ((fits00.drop 28).take 4).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_s032 : ((fits00.drop 32).take 3).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00_end : (fits00.drop 35).all frame030test00=true := by
  decide +kernel

private theorem frame030scope00 : fits00.all frame030test00=true := by
  have h32 := stitchAt 32 3 frame030scope00_s032 frame030scope00_end
  have h28 := stitchAt 28 4 frame030scope00_s028 h32
  have h24 := stitchAt 24 4 frame030scope00_s024 h28
  have h20 := stitchAt 20 4 frame030scope00_s020 h24
  have h16 := stitchAt 16 4 frame030scope00_s016 h20
  have h12 := stitchAt 12 4 frame030scope00_s012 h16
  have h8 := stitchAt 8 4 frame030scope00_s008 h12
  have h4 := stitchAt 4 4 frame030scope00_s004 h8
  have h0 := stitchAt 0 4 frame030scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch00 : batch00.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope00

private abbrev frame030test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch01.stop,F)

private theorem frame030scope01_s000 : ((fits01.drop 0).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s004 : ((fits01.drop 4).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s008 : ((fits01.drop 8).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s012 : ((fits01.drop 12).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s016 : ((fits01.drop 16).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s020 : ((fits01.drop 20).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s024 : ((fits01.drop 24).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s028 : ((fits01.drop 28).take 4).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_s032 : ((fits01.drop 32).take 3).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01_end : (fits01.drop 35).all frame030test01=true := by
  decide +kernel

private theorem frame030scope01 : fits01.all frame030test01=true := by
  have h32 := stitchAt 32 3 frame030scope01_s032 frame030scope01_end
  have h28 := stitchAt 28 4 frame030scope01_s028 h32
  have h24 := stitchAt 24 4 frame030scope01_s024 h28
  have h20 := stitchAt 20 4 frame030scope01_s020 h24
  have h16 := stitchAt 16 4 frame030scope01_s016 h20
  have h12 := stitchAt 12 4 frame030scope01_s012 h16
  have h8 := stitchAt 8 4 frame030scope01_s008 h12
  have h4 := stitchAt 4 4 frame030scope01_s004 h8
  have h0 := stitchAt 0 4 frame030scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch01 : batch01.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope01

private abbrev frame030test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch02.stop,F)

private theorem frame030scope02_s000 : ((fits02.drop 0).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s004 : ((fits02.drop 4).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s008 : ((fits02.drop 8).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s012 : ((fits02.drop 12).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s016 : ((fits02.drop 16).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s020 : ((fits02.drop 20).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s024 : ((fits02.drop 24).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s028 : ((fits02.drop 28).take 4).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_s032 : ((fits02.drop 32).take 3).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02_end : (fits02.drop 35).all frame030test02=true := by
  decide +kernel

private theorem frame030scope02 : fits02.all frame030test02=true := by
  have h32 := stitchAt 32 3 frame030scope02_s032 frame030scope02_end
  have h28 := stitchAt 28 4 frame030scope02_s028 h32
  have h24 := stitchAt 24 4 frame030scope02_s024 h28
  have h20 := stitchAt 20 4 frame030scope02_s020 h24
  have h16 := stitchAt 16 4 frame030scope02_s016 h20
  have h12 := stitchAt 12 4 frame030scope02_s012 h16
  have h8 := stitchAt 8 4 frame030scope02_s008 h12
  have h4 := stitchAt 4 4 frame030scope02_s004 h8
  have h0 := stitchAt 0 4 frame030scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch02 : batch02.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope02

private abbrev frame030test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch03.stop,F)

private theorem frame030scope03_s000 : ((fits03.drop 0).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s004 : ((fits03.drop 4).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s008 : ((fits03.drop 8).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s012 : ((fits03.drop 12).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s016 : ((fits03.drop 16).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s020 : ((fits03.drop 20).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s024 : ((fits03.drop 24).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s028 : ((fits03.drop 28).take 4).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_s032 : ((fits03.drop 32).take 3).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03_end : (fits03.drop 35).all frame030test03=true := by
  decide +kernel

private theorem frame030scope03 : fits03.all frame030test03=true := by
  have h32 := stitchAt 32 3 frame030scope03_s032 frame030scope03_end
  have h28 := stitchAt 28 4 frame030scope03_s028 h32
  have h24 := stitchAt 24 4 frame030scope03_s024 h28
  have h20 := stitchAt 20 4 frame030scope03_s020 h24
  have h16 := stitchAt 16 4 frame030scope03_s016 h20
  have h12 := stitchAt 12 4 frame030scope03_s012 h16
  have h8 := stitchAt 8 4 frame030scope03_s008 h12
  have h4 := stitchAt 4 4 frame030scope03_s004 h8
  have h0 := stitchAt 0 4 frame030scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch03 : batch03.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope03

private abbrev frame030test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch04.stop,F)

private theorem frame030scope04_s000 : ((fits04.drop 0).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s004 : ((fits04.drop 4).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s008 : ((fits04.drop 8).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s012 : ((fits04.drop 12).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s016 : ((fits04.drop 16).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s020 : ((fits04.drop 20).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s024 : ((fits04.drop 24).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s028 : ((fits04.drop 28).take 4).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_s032 : ((fits04.drop 32).take 3).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04_end : (fits04.drop 35).all frame030test04=true := by
  decide +kernel

private theorem frame030scope04 : fits04.all frame030test04=true := by
  have h32 := stitchAt 32 3 frame030scope04_s032 frame030scope04_end
  have h28 := stitchAt 28 4 frame030scope04_s028 h32
  have h24 := stitchAt 24 4 frame030scope04_s024 h28
  have h20 := stitchAt 20 4 frame030scope04_s020 h24
  have h16 := stitchAt 16 4 frame030scope04_s016 h20
  have h12 := stitchAt 12 4 frame030scope04_s012 h16
  have h8 := stitchAt 8 4 frame030scope04_s008 h12
  have h4 := stitchAt 4 4 frame030scope04_s004 h8
  have h0 := stitchAt 0 4 frame030scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch04 : batch04.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope04

private abbrev frame030test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch05.stop,F)

private theorem frame030scope05_s000 : ((fits05.drop 0).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s004 : ((fits05.drop 4).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s008 : ((fits05.drop 8).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s012 : ((fits05.drop 12).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s016 : ((fits05.drop 16).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s020 : ((fits05.drop 20).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s024 : ((fits05.drop 24).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s028 : ((fits05.drop 28).take 4).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_s032 : ((fits05.drop 32).take 3).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05_end : (fits05.drop 35).all frame030test05=true := by
  decide +kernel

private theorem frame030scope05 : fits05.all frame030test05=true := by
  have h32 := stitchAt 32 3 frame030scope05_s032 frame030scope05_end
  have h28 := stitchAt 28 4 frame030scope05_s028 h32
  have h24 := stitchAt 24 4 frame030scope05_s024 h28
  have h20 := stitchAt 20 4 frame030scope05_s020 h24
  have h16 := stitchAt 16 4 frame030scope05_s016 h20
  have h12 := stitchAt 12 4 frame030scope05_s012 h16
  have h8 := stitchAt 8 4 frame030scope05_s008 h12
  have h4 := stitchAt 4 4 frame030scope05_s004 h8
  have h0 := stitchAt 0 4 frame030scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch05 : batch05.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope05

private abbrev frame030test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch06.stop,F)

private theorem frame030scope06_s000 : ((fits06.drop 0).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s004 : ((fits06.drop 4).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s008 : ((fits06.drop 8).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s012 : ((fits06.drop 12).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s016 : ((fits06.drop 16).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s020 : ((fits06.drop 20).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s024 : ((fits06.drop 24).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s028 : ((fits06.drop 28).take 4).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_s032 : ((fits06.drop 32).take 3).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06_end : (fits06.drop 35).all frame030test06=true := by
  decide +kernel

private theorem frame030scope06 : fits06.all frame030test06=true := by
  have h32 := stitchAt 32 3 frame030scope06_s032 frame030scope06_end
  have h28 := stitchAt 28 4 frame030scope06_s028 h32
  have h24 := stitchAt 24 4 frame030scope06_s024 h28
  have h20 := stitchAt 20 4 frame030scope06_s020 h24
  have h16 := stitchAt 16 4 frame030scope06_s016 h20
  have h12 := stitchAt 12 4 frame030scope06_s012 h16
  have h8 := stitchAt 8 4 frame030scope06_s008 h12
  have h4 := stitchAt 4 4 frame030scope06_s004 h8
  have h0 := stitchAt 0 4 frame030scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch06 : batch06.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope06

private abbrev frame030test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame64 (fun z => List.lookup (guideCode z) guide030)
    (batch07.stop,F)

private theorem frame030scope07_s000 : ((fits07.drop 0).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s004 : ((fits07.drop 4).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s008 : ((fits07.drop 8).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s012 : ((fits07.drop 12).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s016 : ((fits07.drop 16).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s020 : ((fits07.drop 20).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s024 : ((fits07.drop 24).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s028 : ((fits07.drop 28).take 4).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_s032 : ((fits07.drop 32).take 3).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07_end : (fits07.drop 35).all frame030test07=true := by
  decide +kernel

private theorem frame030scope07 : fits07.all frame030test07=true := by
  have h32 := stitchAt 32 3 frame030scope07_s032 frame030scope07_end
  have h28 := stitchAt 28 4 frame030scope07_s028 h32
  have h24 := stitchAt 24 4 frame030scope07_s024 h28
  have h20 := stitchAt 20 4 frame030scope07_s020 h24
  have h16 := stitchAt 16 4 frame030scope07_s016 h20
  have h12 := stitchAt 12 4 frame030scope07_s012 h16
  have h8 := stitchAt 8 4 frame030scope07_s008 h12
  have h4 := stitchAt 4 4 frame030scope07_s004 h8
  have h0 := stitchAt 0 4 frame030scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame030batch07 : batch07.pickTest original frame64=true :=
  FitBatch.pickTest_of_scoped scoped030 frame030scope07

private theorem frameBatches030 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame64)=true := by
  simp only [List.all_cons,List.all_nil,frame030batch00,frame030batch01,frame030batch02,frame030batch03,frame030batch04,frame030batch05,frame030batch06,frame030batch07,Bool.and_self]

theorem frameOK030 : frameRankTest original useStop frame64=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches030

theorem stripOK031 : stripTest frame66=true := by decide +kernel

theorem spanOK031 : checkChain 1688 1680 [frame66.span]=true := by decide +kernel

private theorem guideAt031 : List.lookup frame66.span.1 guideTable=some guide031 := by
  decide +kernel

private theorem scoped031 : original.guide frame66.span.1 =
    (fun z => List.lookup (guideCode z) guide031) := by
  funext z
  change (List.lookup frame66.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide031
  simp only [guideAt031,Option.bind_some]

private abbrev frame031test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch00.stop,F)

private theorem frame031scope00_s000 : ((fits00.drop 0).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s004 : ((fits00.drop 4).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s008 : ((fits00.drop 8).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s012 : ((fits00.drop 12).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s016 : ((fits00.drop 16).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s020 : ((fits00.drop 20).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s024 : ((fits00.drop 24).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s028 : ((fits00.drop 28).take 4).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_s032 : ((fits00.drop 32).take 3).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00_end : (fits00.drop 35).all frame031test00=true := by
  decide +kernel

private theorem frame031scope00 : fits00.all frame031test00=true := by
  have h32 := stitchAt 32 3 frame031scope00_s032 frame031scope00_end
  have h28 := stitchAt 28 4 frame031scope00_s028 h32
  have h24 := stitchAt 24 4 frame031scope00_s024 h28
  have h20 := stitchAt 20 4 frame031scope00_s020 h24
  have h16 := stitchAt 16 4 frame031scope00_s016 h20
  have h12 := stitchAt 12 4 frame031scope00_s012 h16
  have h8 := stitchAt 8 4 frame031scope00_s008 h12
  have h4 := stitchAt 4 4 frame031scope00_s004 h8
  have h0 := stitchAt 0 4 frame031scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch00 : batch00.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope00

private abbrev frame031test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch01.stop,F)

private theorem frame031scope01_s000 : ((fits01.drop 0).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s004 : ((fits01.drop 4).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s008 : ((fits01.drop 8).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s012 : ((fits01.drop 12).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s016 : ((fits01.drop 16).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s020 : ((fits01.drop 20).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s024 : ((fits01.drop 24).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s028 : ((fits01.drop 28).take 4).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_s032 : ((fits01.drop 32).take 3).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01_end : (fits01.drop 35).all frame031test01=true := by
  decide +kernel

private theorem frame031scope01 : fits01.all frame031test01=true := by
  have h32 := stitchAt 32 3 frame031scope01_s032 frame031scope01_end
  have h28 := stitchAt 28 4 frame031scope01_s028 h32
  have h24 := stitchAt 24 4 frame031scope01_s024 h28
  have h20 := stitchAt 20 4 frame031scope01_s020 h24
  have h16 := stitchAt 16 4 frame031scope01_s016 h20
  have h12 := stitchAt 12 4 frame031scope01_s012 h16
  have h8 := stitchAt 8 4 frame031scope01_s008 h12
  have h4 := stitchAt 4 4 frame031scope01_s004 h8
  have h0 := stitchAt 0 4 frame031scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch01 : batch01.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope01

private abbrev frame031test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch02.stop,F)

private theorem frame031scope02_s000 : ((fits02.drop 0).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s004 : ((fits02.drop 4).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s008 : ((fits02.drop 8).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s012 : ((fits02.drop 12).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s016 : ((fits02.drop 16).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s020 : ((fits02.drop 20).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s024 : ((fits02.drop 24).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s028 : ((fits02.drop 28).take 4).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_s032 : ((fits02.drop 32).take 3).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02_end : (fits02.drop 35).all frame031test02=true := by
  decide +kernel

private theorem frame031scope02 : fits02.all frame031test02=true := by
  have h32 := stitchAt 32 3 frame031scope02_s032 frame031scope02_end
  have h28 := stitchAt 28 4 frame031scope02_s028 h32
  have h24 := stitchAt 24 4 frame031scope02_s024 h28
  have h20 := stitchAt 20 4 frame031scope02_s020 h24
  have h16 := stitchAt 16 4 frame031scope02_s016 h20
  have h12 := stitchAt 12 4 frame031scope02_s012 h16
  have h8 := stitchAt 8 4 frame031scope02_s008 h12
  have h4 := stitchAt 4 4 frame031scope02_s004 h8
  have h0 := stitchAt 0 4 frame031scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch02 : batch02.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope02

private abbrev frame031test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch03.stop,F)

private theorem frame031scope03_s000 : ((fits03.drop 0).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s004 : ((fits03.drop 4).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s008 : ((fits03.drop 8).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s012 : ((fits03.drop 12).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s016 : ((fits03.drop 16).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s020 : ((fits03.drop 20).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s024 : ((fits03.drop 24).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s028 : ((fits03.drop 28).take 4).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_s032 : ((fits03.drop 32).take 3).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03_end : (fits03.drop 35).all frame031test03=true := by
  decide +kernel

private theorem frame031scope03 : fits03.all frame031test03=true := by
  have h32 := stitchAt 32 3 frame031scope03_s032 frame031scope03_end
  have h28 := stitchAt 28 4 frame031scope03_s028 h32
  have h24 := stitchAt 24 4 frame031scope03_s024 h28
  have h20 := stitchAt 20 4 frame031scope03_s020 h24
  have h16 := stitchAt 16 4 frame031scope03_s016 h20
  have h12 := stitchAt 12 4 frame031scope03_s012 h16
  have h8 := stitchAt 8 4 frame031scope03_s008 h12
  have h4 := stitchAt 4 4 frame031scope03_s004 h8
  have h0 := stitchAt 0 4 frame031scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch03 : batch03.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope03

private abbrev frame031test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch04.stop,F)

private theorem frame031scope04_s000 : ((fits04.drop 0).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s004 : ((fits04.drop 4).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s008 : ((fits04.drop 8).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s012 : ((fits04.drop 12).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s016 : ((fits04.drop 16).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s020 : ((fits04.drop 20).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s024 : ((fits04.drop 24).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s028 : ((fits04.drop 28).take 4).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_s032 : ((fits04.drop 32).take 3).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04_end : (fits04.drop 35).all frame031test04=true := by
  decide +kernel

private theorem frame031scope04 : fits04.all frame031test04=true := by
  have h32 := stitchAt 32 3 frame031scope04_s032 frame031scope04_end
  have h28 := stitchAt 28 4 frame031scope04_s028 h32
  have h24 := stitchAt 24 4 frame031scope04_s024 h28
  have h20 := stitchAt 20 4 frame031scope04_s020 h24
  have h16 := stitchAt 16 4 frame031scope04_s016 h20
  have h12 := stitchAt 12 4 frame031scope04_s012 h16
  have h8 := stitchAt 8 4 frame031scope04_s008 h12
  have h4 := stitchAt 4 4 frame031scope04_s004 h8
  have h0 := stitchAt 0 4 frame031scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch04 : batch04.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope04

private abbrev frame031test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch05.stop,F)

private theorem frame031scope05_s000 : ((fits05.drop 0).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s004 : ((fits05.drop 4).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s008 : ((fits05.drop 8).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s012 : ((fits05.drop 12).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s016 : ((fits05.drop 16).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s020 : ((fits05.drop 20).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s024 : ((fits05.drop 24).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s028 : ((fits05.drop 28).take 4).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_s032 : ((fits05.drop 32).take 3).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05_end : (fits05.drop 35).all frame031test05=true := by
  decide +kernel

private theorem frame031scope05 : fits05.all frame031test05=true := by
  have h32 := stitchAt 32 3 frame031scope05_s032 frame031scope05_end
  have h28 := stitchAt 28 4 frame031scope05_s028 h32
  have h24 := stitchAt 24 4 frame031scope05_s024 h28
  have h20 := stitchAt 20 4 frame031scope05_s020 h24
  have h16 := stitchAt 16 4 frame031scope05_s016 h20
  have h12 := stitchAt 12 4 frame031scope05_s012 h16
  have h8 := stitchAt 8 4 frame031scope05_s008 h12
  have h4 := stitchAt 4 4 frame031scope05_s004 h8
  have h0 := stitchAt 0 4 frame031scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch05 : batch05.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope05

private abbrev frame031test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch06.stop,F)

private theorem frame031scope06_s000 : ((fits06.drop 0).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s004 : ((fits06.drop 4).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s008 : ((fits06.drop 8).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s012 : ((fits06.drop 12).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s016 : ((fits06.drop 16).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s020 : ((fits06.drop 20).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s024 : ((fits06.drop 24).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s028 : ((fits06.drop 28).take 4).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_s032 : ((fits06.drop 32).take 3).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06_end : (fits06.drop 35).all frame031test06=true := by
  decide +kernel

private theorem frame031scope06 : fits06.all frame031test06=true := by
  have h32 := stitchAt 32 3 frame031scope06_s032 frame031scope06_end
  have h28 := stitchAt 28 4 frame031scope06_s028 h32
  have h24 := stitchAt 24 4 frame031scope06_s024 h28
  have h20 := stitchAt 20 4 frame031scope06_s020 h24
  have h16 := stitchAt 16 4 frame031scope06_s016 h20
  have h12 := stitchAt 12 4 frame031scope06_s012 h16
  have h8 := stitchAt 8 4 frame031scope06_s008 h12
  have h4 := stitchAt 4 4 frame031scope06_s004 h8
  have h0 := stitchAt 0 4 frame031scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch06 : batch06.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope06

private abbrev frame031test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame66 (fun z => List.lookup (guideCode z) guide031)
    (batch07.stop,F)

private theorem frame031scope07_s000 : ((fits07.drop 0).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s004 : ((fits07.drop 4).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s008 : ((fits07.drop 8).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s012 : ((fits07.drop 12).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s016 : ((fits07.drop 16).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s020 : ((fits07.drop 20).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s024 : ((fits07.drop 24).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s028 : ((fits07.drop 28).take 4).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_s032 : ((fits07.drop 32).take 3).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07_end : (fits07.drop 35).all frame031test07=true := by
  decide +kernel

private theorem frame031scope07 : fits07.all frame031test07=true := by
  have h32 := stitchAt 32 3 frame031scope07_s032 frame031scope07_end
  have h28 := stitchAt 28 4 frame031scope07_s028 h32
  have h24 := stitchAt 24 4 frame031scope07_s024 h28
  have h20 := stitchAt 20 4 frame031scope07_s020 h24
  have h16 := stitchAt 16 4 frame031scope07_s016 h20
  have h12 := stitchAt 12 4 frame031scope07_s012 h16
  have h8 := stitchAt 8 4 frame031scope07_s008 h12
  have h4 := stitchAt 4 4 frame031scope07_s004 h8
  have h0 := stitchAt 0 4 frame031scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame031batch07 : batch07.pickTest original frame66=true :=
  FitBatch.pickTest_of_scoped scoped031 frame031scope07

private theorem frameBatches031 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame66)=true := by
  simp only [List.all_cons,List.all_nil,frame031batch00,frame031batch01,frame031batch02,frame031batch03,frame031batch04,frame031batch05,frame031batch06,frame031batch07,Bool.and_self]

theorem frameOK031 : frameRankTest original useStop frame66=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches031


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
