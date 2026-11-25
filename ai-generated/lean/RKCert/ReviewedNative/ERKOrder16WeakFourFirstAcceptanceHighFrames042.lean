module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem stripOK084 : stripTest frame171=true := by decide +kernel

theorem spanOK084 : checkChain 1936 1920 [frame171.span]=true := by decide +kernel

private theorem guideAt084 : List.lookup frame171.span.1 guideTable=some guide084 := by
  decide +kernel

private theorem scoped084 : original.guide frame171.span.1 =
    (fun z => List.lookup (guideCode z) guide084) := by
  funext z
  change (List.lookup frame171.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide084
  simp only [guideAt084,Option.bind_some]

private abbrev frame084test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch00.stop,F)

private theorem frame084scope00_s000 : ((fits00.drop 0).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s004 : ((fits00.drop 4).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s008 : ((fits00.drop 8).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s012 : ((fits00.drop 12).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s016 : ((fits00.drop 16).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s020 : ((fits00.drop 20).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s024 : ((fits00.drop 24).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s028 : ((fits00.drop 28).take 4).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_s032 : ((fits00.drop 32).take 3).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00_end : (fits00.drop 35).all frame084test00=true := by
  decide +kernel

private theorem frame084scope00 : fits00.all frame084test00=true := by
  have h32 := stitchAt 32 3 frame084scope00_s032 frame084scope00_end
  have h28 := stitchAt 28 4 frame084scope00_s028 h32
  have h24 := stitchAt 24 4 frame084scope00_s024 h28
  have h20 := stitchAt 20 4 frame084scope00_s020 h24
  have h16 := stitchAt 16 4 frame084scope00_s016 h20
  have h12 := stitchAt 12 4 frame084scope00_s012 h16
  have h8 := stitchAt 8 4 frame084scope00_s008 h12
  have h4 := stitchAt 4 4 frame084scope00_s004 h8
  have h0 := stitchAt 0 4 frame084scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch00 : batch00.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope00

private abbrev frame084test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch01.stop,F)

private theorem frame084scope01_s000 : ((fits01.drop 0).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s004 : ((fits01.drop 4).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s008 : ((fits01.drop 8).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s012 : ((fits01.drop 12).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s016 : ((fits01.drop 16).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s020 : ((fits01.drop 20).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s024 : ((fits01.drop 24).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s028 : ((fits01.drop 28).take 4).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_s032 : ((fits01.drop 32).take 3).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01_end : (fits01.drop 35).all frame084test01=true := by
  decide +kernel

private theorem frame084scope01 : fits01.all frame084test01=true := by
  have h32 := stitchAt 32 3 frame084scope01_s032 frame084scope01_end
  have h28 := stitchAt 28 4 frame084scope01_s028 h32
  have h24 := stitchAt 24 4 frame084scope01_s024 h28
  have h20 := stitchAt 20 4 frame084scope01_s020 h24
  have h16 := stitchAt 16 4 frame084scope01_s016 h20
  have h12 := stitchAt 12 4 frame084scope01_s012 h16
  have h8 := stitchAt 8 4 frame084scope01_s008 h12
  have h4 := stitchAt 4 4 frame084scope01_s004 h8
  have h0 := stitchAt 0 4 frame084scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch01 : batch01.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope01

private abbrev frame084test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch02.stop,F)

private theorem frame084scope02_s000 : ((fits02.drop 0).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s004 : ((fits02.drop 4).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s008 : ((fits02.drop 8).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s012 : ((fits02.drop 12).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s016 : ((fits02.drop 16).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s020 : ((fits02.drop 20).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s024 : ((fits02.drop 24).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s028 : ((fits02.drop 28).take 4).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_s032 : ((fits02.drop 32).take 3).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02_end : (fits02.drop 35).all frame084test02=true := by
  decide +kernel

private theorem frame084scope02 : fits02.all frame084test02=true := by
  have h32 := stitchAt 32 3 frame084scope02_s032 frame084scope02_end
  have h28 := stitchAt 28 4 frame084scope02_s028 h32
  have h24 := stitchAt 24 4 frame084scope02_s024 h28
  have h20 := stitchAt 20 4 frame084scope02_s020 h24
  have h16 := stitchAt 16 4 frame084scope02_s016 h20
  have h12 := stitchAt 12 4 frame084scope02_s012 h16
  have h8 := stitchAt 8 4 frame084scope02_s008 h12
  have h4 := stitchAt 4 4 frame084scope02_s004 h8
  have h0 := stitchAt 0 4 frame084scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch02 : batch02.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope02

private abbrev frame084test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch03.stop,F)

private theorem frame084scope03_s000 : ((fits03.drop 0).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s004 : ((fits03.drop 4).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s008 : ((fits03.drop 8).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s012 : ((fits03.drop 12).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s016 : ((fits03.drop 16).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s020 : ((fits03.drop 20).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s024 : ((fits03.drop 24).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s028 : ((fits03.drop 28).take 4).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_s032 : ((fits03.drop 32).take 3).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03_end : (fits03.drop 35).all frame084test03=true := by
  decide +kernel

private theorem frame084scope03 : fits03.all frame084test03=true := by
  have h32 := stitchAt 32 3 frame084scope03_s032 frame084scope03_end
  have h28 := stitchAt 28 4 frame084scope03_s028 h32
  have h24 := stitchAt 24 4 frame084scope03_s024 h28
  have h20 := stitchAt 20 4 frame084scope03_s020 h24
  have h16 := stitchAt 16 4 frame084scope03_s016 h20
  have h12 := stitchAt 12 4 frame084scope03_s012 h16
  have h8 := stitchAt 8 4 frame084scope03_s008 h12
  have h4 := stitchAt 4 4 frame084scope03_s004 h8
  have h0 := stitchAt 0 4 frame084scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch03 : batch03.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope03

private abbrev frame084test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch04.stop,F)

private theorem frame084scope04_s000 : ((fits04.drop 0).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s004 : ((fits04.drop 4).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s008 : ((fits04.drop 8).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s012 : ((fits04.drop 12).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s016 : ((fits04.drop 16).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s020 : ((fits04.drop 20).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s024 : ((fits04.drop 24).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s028 : ((fits04.drop 28).take 4).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_s032 : ((fits04.drop 32).take 3).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04_end : (fits04.drop 35).all frame084test04=true := by
  decide +kernel

private theorem frame084scope04 : fits04.all frame084test04=true := by
  have h32 := stitchAt 32 3 frame084scope04_s032 frame084scope04_end
  have h28 := stitchAt 28 4 frame084scope04_s028 h32
  have h24 := stitchAt 24 4 frame084scope04_s024 h28
  have h20 := stitchAt 20 4 frame084scope04_s020 h24
  have h16 := stitchAt 16 4 frame084scope04_s016 h20
  have h12 := stitchAt 12 4 frame084scope04_s012 h16
  have h8 := stitchAt 8 4 frame084scope04_s008 h12
  have h4 := stitchAt 4 4 frame084scope04_s004 h8
  have h0 := stitchAt 0 4 frame084scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch04 : batch04.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope04

private abbrev frame084test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch05.stop,F)

private theorem frame084scope05_s000 : ((fits05.drop 0).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s004 : ((fits05.drop 4).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s008 : ((fits05.drop 8).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s012 : ((fits05.drop 12).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s016 : ((fits05.drop 16).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s020 : ((fits05.drop 20).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s024 : ((fits05.drop 24).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s028 : ((fits05.drop 28).take 4).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_s032 : ((fits05.drop 32).take 3).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05_end : (fits05.drop 35).all frame084test05=true := by
  decide +kernel

private theorem frame084scope05 : fits05.all frame084test05=true := by
  have h32 := stitchAt 32 3 frame084scope05_s032 frame084scope05_end
  have h28 := stitchAt 28 4 frame084scope05_s028 h32
  have h24 := stitchAt 24 4 frame084scope05_s024 h28
  have h20 := stitchAt 20 4 frame084scope05_s020 h24
  have h16 := stitchAt 16 4 frame084scope05_s016 h20
  have h12 := stitchAt 12 4 frame084scope05_s012 h16
  have h8 := stitchAt 8 4 frame084scope05_s008 h12
  have h4 := stitchAt 4 4 frame084scope05_s004 h8
  have h0 := stitchAt 0 4 frame084scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch05 : batch05.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope05

private abbrev frame084test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch06.stop,F)

private theorem frame084scope06_s000 : ((fits06.drop 0).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s004 : ((fits06.drop 4).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s008 : ((fits06.drop 8).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s012 : ((fits06.drop 12).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s016 : ((fits06.drop 16).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s020 : ((fits06.drop 20).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s024 : ((fits06.drop 24).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s028 : ((fits06.drop 28).take 4).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_s032 : ((fits06.drop 32).take 3).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06_end : (fits06.drop 35).all frame084test06=true := by
  decide +kernel

private theorem frame084scope06 : fits06.all frame084test06=true := by
  have h32 := stitchAt 32 3 frame084scope06_s032 frame084scope06_end
  have h28 := stitchAt 28 4 frame084scope06_s028 h32
  have h24 := stitchAt 24 4 frame084scope06_s024 h28
  have h20 := stitchAt 20 4 frame084scope06_s020 h24
  have h16 := stitchAt 16 4 frame084scope06_s016 h20
  have h12 := stitchAt 12 4 frame084scope06_s012 h16
  have h8 := stitchAt 8 4 frame084scope06_s008 h12
  have h4 := stitchAt 4 4 frame084scope06_s004 h8
  have h0 := stitchAt 0 4 frame084scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch06 : batch06.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope06

private abbrev frame084test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame171 (fun z => List.lookup (guideCode z) guide084)
    (batch07.stop,F)

private theorem frame084scope07_s000 : ((fits07.drop 0).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s004 : ((fits07.drop 4).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s008 : ((fits07.drop 8).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s012 : ((fits07.drop 12).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s016 : ((fits07.drop 16).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s020 : ((fits07.drop 20).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s024 : ((fits07.drop 24).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s028 : ((fits07.drop 28).take 4).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_s032 : ((fits07.drop 32).take 3).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07_end : (fits07.drop 35).all frame084test07=true := by
  decide +kernel

private theorem frame084scope07 : fits07.all frame084test07=true := by
  have h32 := stitchAt 32 3 frame084scope07_s032 frame084scope07_end
  have h28 := stitchAt 28 4 frame084scope07_s028 h32
  have h24 := stitchAt 24 4 frame084scope07_s024 h28
  have h20 := stitchAt 20 4 frame084scope07_s020 h24
  have h16 := stitchAt 16 4 frame084scope07_s016 h20
  have h12 := stitchAt 12 4 frame084scope07_s012 h16
  have h8 := stitchAt 8 4 frame084scope07_s008 h12
  have h4 := stitchAt 4 4 frame084scope07_s004 h8
  have h0 := stitchAt 0 4 frame084scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame084batch07 : batch07.pickTest original frame171=true :=
  FitBatch.pickTest_of_scoped scoped084 frame084scope07

private theorem frameBatches084 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame171)=true := by
  simp only [List.all_cons,List.all_nil,frame084batch00,frame084batch01,frame084batch02,frame084batch03,frame084batch04,frame084batch05,frame084batch06,frame084batch07,Bool.and_self]

theorem frameOK084 : frameRankTest original useStop frame171=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches084

theorem stripOK085 : stripTest frame172=true := by decide +kernel

theorem spanOK085 : checkChain 1952 1936 [frame172.span]=true := by decide +kernel

private theorem guideAt085 : List.lookup frame172.span.1 guideTable=some guide085 := by
  decide +kernel

private theorem scoped085 : original.guide frame172.span.1 =
    (fun z => List.lookup (guideCode z) guide085) := by
  funext z
  change (List.lookup frame172.span.1 guideTable).bind
    (fun xs => List.lookup (guideCode z) xs)=List.lookup (guideCode z) guide085
  simp only [guideAt085,Option.bind_some]

private abbrev frame085test00 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch00.stop,F)

private theorem frame085scope00_s000 : ((fits00.drop 0).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s004 : ((fits00.drop 4).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s008 : ((fits00.drop 8).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s012 : ((fits00.drop 12).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s016 : ((fits00.drop 16).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s020 : ((fits00.drop 20).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s024 : ((fits00.drop 24).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s028 : ((fits00.drop 28).take 4).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_s032 : ((fits00.drop 32).take 3).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00_end : (fits00.drop 35).all frame085test00=true := by
  decide +kernel

private theorem frame085scope00 : fits00.all frame085test00=true := by
  have h32 := stitchAt 32 3 frame085scope00_s032 frame085scope00_end
  have h28 := stitchAt 28 4 frame085scope00_s028 h32
  have h24 := stitchAt 24 4 frame085scope00_s024 h28
  have h20 := stitchAt 20 4 frame085scope00_s020 h24
  have h16 := stitchAt 16 4 frame085scope00_s016 h20
  have h12 := stitchAt 12 4 frame085scope00_s012 h16
  have h8 := stitchAt 8 4 frame085scope00_s008 h12
  have h4 := stitchAt 4 4 frame085scope00_s004 h8
  have h0 := stitchAt 0 4 frame085scope00_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch00 : batch00.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope00

private abbrev frame085test01 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch01.stop,F)

private theorem frame085scope01_s000 : ((fits01.drop 0).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s004 : ((fits01.drop 4).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s008 : ((fits01.drop 8).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s012 : ((fits01.drop 12).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s016 : ((fits01.drop 16).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s020 : ((fits01.drop 20).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s024 : ((fits01.drop 24).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s028 : ((fits01.drop 28).take 4).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_s032 : ((fits01.drop 32).take 3).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01_end : (fits01.drop 35).all frame085test01=true := by
  decide +kernel

private theorem frame085scope01 : fits01.all frame085test01=true := by
  have h32 := stitchAt 32 3 frame085scope01_s032 frame085scope01_end
  have h28 := stitchAt 28 4 frame085scope01_s028 h32
  have h24 := stitchAt 24 4 frame085scope01_s024 h28
  have h20 := stitchAt 20 4 frame085scope01_s020 h24
  have h16 := stitchAt 16 4 frame085scope01_s016 h20
  have h12 := stitchAt 12 4 frame085scope01_s012 h16
  have h8 := stitchAt 8 4 frame085scope01_s008 h12
  have h4 := stitchAt 4 4 frame085scope01_s004 h8
  have h0 := stitchAt 0 4 frame085scope01_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch01 : batch01.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope01

private abbrev frame085test02 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch02.stop,F)

private theorem frame085scope02_s000 : ((fits02.drop 0).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s004 : ((fits02.drop 4).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s008 : ((fits02.drop 8).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s012 : ((fits02.drop 12).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s016 : ((fits02.drop 16).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s020 : ((fits02.drop 20).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s024 : ((fits02.drop 24).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s028 : ((fits02.drop 28).take 4).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_s032 : ((fits02.drop 32).take 3).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02_end : (fits02.drop 35).all frame085test02=true := by
  decide +kernel

private theorem frame085scope02 : fits02.all frame085test02=true := by
  have h32 := stitchAt 32 3 frame085scope02_s032 frame085scope02_end
  have h28 := stitchAt 28 4 frame085scope02_s028 h32
  have h24 := stitchAt 24 4 frame085scope02_s024 h28
  have h20 := stitchAt 20 4 frame085scope02_s020 h24
  have h16 := stitchAt 16 4 frame085scope02_s016 h20
  have h12 := stitchAt 12 4 frame085scope02_s012 h16
  have h8 := stitchAt 8 4 frame085scope02_s008 h12
  have h4 := stitchAt 4 4 frame085scope02_s004 h8
  have h0 := stitchAt 0 4 frame085scope02_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch02 : batch02.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope02

private abbrev frame085test03 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch03.stop,F)

private theorem frame085scope03_s000 : ((fits03.drop 0).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s004 : ((fits03.drop 4).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s008 : ((fits03.drop 8).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s012 : ((fits03.drop 12).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s016 : ((fits03.drop 16).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s020 : ((fits03.drop 20).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s024 : ((fits03.drop 24).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s028 : ((fits03.drop 28).take 4).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_s032 : ((fits03.drop 32).take 3).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03_end : (fits03.drop 35).all frame085test03=true := by
  decide +kernel

private theorem frame085scope03 : fits03.all frame085test03=true := by
  have h32 := stitchAt 32 3 frame085scope03_s032 frame085scope03_end
  have h28 := stitchAt 28 4 frame085scope03_s028 h32
  have h24 := stitchAt 24 4 frame085scope03_s024 h28
  have h20 := stitchAt 20 4 frame085scope03_s020 h24
  have h16 := stitchAt 16 4 frame085scope03_s016 h20
  have h12 := stitchAt 12 4 frame085scope03_s012 h16
  have h8 := stitchAt 8 4 frame085scope03_s008 h12
  have h4 := stitchAt 4 4 frame085scope03_s004 h8
  have h0 := stitchAt 0 4 frame085scope03_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch03 : batch03.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope03

private abbrev frame085test04 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch04.stop,F)

private theorem frame085scope04_s000 : ((fits04.drop 0).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s004 : ((fits04.drop 4).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s008 : ((fits04.drop 8).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s012 : ((fits04.drop 12).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s016 : ((fits04.drop 16).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s020 : ((fits04.drop 20).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s024 : ((fits04.drop 24).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s028 : ((fits04.drop 28).take 4).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_s032 : ((fits04.drop 32).take 3).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04_end : (fits04.drop 35).all frame085test04=true := by
  decide +kernel

private theorem frame085scope04 : fits04.all frame085test04=true := by
  have h32 := stitchAt 32 3 frame085scope04_s032 frame085scope04_end
  have h28 := stitchAt 28 4 frame085scope04_s028 h32
  have h24 := stitchAt 24 4 frame085scope04_s024 h28
  have h20 := stitchAt 20 4 frame085scope04_s020 h24
  have h16 := stitchAt 16 4 frame085scope04_s016 h20
  have h12 := stitchAt 12 4 frame085scope04_s012 h16
  have h8 := stitchAt 8 4 frame085scope04_s008 h12
  have h4 := stitchAt 4 4 frame085scope04_s004 h8
  have h0 := stitchAt 0 4 frame085scope04_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch04 : batch04.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope04

private abbrev frame085test05 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch05.stop,F)

private theorem frame085scope05_s000 : ((fits05.drop 0).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s004 : ((fits05.drop 4).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s008 : ((fits05.drop 8).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s012 : ((fits05.drop 12).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s016 : ((fits05.drop 16).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s020 : ((fits05.drop 20).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s024 : ((fits05.drop 24).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s028 : ((fits05.drop 28).take 4).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_s032 : ((fits05.drop 32).take 3).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05_end : (fits05.drop 35).all frame085test05=true := by
  decide +kernel

private theorem frame085scope05 : fits05.all frame085test05=true := by
  have h32 := stitchAt 32 3 frame085scope05_s032 frame085scope05_end
  have h28 := stitchAt 28 4 frame085scope05_s028 h32
  have h24 := stitchAt 24 4 frame085scope05_s024 h28
  have h20 := stitchAt 20 4 frame085scope05_s020 h24
  have h16 := stitchAt 16 4 frame085scope05_s016 h20
  have h12 := stitchAt 12 4 frame085scope05_s012 h16
  have h8 := stitchAt 8 4 frame085scope05_s008 h12
  have h4 := stitchAt 4 4 frame085scope05_s004 h8
  have h0 := stitchAt 0 4 frame085scope05_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch05 : batch05.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope05

private abbrev frame085test06 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch06.stop,F)

private theorem frame085scope06_s000 : ((fits06.drop 0).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s004 : ((fits06.drop 4).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s008 : ((fits06.drop 8).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s012 : ((fits06.drop 12).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s016 : ((fits06.drop 16).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s020 : ((fits06.drop 20).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s024 : ((fits06.drop 24).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s028 : ((fits06.drop 28).take 4).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_s032 : ((fits06.drop 32).take 3).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06_end : (fits06.drop 35).all frame085test06=true := by
  decide +kernel

private theorem frame085scope06 : fits06.all frame085test06=true := by
  have h32 := stitchAt 32 3 frame085scope06_s032 frame085scope06_end
  have h28 := stitchAt 28 4 frame085scope06_s028 h32
  have h24 := stitchAt 24 4 frame085scope06_s024 h28
  have h20 := stitchAt 20 4 frame085scope06_s020 h24
  have h16 := stitchAt 16 4 frame085scope06_s016 h20
  have h12 := stitchAt 12 4 frame085scope06_s012 h16
  have h8 := stitchAt 8 4 frame085scope06_s008 h12
  have h4 := stitchAt 4 4 frame085scope06_s004 h8
  have h0 := stitchAt 0 4 frame085scope06_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch06 : batch06.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope06

private abbrev frame085test07 (F : Finset (Option (Fin 7))) : Bool :=
  scopedPickTest original frame172 (fun z => List.lookup (guideCode z) guide085)
    (batch07.stop,F)

private theorem frame085scope07_s000 : ((fits07.drop 0).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s004 : ((fits07.drop 4).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s008 : ((fits07.drop 8).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s012 : ((fits07.drop 12).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s016 : ((fits07.drop 16).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s020 : ((fits07.drop 20).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s024 : ((fits07.drop 24).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s028 : ((fits07.drop 28).take 4).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_s032 : ((fits07.drop 32).take 3).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07_end : (fits07.drop 35).all frame085test07=true := by
  decide +kernel

private theorem frame085scope07 : fits07.all frame085test07=true := by
  have h32 := stitchAt 32 3 frame085scope07_s032 frame085scope07_end
  have h28 := stitchAt 28 4 frame085scope07_s028 h32
  have h24 := stitchAt 24 4 frame085scope07_s024 h28
  have h20 := stitchAt 20 4 frame085scope07_s020 h24
  have h16 := stitchAt 16 4 frame085scope07_s016 h20
  have h12 := stitchAt 12 4 frame085scope07_s012 h16
  have h8 := stitchAt 8 4 frame085scope07_s008 h12
  have h4 := stitchAt 4 4 frame085scope07_s004 h8
  have h0 := stitchAt 0 4 frame085scope07_s000 h4
  simpa only [List.drop_zero] using h0

private theorem frame085batch07 : batch07.pickTest original frame172=true :=
  FitBatch.pickTest_of_scoped scoped085 frame085scope07

private theorem frameBatches085 : [batch00,batch01,batch02,batch03,batch04,batch05,batch06,batch07].all (FitBatch.pickTest original frame172)=true := by
  simp only [List.all_cons,List.all_nil,frame085batch00,frame085batch01,frame085batch02,frame085batch03,frame085batch04,frame085batch05,frame085batch06,frame085batch07,Bool.and_self]

theorem frameOK085 : frameRankTest original useStop frame172=true :=
  frameRankTest_of_batch_checkpoints planChecked frameBatches085


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
