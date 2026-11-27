module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBase
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA3
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckA6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckC0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckC3
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckC6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckS0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckS3
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckS6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckS9
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckMoments0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckMoments3
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckMoments6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckMoments9
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts0
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts1
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts2
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts3
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts4
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts5
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts6
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts7
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts8
public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckProducts9
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem arA (d : Nat) (hd : d < 9) : blockA d = true := by
  interval_cases d
  · exact chk_A0
  · exact chk_A1
  · exact chk_A2
  · exact chk_A3
  · exact chk_A4
  · exact chk_A5
  · exact chk_A6
  · exact chk_A7
  · exact chk_A8

theorem arC (d : Nat) (hd : d < 9) : blockC d = true := by
  interval_cases d
  · exact chk_C0
  · exact chk_C1
  · exact chk_C2
  · exact chk_C3
  · exact chk_C4
  · exact chk_C5
  · exact chk_C6
  · exact chk_C7
  · exact chk_C8

theorem arS (d : Nat) (hd : d < 10) : blockS d = true := by
  interval_cases d
  · exact chk_S0
  · exact chk_S1
  · exact chk_S2
  · exact chk_S3
  · exact chk_S4
  · exact chk_S5
  · exact chk_S6
  · exact chk_S7
  · exact chk_S8
  · exact chk_S9

theorem arp (d e : Nat) (h : d+e < 10) : blockP d e = true := by
  have hn : d < 10 := by omega
  interval_cases d
  · have he : e < 10 := by omega
    interval_cases e
    · exact chk_m0_0
    · exact chk_m0_1
    · exact chk_m0_2
    · exact chk_m0_3
    · exact chk_m0_4
    · exact chk_m0_5
    · exact chk_m0_6
    · exact chk_m0_7
    · exact chk_m0_8
    · exact chk_m0_9
  · have he : e < 9 := by omega
    interval_cases e
    · exact chk_m1_0
    · exact chk_m1_1
    · exact chk_m1_2
    · exact chk_m1_3
    · exact chk_m1_4
    · exact chk_m1_5
    · exact chk_m1_6
    · exact chk_m1_7
    · exact chk_m1_8
  · have he : e < 8 := by omega
    interval_cases e
    · exact chk_m2_0
    · exact chk_m2_1
    · exact chk_m2_2
    · exact chk_m2_3
    · exact chk_m2_4
    · exact chk_m2_5
    · exact chk_m2_6
    · exact chk_m2_7
  · have he : e < 7 := by omega
    interval_cases e
    · exact chk_m3_0
    · exact chk_m3_1
    · exact chk_m3_2
    · exact chk_m3_3
    · exact chk_m3_4
    · exact chk_m3_5
    · exact chk_m3_6
  · have he : e < 6 := by omega
    interval_cases e
    · exact chk_m4_0
    · exact chk_m4_1
    · exact chk_m4_2
    · exact chk_m4_3
    · exact chk_m4_4
    · exact chk_m4_5
  · have he : e < 5 := by omega
    interval_cases e
    · exact chk_m5_0
    · exact chk_m5_1
    · exact chk_m5_2
    · exact chk_m5_3
    · exact chk_m5_4
  · have he : e < 4 := by omega
    interval_cases e
    · exact chk_m6_0
    · exact chk_m6_1
    · exact chk_m6_2
    · exact chk_m6_3
  · have he : e < 3 := by omega
    interval_cases e
    · exact chk_m7_0
    · exact chk_m7_1
    · exact chk_m7_2
  · have he : e < 2 := by omega
    interval_cases e
    · exact chk_m8_0
    · exact chk_m8_1
  · have he : e < 1 := by omega
    interval_cases e
    · exact chk_m9_0

theorem arPrim (d : Nat) (hd : d < 9) : checkPrimitive packet d = true := by
  interval_cases d
  · exact chk_P0
  · exact chk_P1
  · exact chk_P2
  · exact chk_P3
  · exact chk_P4
  · exact chk_P5
  · exact chk_P6
  · exact chk_P7
  · exact chk_P8

theorem arScalar (d : Nat) (hd : d < 10) : checkScalar packet d = true := by
  interval_cases d
  · exact chk_Q0
  · exact chk_Q1
  · exact chk_Q2
  · exact chk_Q3
  · exact chk_Q4
  · exact chk_Q5
  · exact chk_Q6
  · exact chk_Q7
  · exact chk_Q8
  · exact chk_Q9

theorem receipts : Receipts packet := by
  refine ⟨chk_node,?_,?_,?_,arPrim,?_,arScalar,chk_bush⟩
  · intro d hd i
    exact List.all_eq_true.mp (arA d hd) i (List.mem_finRange i)
  · intro d hd i
    exact List.all_eq_true.mp (arC d hd) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp
      (List.all_eq_true.mp (arp d e hd) i (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd i
    exact List.all_eq_true.mp (arS d hd) i (List.mem_finRange i)

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
