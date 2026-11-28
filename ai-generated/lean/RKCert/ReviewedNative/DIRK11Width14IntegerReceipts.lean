module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsBase
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA3From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA4From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA5From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA6From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA6From2
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA6From4
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA7From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA7From2
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA7From4
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA7From6
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA8From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA8From2
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA8From4
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA8From6
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA8From8
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA8From10
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA9From0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA9From2
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA9From4
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA9From6
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA9From8
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsA9From10
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsCS0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsCS3
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsCS6
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsCS9
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsQ0
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsQ2
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsQ4
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsQ6
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsQ8
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsQ10
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsP3
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsP4
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsP5
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsP6
public import RKCert.ReviewedNative.DIRK11Width14IntegerBitsP7
import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem allC (d : Nat) (hd : d < 10) : blockC d = true := by
  interval_cases d
  · exact chk_c0
  · exact chk_c1
  · exact chk_c2
  · exact chk_c3
  · exact chk_c4
  · exact chk_c5
  · exact chk_c6
  · exact chk_c7
  · exact chk_c8
  · exact chk_c9

theorem allS (d : Nat) (hd : d < 11) : blockS d = true := by
  interval_cases d
  · exact chk_s0
  · exact chk_s1
  · exact chk_s2
  · exact chk_s3
  · exact chk_s4
  · exact chk_s5
  · exact chk_s6
  · exact chk_s7
  · exact chk_s8
  · exact chk_s9
  · exact chk_s10

theorem allQ (d : Nat) (hd : d < 11) : checkScalar packet d = true := by
  interval_cases d
  · exact chk_q0
  · exact chk_q1
  · exact chk_q2
  · exact chk_q3
  · exact chk_q4
  · exact chk_q5
  · exact chk_q6
  · exact chk_q7
  · exact chk_q8
  · exact chk_q9
  · exact chk_q10

theorem allH (d : Nat) (hd : d < 10) : checkPrimitive packet d = true := by
  interval_cases d
  · exact chk_h0
  · exact chk_h1
  · exact chk_h2
  · exact chk_h3
  · exact chk_h4
  · exact chk_h5
  · exact chk_h6
  · exact chk_h7
  · exact chk_h8
  · exact chk_h9

theorem allA (d : Nat) (hd : d < 10) (i : Fin (packet.size d)) :
    checkA packet d i = true := by
  have hi := i.isLt
  have row (h : blockARow d i.val = true) : checkA packet d i = true := by
    simpa [blockARow,hi] using h
  apply row
  interval_cases d
  · change i.val < 0 at hi
    omega
  · change i.val < 0 at hi
    omega
  · change i.val < 0 at hi
    omega
  · change i.val < 1 at hi
    interval_cases i.val
    · exact chk_a3_0
  · change i.val < 2 at hi
    interval_cases i.val
    · exact chk_a4_0
    · exact chk_a4_1
  · change i.val < 3 at hi
    interval_cases i.val
    · exact chk_a5_0
    · exact chk_a5_1
    · exact chk_a5_2
  · change i.val < 5 at hi
    interval_cases i.val
    · exact chk_a6_0
    · exact chk_a6_1
    · exact chk_a6_2
    · exact chk_a6_3
    · exact chk_a6_4
  · change i.val < 8 at hi
    interval_cases i.val
    · exact chk_a7_0
    · exact chk_a7_1
    · exact chk_a7_2
    · exact chk_a7_3
    · exact chk_a7_4
    · exact chk_a7_5
    · exact chk_a7_6
    · exact chk_a7_7
  · change i.val < 11 at hi
    interval_cases i.val
    · exact chk_a8_0
    · exact chk_a8_1
    · exact chk_a8_2
    · exact chk_a8_3
    · exact chk_a8_4
    · exact chk_a8_5
    · exact chk_a8_6
    · exact chk_a8_7
    · exact chk_a8_8
    · exact chk_a8_9
    · exact chk_a8_10
  · change i.val < 12 at hi
    interval_cases i.val
    · exact chk_a9_0
    · exact chk_a9_1
    · exact chk_a9_2
    · exact chk_a9_3
    · exact chk_a9_4
    · exact chk_a9_5
    · exact chk_a9_6
    · exact chk_a9_7
    · exact chk_a9_8
    · exact chk_a9_9
    · exact chk_a9_10
    · exact chk_a9_11

theorem allP (d e : Nat) (h : d+e < 11) : blockP d e = true := by
  have hn : d < 11 := by omega
  interval_cases d
  · rfl
  · rfl
  · rfl
  · have he : e < 8 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact chk_p3_3
    · exact chk_p3_4
    · exact chk_p3_5
    · exact chk_p3_6
    · exact chk_p3_7
  · have he : e < 7 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact chk_p4_3
    · exact chk_p4_4
    · exact chk_p4_5
    · exact chk_p4_6
  · have he : e < 6 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact chk_p5_3
    · exact chk_p5_4
    · exact chk_p5_5
  · have he : e < 5 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact chk_p6_3
    · exact chk_p6_4
  · have he : e < 4 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact chk_p7_3
  · have he : e < 3 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · have he : e < 2 := by omega
    interval_cases e
    · decide +kernel
    · decide +kernel
  · have he : e < 1 := by omega
    interval_cases e
    · decide +kernel

theorem receipts : Receipts packet := by
  refine ⟨chk_node,allA,?_,?_,allH,?_,allQ,chk_failure⟩
  · intro d hd i
    exact List.all_eq_true.mp (allC d hd) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp
      (List.all_eq_true.mp (allP d e hd) i (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd i
    exact List.all_eq_true.mp (allS d hd) i (List.mem_finRange i)

end RKResearch.Certified.DIRK11Width14IntegerChecks
