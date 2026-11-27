module

public import RKCert.ReviewedNative.DIRK10RationalTwelveFlagReplayMoments
public import RKCert.ReviewedNative.DIRK10RationalTwelveFlagReplayActionsA
public import RKCert.ReviewedNative.DIRK10RationalTwelveFlagReplayActionsC
public import RKCert.ReviewedNative.DIRK10RationalTwelveFlagReplaySilence
public import RKCert.ReviewedNative.DIRK10RationalTwelveFlagReplayProducts
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.DIRK10RationalTwelveFlagReplay
open RKResearch RationalFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem stepA (d : ℕ) (hd : d < 9) : blockA d = true := by
  interval_cases d
  · exact actA0
  · exact actA1
  · exact actA2
  · exact actA3
  · exact actA4
  · exact actA5
  · exact actA6
  · exact actA7
  · exact actA8

theorem stepC (d : ℕ) (hd : d < 9) : blockC d = true := by
  interval_cases d
  · exact actC0
  · exact actC1
  · exact actC2
  · exact actC3
  · exact actC4
  · exact actC5
  · exact actC6
  · exact actC7
  · exact actC8

theorem silence (d : ℕ) (hd : d < 10) : blockS d = true := by
  interval_cases d
  · exact silent0
  · exact silent1
  · exact silent2
  · exact silent3
  · exact silent4
  · exact silent5
  · exact silent6
  · exact silent7
  · exact silent8
  · exact silent9

theorem primitiveReceipt (d : ℕ) (hd : d < 9) : checkPrimitive packet d = true := by
  interval_cases d
  · exact primitive0
  · exact primitive1
  · exact primitive2
  · exact primitive3
  · exact primitive4
  · exact primitive5
  · exact primitive6
  · exact primitive7
  · exact primitive8

theorem scalarReceipt (d : ℕ) (hd : d < 10) : checkScalar packet d = true := by
  interval_cases d
  · exact scalar0
  · exact scalar1
  · exact scalar2
  · exact scalar3
  · exact scalar4
  · exact scalar5
  · exact scalar6
  · exact scalar7
  · exact scalar8
  · exact scalar9

theorem products (d e : ℕ) (h : d+e < 10) : blockP d e = true := by
  have hd : d < 10 := by omega
  interval_cases d
  · have he : e < 10 := by omega
    interval_cases e
    · exact product0_0
    · exact product0_1
    · exact product0_2
    · exact product0_3
    · exact product0_4
    · exact product0_5
    · exact product0_6
    · exact product0_7
    · exact product0_8
    · exact product0_9
  · have he : e < 9 := by omega
    interval_cases e
    · exact product1_0
    · exact product1_1
    · exact product1_2
    · exact product1_3
    · exact product1_4
    · exact product1_5
    · exact product1_6
    · exact product1_7
    · exact product1_8
  · have he : e < 8 := by omega
    interval_cases e
    · exact product2_0
    · exact product2_1
    · exact product2_2
    · exact product2_3
    · exact product2_4
    · exact product2_5
    · exact product2_6
    · exact product2_7
  · have he : e < 7 := by omega
    interval_cases e
    · exact product3_0
    · exact product3_1
    · exact product3_2
    · exact product3_3
    · exact product3_4
    · exact product3_5
    · exact product3_6
  · have he : e < 6 := by omega
    interval_cases e
    · exact product4_0
    · exact product4_1
    · exact product4_2
    · exact product4_3
    · exact product4_4
    · exact product4_5
  · have he : e < 5 := by omega
    interval_cases e
    · exact product5_0
    · exact product5_1
    · exact product5_2
    · exact product5_3
    · exact product5_4
  · have he : e < 4 := by omega
    interval_cases e
    · exact product6_0
    · exact product6_1
    · exact product6_2
    · exact product6_3
  · have he : e < 3 := by omega
    interval_cases e
    · exact product7_0
    · exact product7_1
    · exact product7_2
  · have he : e < 2 := by omega
    interval_cases e
    · exact product8_0
    · exact product8_1
  · have he : e < 1 := by omega
    interval_cases e
    · exact product9_0

theorem receipts : Receipts 10 packet := by
  refine ⟨node,?_,?_,?_,?_,?_,scalarReceipt⟩
  · intro d hd i
    exact List.all_eq_true.mp (stepA d (by omega)) i (List.mem_finRange i)
  · intro d hd i
    exact List.all_eq_true.mp (stepC d (by omega)) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp (List.all_eq_true.mp (products d e hd) i
      (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd
    exact primitiveReceipt d (by omega)
  · intro d hd i
    exact List.all_eq_true.mp (silence d hd) i (List.mem_finRange i)

/-- The literal lower triangular rational matrix satisfies all reviewed
rooted-tree order conditions through ten. -/
theorem order_ten : HasOrder 10 (matrix packet) packet.b :=
  RationalFlagReplay.order receipts

theorem not_order_eleven : ¬ HasOrder 11 (matrix packet) packet.b :=
  no_order_succ receipts (by rw [next_star]; decide +kernel)

theorem lower_triangular : (matrix packet).IsLowerTriangular :=
  lower packet

theorem exists_exact :
    ∃ (A : Matrix (Fin 12) (Fin 12) ℚ) (b : Fin 12 → ℚ),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b :=
  ⟨matrix packet,packet.b,lower_triangular,order_ten,not_order_eleven⟩

end RKResearch.Certified.DIRK10RationalTwelveFlagReplay

#print axioms RKResearch.Certified.DIRK10RationalTwelveFlagReplay.order_ten
#print axioms RKResearch.Certified.DIRK10RationalTwelveFlagReplay.exists_exact
