module
import RKCert.ReviewedNative.ERKOrderTwelveCoreAdmission

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.ERK12 Module

section ActualOrderTwelve
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (h : HasOrder A b 12) (cap : s+1≤17)

example : ∃ r U w, ForwardStaircase A r U w ∧ zeroSpace A 2≤U ∧ 2≤r ∧ r≤4 := by
  have S := saturation_of_order ha h cap
  have T := terminal_band ha h S
  obtain ⟨r,U,w,F⟩ := forward_staircase ha h S
  have admit := grade_two_in_core ha h S T F
  have low := zeroSpace_finrank ha h (n:=1) (by decide)
  change 1≤finrank K (zeroSpace A 2) at low
  have width := Submodule.finrank_mono admit
  have base := F.initial.baseRank
  have five := S.f5
  exact ⟨r,U,w,F,admit,F.length,by omega⟩
end ActualOrderTwelve

#print axioms buffered_clock_sup
#print axioms paid_buffered_clock_step
#print axioms HeadFiber.core_product_of_clock_slices
#print axioms HeadFiber.first_unmatched_joint_block
#print axioms HeadFiber.joint_prefix_detector
#print axioms forward_staircase
#print axioms grade_two_multiplier_stable
#print axioms grade_two_multiplier_profile
#print axioms grade_two_in_core
