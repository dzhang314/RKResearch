import RKCert.ReviewedNative.OneOffReceiverPrefix

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.OneOff
open Module
open scoped Matrix Classical

#print axioms origin_of_single_off
#print axioms mDef_prefix
#print axioms first_h_split
#print axioms FirstH.restricted_profile
#print axioms forward_minimal_ranks
#print axioms order9_first_h_of_capacity
#print axioms constant_amplitude_of_dependent_square
#print axioms independent_square_on_first_impossible
#print axioms independent_square_off_first_impossible
#print axioms order9_constant_amplitude_of_capacity
#print axioms ConstantAmplitude.off_weight_cancel
#print axioms grade_two_span
#print axioms ConstantAmplitude.receiver_order_two
#print axioms ConstantAmplitude.predecessor_defect_space

-- Import-only consumer; neither the old tree nor its order bridge is on LEAN_PATH.
example {K : Type*} [Field K] [CharZero K]
    {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 9 A b)
    (off : (offKnots A).card = 1) (cap : finrank K (treeSpace A 4) ≤ 8) :
    ∃ j : Fin 12, HasOrder 2
      ((nodes A j)⁻¹ • prefixMatrix A j.isLt.le) (fun l : Fin j.val => (nodes A j)⁻¹ * A j (Fin.castLE j.isLt.le l)) := by
  obtain ⟨a,d,i,j,D⟩ := order9_constant_amplitude_of_capacity ha ho off cap
  exact ⟨j,D.receiver_order_two ha⟩
