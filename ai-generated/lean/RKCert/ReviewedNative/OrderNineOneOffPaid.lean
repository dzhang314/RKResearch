module
public import RKCert.ReviewedNative.EndpointAdjoint
public import RKCert.ReviewedNative.OneOffReceiverPrefix

@[expose] public section

/-! # Native reverse capacity pays the order-nine forward chart

The reviewed tableau is unchanged throughout. The total-stage bound pays the
four reverse slots via `EndpointAdjoint`; no separate grade-four upper rank is
assumed in the physical one-off conclusions. -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem order9_forward_chart (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b 9) (stages : s ≤ 12) :
    s = 12 ∧ finrank K (zeroSpace A 3) = 2 ∧ finrank K (zeroSpace A 4) = 3 ∧
      finrank K (treeSpace A 3) = 6 ∧ finrank K (treeSpace A 4) = 8 := by
  have room := Reverse.orderNine_paid_room ha ho
  have cap : finrank K (treeSpace A 4) ≤ 8 := by omega
  cases s with
  | zero => omega
  | succ n =>
    have R := forward_minimal_ranks ha ho (by decide) cap
    exact ⟨by have := R.2.2.2; omega,R⟩

/-- All three physical amplitude branches are now decided directly from the
reviewed order, strict lower shape, and the twelve-stage ceiling. -/
theorem order9_constant_amplitude (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b 9) (stages : s ≤ 12) (off : (offKnots A).card = 1) :
    ∃ (a d : K) (i j : Fin s), ConstantAmplitude A a d i j := by
  have room := Reverse.orderNine_paid_room ha ho
  have cap : finrank K (treeSpace A 4) ≤ 8 := by omega
  cases s with
  | zero => omega
  | succ n =>
    exact constant_amplitude_of_single_off_of_capacity ha ho (by decide) off cap

/-- First clean receiver with its whole leading matrix and actual incoming
row. This is the reviewed order predicate, not a condition on a state quotient. -/
theorem order9_receiver_order_two (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b 9) (stages : s ≤ 12) (off : (offKnots A).card = 1) :
    ∃ j : Fin s, HasOrder ((nodes A j)⁻¹ • prefixMatrix A j.isLt.le)
      (fun l : Fin j.val => (nodes A j)⁻¹ * A j (Fin.castLE j.isLt.le l)) 2 := by
  obtain ⟨_,_,_,j,D⟩ := order9_constant_amplitude ha ho stages off
  exact ⟨j,D.receiver_order_two ha⟩

end RKResearch.Certified.Graded.OneOff
