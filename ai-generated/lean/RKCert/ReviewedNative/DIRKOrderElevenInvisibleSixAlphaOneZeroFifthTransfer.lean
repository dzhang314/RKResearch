import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroFifthTransfer

open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- Nothing after the literal target can participate in a triangular read. -/
theorem prefix_row_only_diagonal {s : Nat} {M : Fin s → Fin s → K}
    {f : Fin s → K} {i : Fin s}
    (hM : ∀ j k, j < k → M j k = 0)
    (hp : ∀ j, j < i → f j = 0) :
    (∑ j, M i j * f j) = M i i * f i := by
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · simp [hp j h]
    · simp [hM i j h]
  · simp

/-- At the first forward clean row the diagonal vanishes; at the fourth
reverse row the matched input itself vanishes. No relation between the
two later chronology positions is used. -/
theorem opposite_literal_ingress {s : Nat}
    {A N : Fin s → Fin s → K} {f D : Fin s → K} {b v : Fin s}
    (hA : ∀ j k, j < k → A j k = 0)
    (hN : ∀ j k, j < k → N j k = 0)
    (hf : ∀ j, j < b → f j = 0)
    (hD : ∀ j, j < v → D j = 0)
    (hdb : A b b = 0) (hDv : D v = 0)
    {J G L wt IQ : K}
    (hfwd : (∑ j, A b j * f j) = J)
    (hrev : (∑ j, N v j * D j) = G*L - wt*IQ) :
    J = 0 ∧ wt*IQ = G*L := by
  rw [prefix_row_only_diagonal hA hf, hdb, zero_mul] at hfwd
  rw [prefix_row_only_diagonal hN hD, hDv, mul_zero] at hrev
  exact ⟨hfwd.symm, (sub_eq_zero.mp hrev.symm).symm⟩

theorem homogeneous_first_pin {j0 j1 h0 h1 h2 t : K}
    (hj : j0+j1*t=0) (hh : h0+h1*t+h2*t^2=0) :
    j1^2*h0-j0*j1*h1+j0^2*h2=0 := by
  have h0' : j0 = -(j1*t) := by linear_combination hj
  rw [h0']
  linear_combination j1^2 * hh

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroFifthTransfer

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneZeroFifthTransfer
#print axioms prefix_row_only_diagonal
#print axioms opposite_literal_ingress
#print axioms homogeneous_first_pin
