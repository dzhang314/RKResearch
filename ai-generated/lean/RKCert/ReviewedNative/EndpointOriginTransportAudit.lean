module

public import RKCert.ReviewedNative.EndpointOriginTransport

public section

namespace RKResearch.Certified.Graded.Reverse

open RKResearch
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {t : Fin s}
variable (last : LastActive b t) (ha : ∀ i j, i ≤ j → A i j = 0)

include last ha

example : reflectedClock A t = 0 ↔ firstSeed A b t = 0 :=
  last.reflected_zero_iff_firstSeed_at_last ha

example (C : ℕ → Submodule K (Fin s → K)) (n : ℕ)
    (credit : ∀ k < n, reflectedClock A t = 0 → C k ≤ tailZero t) :
    reflectedClock A t = 0 ↔ ∀ w ∈ adjointFlag A b C n, w t = 0 :=
  last.reflected_zero_iff_adjointFlag_vanishes ha C n credit

example (n : ℕ) : reflectedClock A t = 0 ↔ ∀ w ∈ back A b n, w t = 0 :=
  last.reflected_zero_iff_back_vanishes ha n

example (n : ℕ) : reflectedClock A t = 0 ↔ ∀ w ∈ primitiveBack A b n, w t = 0 :=
  last.reflected_zero_iff_primitiveBack_vanishes ha n

example (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) (V : Submodule K (Fin s → K))
    (credit : ∀ k < n, reflectedClock A t = 0 → C k ≤ tailZero t)
    (sat : adjointFlag A b C n = annih V) :
    reflectedClock A t = 0 ↔ coordinate (K:=K) t ∈ V :=
  last.reflected_zero_iff_coordinate_mem_of_adjointFlag_eq_annih ha C n V credit sat

example (n : ℕ) (V : Submodule K (Fin s → K)) (sat : back A b n = annih V) :
    reflectedClock A t = 0 ↔ coordinate (K:=K) t ∈ V :=
  last.reflected_zero_iff_coordinate_mem_of_back_eq_annih ha n V sat

example (n : ℕ) (V : Submodule K (Fin s → K)) (sat : primitiveBack A b n = annih V) :
    reflectedClock A t = 0 ↔ coordinate (K:=K) t ∈ V :=
  last.reflected_zero_iff_coordinate_mem_of_primitiveBack_eq_annih ha n V sat

example (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) (V : Submodule K (Fin s → K))
    (inc : adjointFlag A b C n ≤ annih V) (ht : coordinate (K:=K) t ∈ V) :
    reflectedClock A t = 0 :=
  last.reflected_zero_of_coordinate_mem_of_adjointFlag_le_annih ha C n V inc ht

example {p : ℕ} (ho : HasOrder p A b) (j : ℕ) (pay : j+2 ≤ p)
    (ht : coordinate (K:=K) t ∈ treeSpace A j) :
    reflectedClock A t = 0 :=
  last.reflected_zero_of_coordinate_mem_treeSpace ha ho j pay ht

#print axioms LastActive.reflected_zero_iff_firstSeed_at_last
#print axioms LastActive.reflected_zero_iff_adjointFlag_vanishes
#print axioms LastActive.reflected_zero_iff_back_vanishes
#print axioms LastActive.reflected_zero_iff_primitiveBack_vanishes
#print axioms LastActive.reflected_zero_iff_coordinate_mem_of_adjointFlag_eq_annih
#print axioms LastActive.reflected_zero_iff_coordinate_mem_of_back_eq_annih
#print axioms LastActive.reflected_zero_iff_coordinate_mem_of_primitiveBack_eq_annih
#print axioms LastActive.reflected_zero_of_coordinate_mem_of_adjointFlag_le_annih
#print axioms LastActive.reflected_zero_of_coordinate_mem_treeSpace

end RKResearch.Certified.Graded.Reverse
