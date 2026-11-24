module
import RKCert.ReviewedNative.ERKEvenHorizon
import Mathlib.Data.ZMod.Basic

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Module
universe u

section Field
variable {K : Type u} [Field K] {s p q : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
variable (ha : ∀ i j, i ≤ j → A i j=0) (h : HasOrder p A b)

example (hq : 2≤q) (pay : 2*q≤p) :
    2*q-1+finrank K (zeroSpace A q)+finrank K (back A b 0) ≤ s :=
  erk_even_midpoint_budget ha h hq pay

example (hq : 1≤q) (pay : 2*q+1≤p) (d : ℕ) (surplus : q-1+d≤finrank K (zeroSpace A q)) :
    3*q+d ≤ s := by
  have room := erk_odd_midpoint_budget ha h hq pay
  omega

example (hq : 2≤q) (pay : 2*q≤p) (cap : s≤3*q-2) :
    ∃ t, (∀ i, i≤t) ∧ LastActive b t ∧ nodes A t=1 ∧ coordinate (K:=K) t ∈ treeSpace A q :=
  (erk_even_horizon_of_stage_cap ha h hq pay cap).terminal

end Field

section Ring
variable {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ha : ∀ i j, i ≤ j → A i j=0)

example (h : HasOrder p A b) : max p ((3*p+1)/2-2) ≤ s := h.erk_uniform_stages ha

example (h : HasOrder p A b) : erkUniformFloor p ≤ s := h.erk_uniform_floor_le_stages ha

example (h : HasOrder 5 A b) : 6≤s := h.erk_uniform_stages ha

example (h : HasOrder 6 A b) : 7≤s := h.erk_uniform_stages ha

example (h : HasOrder 20 A b) : 28≤s := h.erk_uniform_stages ha

end Ring

/-- The fifth-order test is not vacuous from denominator arithmetic: all
integers 1 through 5 are units in this non-field. -/
example {A : Matrix (Fin 5) (Fin 5) (ZMod 77)} {b : Fin 5 → ZMod 77}
    (ha : ∀ i j, i ≤ j → A i j=0) : ¬ HasOrder 5 A b := by
  intro h
  let _ : Fact (1 < 77) := ⟨by decide⟩
  exact (by decide : ¬max 5 ((3*5+1)/2-2)≤5) (h.erk_uniform_stages ha)

example {A : Matrix (Fin 26) (Fin 26) (ZMod 23)} {b : Fin 26 → ZMod 23}
    (ha : ∀ i j, i ≤ j → A i j=0) : ¬ HasOrder 19 A b := by
  intro h
  let _ : Fact (1 < 23) := ⟨by decide⟩
  exact (by decide : ¬max 19 ((3*19+1)/2-2)≤26) (h.erk_uniform_stages ha)

#check RKResearch.HasOrder.erk_uniform_stages
#print axioms RKResearch.HasOrder.strict_lower_triangular_of_all_fields
#print axioms erk_midpoint_tree_rank
#print axioms erk_even_midpoint_budget
#print axioms erk_odd_midpoint_budget
#print axioms erk_even_horizon_of_stage_cap
#print axioms RKResearch.HasOrder.erk_uniform_stages_field
#print axioms RKResearch.HasOrder.erk_uniform_stages
#print axioms RKResearch.HasOrder.erk_uniform_floor_le_stages
#print axioms RKResearch.erkUniformFloor_through_twenty
