module

public import RKCert.UniformDIRK
public import RKCert.RationalDIRK7
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace RKCert.DIRKFloorRegression

/-- The previously checked rational witness and the unrestricted lower bound
meet, without restricting the competitors' diagonal or weights. -/
theorem order_seven_rational_minimum :
    IsLeast {s : ℕ | ∃ (A : Fin s → Fin s → ℚ) (b : Fin s → ℚ),
      (∀ i j, i.val < j.val → A i j = 0) ∧ HasTreeOrderAtLeast A b 7} 7 := by
  refine ⟨⟨RationalDIRK7.A,RationalDIRK7.b,RationalDIRK7.lowerTriangular,RationalDIRK7.order_seven⟩,?_⟩
  rintro s ⟨A,b,ha,ho⟩
  exact dirkRingFloor_le_stages ha ho

/-- A genuinely nonreduced test ring of positive characteristic, with a
nonzero nilpotent and no injective map to a field. -/
theorem nilpotent_mod529 : (23 : ZMod 529) ≠ 0 ∧ (23 : ZMod 529)^2 = 0 := by decide

theorem order_twenty_mod529 {s : ℕ} {A : Fin s → Fin s → ZMod 529} {b : Fin s → ZMod 529}
    (ha : ∀ i j, i.val < j.val → A i j = 0) (ho : HasTreeOrderAtLeast A b 20) :
    26 ≤ s := by
  let _ : Nontrivial (ZMod 529) := ⟨⟨0,1,by decide⟩⟩
  exact dirkRingFloor_le_stages ha ho

/-- The nontrivial-ring hypothesis cannot simply be dropped: the empty
tableau over the zero ring meets the full tree order conditions for every p. -/
theorem empty_zero_ring (p : ℕ) :
    HasTreeOrderAtLeast (s:=0) (fun _ _ => (0 : ZMod 1)) (fun _ => 0) p := by
  intro _ _
  exact Subsingleton.elim _ _

end RKCert.DIRKFloorRegression
