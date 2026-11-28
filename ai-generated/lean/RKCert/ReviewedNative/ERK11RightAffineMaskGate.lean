/-! Core field cancellation for the physical right plateau collision. -/
namespace RKResearch.ERK11RightAffineMaskGate
open Lean.Grind

theorem rightChronologicalAlias {K : Type} [Field K] (H C z d : K)
    (hH : H≠0) (hz : H*z=C) (hc : C-d*H=0) :
    z=d := by
  rw [← hz] at hc
  have he : H*(z-d)=0 := by calc
    H*(z-d) = H*z-d*H := by grind
    _ = 0 := hc
  grind

end RKResearch.ERK11RightAffineMaskGate
#print axioms RKResearch.ERK11RightAffineMaskGate.rightChronologicalAlias
