import Lean.Elab.Tactic.Omega

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSquareSlots

/-- Mandatory seven ordinary representatives, one slot per dirty
row, then the increments for the three sorts of square-mass fibers. -/
theorem slot_census {z q i o x : Nat}
    (hz : 1≤z) (hq : 4≤q) (ho : o≤1)
    (split : q=i+o+x) (h : 7+z+q+2*x+o≤13) :
    z≤2 ∧ x=0 ∧ 3≤i ∧ (2≤z → z=2 ∧ q=4 ∧ i=4 ∧ o=0) := by omega

theorem one_ghost_slots {q i o x : Nat}
    (hq : 4≤q) (ho : o≤1)
    (split : q=i+o+x) (h : 7+1+q+2*x+o≤13) :
    x=0 ∧ ((q=5 ∧ i=5 ∧ o=0) ∨ (q=4 ∧ i=4 ∧ o=0) ∨
           (q=4 ∧ i=3 ∧ o=1)) := by omega

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSquareSlots

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSquareSlots
#print axioms slot_census
#print axioms one_ghost_slots
