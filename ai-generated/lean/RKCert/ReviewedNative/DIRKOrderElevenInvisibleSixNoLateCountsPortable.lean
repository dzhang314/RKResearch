import Lean.Elab.Tactic.Omega

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixNoLateCountsPortable

/-- Exact combinatorial census after the two paid chronology gates. -/
theorem all_counts {a b g : Nat} (ha : a ≤ 2) (hg : 3 ≤ g)
    (hs : a+b+g=6) :
    (a=0 ∧ ((b=0 ∧ g=6) ∨ (b=1 ∧ g=5) ∨ (b=2 ∧ g=4) ∨ (b=3 ∧ g=3))) ∨
    (a=1 ∧ ((b=0 ∧ g=5) ∨ (b=1 ∧ g=4) ∨ (b=2 ∧ g=3))) ∨
    (a=2 ∧ ((b=0 ∧ g=4) ∨ (b=1 ∧ g=3))) := by omega

/-- A nonconstant degree-at-most-three profile cannot enter the
six-initial-ghost branch once the paid forward degree bound is known. -/
theorem nonconstant_gamma {d g : Nat} (hd : d ≤ 3)
    (h : g ≤ d+2) (hmin : 3 ≤ g) :
    g=3 ∨ g=4 ∨ g=5 := by omega

theorem degree_one_gamma {g : Nat} (h : g≤1+2) (hmin : 3 ≤ g) : g=3 := by omega
theorem degree_two_gamma {g : Nat} (h : g≤2+2) (hmin : 3 ≤ g) :
    g=3 ∨ g=4 := by omega

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixNoLateCountsPortable

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixNoLateCountsPortable
#print axioms all_counts
#print axioms nonconstant_gamma
#print axioms degree_one_gamma
#print axioms degree_two_gamma
