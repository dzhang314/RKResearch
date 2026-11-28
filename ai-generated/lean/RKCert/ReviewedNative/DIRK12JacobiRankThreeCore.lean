/-!
Core-only exact residue tests for the degree-12 numerator and the Jacobi
quartic in the canonical rank-three third-copy chart. These are finite
arithmetic gates, not a native theorem for the surrounding tableau.
-/
namespace RKResearch.Certified.DIRK12JacobiRankThree

def numerator (x : Int) : Int :=
  ([4000000, -40800000, 167610000, -371374000, 514995300, -489665160,
    338552340, -175445532, 68020317, -19036726, 3582327, -399522, 19705]
    : List Int).foldl (fun q a => (q*x+a) % 11) 0

def quartic (x : Int) : Int :=
  ([66, -132, 84, -18, 1] : List Int).foldl (fun q a => (q*x+a) % 13) 0

theorem numerator_all_residues :
    (4000000 : Int) % 11 ≠ 0 ∧ ∀ x : Fin 11, numerator (Int.ofNat x.val) ≠ 0 := by
  decide

theorem quartic_all_residues :
    (66 : Int) % 13 ≠ 0 ∧ ∀ x : Fin 13, quartic (Int.ofNat x.val) ≠ 0 := by
  decide

end RKResearch.Certified.DIRK12JacobiRankThree

#print axioms RKResearch.Certified.DIRK12JacobiRankThree.numerator_all_residues
#print axioms RKResearch.Certified.DIRK12JacobiRankThree.quartic_all_residues
