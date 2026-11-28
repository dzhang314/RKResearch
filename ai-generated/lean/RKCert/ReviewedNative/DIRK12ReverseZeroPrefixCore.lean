/-! Exact scalar gates in the local modulus-37 reverse-prefix obstruction. -/
namespace RKResearch.Certified.DIRK12ReverseZeroPrefix

def pairs : List (Int × Int) :=
  [(24,33),(10,32),(33,17),(19,6),(5,17),(28,32),(14,33)]

theorem first_two_numerators_zero :
    (148 : Int) % 37 = 0 ∧ (962 : Int) % 37 = 0 ∧
    (31185 : Int) % 37 ≠ 0 ∧ (5145525 : Int) % 37 ≠ 0 := by
  decide

theorem no_literal_diagonal :
    ∀ (i : Fin pairs.length) (a : Fin 37),
      let (y,w) := pairs[i.val]
      let k : Int := Int.ofNat a.val
      ¬ ((2*k*w*y-w*y^2) % 37 = 0 ∧ (3*k*w*y^2-w*y^3) % 37 = 0) := by
  decide

end RKResearch.Certified.DIRK12ReverseZeroPrefix

#print axioms RKResearch.Certified.DIRK12ReverseZeroPrefix.first_two_numerators_zero
#print axioms RKResearch.Certified.DIRK12ReverseZeroPrefix.no_literal_diagonal
