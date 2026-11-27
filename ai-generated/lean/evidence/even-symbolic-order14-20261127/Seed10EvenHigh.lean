module
public import Seed10Even
import all Seed10Even
import all Certificate10
@[expose] public section
namespace RKResearch.Certified.Seed10EvenHigh
open RootedTreeGram TwoDonorDense StrictSDIRKGram22Order10

def high (i : Fin 2) : Fin 5 := ⟨3+i.val, by have := i.isLt; omega⟩
private theorem last_energy (i : Fin 2) :
    energy (cov 6) (localForm (Seed10Even.donor (high i)) (Seed10Even.num (high i))
      (Seed10Even.den (high i)) 6) = 0 :=
  of_decide_eq_true (List.all_eq_true.mp (show (List.finRange 2).all (fun j => decide
    (energy (cov 6) (localForm (Seed10Even.donor (high j)) (Seed10Even.num (high j))
      (Seed10Even.den (high j)) 6) = 0)) = true from by decide +kernel) i (List.mem_finRange i))

theorem pure_high (i : Fin 2) : PureAt A (Seed10Even.donor (high i)) 7 := by
  apply trace.pureAt_of_local castA (by decide +kernel) (Seed10Even.donor (high i))
    (Seed10Even.num (high i)) (Seed10Even.den (high i))
    (Seed10Even.den_ne (high i)) (Seed10Even.donor_clock (high i)) (by decide)
  intro g hg
  by_cases h : g < 6
  · exact Seed10Even.sample_energies (high i) ⟨g,h⟩
  · have hg' : g=6 := by omega
    rw [hg']
    exact last_energy i
#print axioms pure_high
end RKResearch.Certified.Seed10EvenHigh
