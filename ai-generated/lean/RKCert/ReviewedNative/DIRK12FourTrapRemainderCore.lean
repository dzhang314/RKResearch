/-! The sixteen scaled moments of the two exact four-trapezoid remainders. -/
namespace RKResearch.Certified.DIRK12FourTrapRemainder
def remainderA : List (Int × Int) :=
  [(1,-2400),(3,-1664),(4,-423),(6,-620),(8,-81),(9,-32),(10,-12)]
def remainderB : List (Int × Int) :=
  [(1,-132066),(3,-91025),(4,-24255),(6,-31328),(7,-4950),(9,-4070),(11,-81)]
def scaledTest (r : List (Int × Int)) (d : Int) (j : Nat) : Prop :=
  let t : Int := Int.ofNat j
  (r.foldl (fun a q => a + q.2 * q.1^j) 0) *
    (t+1)*(t+2)*(t+3)*(t+4) = -d * (12 : Int)^j

instance (r : List (Int × Int)) (d : Int) (j : Nat) : Decidable (scaledTest r d j) := by
  unfold scaledTest
  infer_instance

theorem remainderA_paid_moments : ∀ j : Fin 8, scaledTest remainderA 138600 (j.val+1) := by
  decide
theorem remainderB_paid_moments : ∀ j : Fin 8, scaledTest remainderB 7623000 (j.val+1) := by
  decide
end RKResearch.Certified.DIRK12FourTrapRemainder

#print axioms RKResearch.Certified.DIRK12FourTrapRemainder.remainderA_paid_moments
#print axioms RKResearch.Certified.DIRK12FourTrapRemainder.remainderB_paid_moments
