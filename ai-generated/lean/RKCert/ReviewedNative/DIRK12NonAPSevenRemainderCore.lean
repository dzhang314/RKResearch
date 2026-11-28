/-! Eight exact scaled moments of the non-arithmetic DIRK12 remainder. -/
namespace RKResearch.Certified.DIRK12NonAPSeven
def data : List (Int × Int) :=
  [(2,-531441),(6,-519750),(9,-90112),(12,-324324),(18,-150535),(24,-43848),(30,-5346)]
def test (j : Nat) : Prop :=
  let k := Int.ofNat j
  (data.foldl (fun s u => s + u.2*u.1^j) 0) *
   (k+1)*(k+2)*(k+3)*(k+4) = -42688800*(36 : Int)^j
instance (j : Nat) : Decidable (test j) := by
  unfold test
  infer_instance
theorem eight_scaled_moments : ∀ j : Fin 8, test (j.val+1) := by decide
end RKResearch.Certified.DIRK12NonAPSeven

#print axioms RKResearch.Certified.DIRK12NonAPSeven.eight_scaled_moments
