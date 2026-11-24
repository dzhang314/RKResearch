module

public import RKCert.ReviewedNative.LobattoDIRK88Data

@[expose] public section

namespace RKResearch.Certified.LobattoDIRK88

def checkSpan (f : Fin Count → Bool) (s n : ℕ) : Bool :=
  (List.range' s n).all (fun i => f (tag i))

def gradeOK (i : Fin Count) : Bool :=
  decide (0 < (keys i).order) &&
    (List.range 9).all (fun q => decide ((keys i).order ≤ q → i.val < cutoff q))

end RKResearch.Certified.LobattoDIRK88
