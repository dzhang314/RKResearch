import RKCert.ReviewedNative.ExteriorSignSwitchSharpness

open Polynomial
open RKCert.ReviewedNative.FormalSignedQuadrature
open RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (T : Finset K) (mu : K → K) (A : K[X]) (a : K)

#check (exteriorSignSwitchCost_le_degree_at_anchor (T := T) (mu := mu) (A := A) (a := a) :
  (∀ x ∈ exteriorSites T, mu x ≠ 0) →
    a ∈ Set.Ioo (0 : K) 1 → 0 < A.eval a →
    (∀ x ∈ exteriorSites T, mu x * A.eval x ≤ 0) →
    exteriorSignSwitchCost T mu ≤ A.natDegree)

#check (exteriorSignSwitchCost_isLeast_degree T mu :
  (∀ x ∈ exteriorSites T, mu x ≠ 0) →
    IsLeast {d : ℕ | ∃ B : K[X], B.natDegree = d ∧
      (∀ x ∈ Set.Ioo (0 : K) 1, 0 < B.eval x) ∧
      (∀ x ∈ exteriorSites T, mu x * B.eval x ≤ 0)} (exteriorSignSwitchCost T mu))
end

#print axioms RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch.exteriorSignSwitchCost_isLeast_degree
