import RKCert.ReviewedNative.DiagonalTwin

open RKResearch
open RKResearch.Certified.DiagonalTwin
open RKResearch.Certified.Graded (mergeCoefficient)

example {K : Type*} [CommRing K]
    (A12 : Matrix (Fin 12) (Fin 12) K) (b12 : Fin 12 → K) (γ : K)
    (hL : A12.IsLowerTriangular) (hDiag : ∀ k, A12 k k = γ) (hγ : γ ≠ 0)
    (hRow : ∀ k : Fin 12,
      A12 4 k - (if k = 4 then γ else 0) =
        A12 2 k - (if k = 2 then γ else 0))
    (h8 : HasOrder 8 A12 b12) :
    let B := contractMatrix (4 : Fin 12) (2 : Fin 11) A12
    let b := mergeCoefficient (4 : Fin 12) (2 : Fin 11) b12
    B.IsLowerTriangular ∧ (∀ k, B k k = γ) ∧ γ ≠ 0 ∧ HasOrder 8 B b := by
  have hc : (4 : Fin 12).succAbove (2 : Fin 11) < (4 : Fin 12) := by decide
  have hr : (4 : Fin 12).succAbove (2 : Fin 11) = (2 : Fin 12) := by decide
  have ht : DiagonalTwins (4 : Fin 12) (2 : Fin 11) γ A12 := by
    intro k
    simpa only [hr] using hRow k
  exact contract_strict_sdirk (n := 11) (p := 8)
    (j := (4 : Fin 12)) (r := (2 : Fin 11)) hc hL hDiag hγ ht h8
#print axioms RKResearch.Certified.DiagonalTwin.phi_diagonalTwins
#print axioms RKResearch.Certified.DiagonalTwin.hasOrder_diagonalTwins_iff
#print axioms RKResearch.Certified.DiagonalTwin.contract_strict_sdirk
