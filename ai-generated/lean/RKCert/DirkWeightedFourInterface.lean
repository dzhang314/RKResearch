module
public import RKCert.DirkShortTrace
public import RKCert.HeadChart
@[expose] public section
namespace RKCert.Paired.LocalProjection
open RKCert.Endpoint Polynomial RKCert.OneEscape
variable {K:Type*} [Field K] {s m:ℕ}
noncomputable section

/-- Exact finite package for the residual weighted fourth-grade pivot
obstruction. Its scalar base may have zeros; no order of a synthetic tableau
or product of two reverse rows is required. All chronology is physical in
the decreasing index direction. -/
structure WeightedFour (K:Type*) [Field K] (s:ℕ) where
  clock : Vec K s
  base : Vec K s
  head : Vec K s
  op : Vec K s→ₗ[K]Vec K s
  causal : ∀i:Fin s,∀ x z:Vec K s,(∀l,i ≤ l → x l=z l) → op x i=op z i
  quadrature : ∀P:K[X],P.natDegree≤7 → row (weightedEval clock base P) 1=(formalPrimitive P).eval 1
  primitive : ∀j:ℕ,3≤j → j≤5 → ∀P q:K[X],P.natDegree≤j → q.degree<(j-3:ℕ) →
    op (weightedEval clock base P-weightedEval clock head q) - weightedEval clock base (formalPrimitive P)
      ∈chain (diag clock) ⊥ head (j-2)
  commutator : ∀j:ℕ,3≤j → j≤4 → ∀P:K[X],P.natDegree≤j →
    commutatorR op (diag clock) (weightedEval clock base P)∈chain (diag clock) ⊥ head (j-1)

end
end RKCert.Paired.LocalProjection
