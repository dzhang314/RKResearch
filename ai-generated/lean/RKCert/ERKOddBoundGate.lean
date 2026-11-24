module
public import RKCert.ERKOddNonzeroBound
public import RKCert.ERKOddPencilArithmetic

@[expose] public section
/-! # Complete native order-17 reduction to one explicit arithmetic certificate -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired.ERKOddHidden RKCert.FixedPolynomial Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_erk17_stage_bound_of_pencil_gate
    (gate:∀(P:K[X])(a u:K),OddPencilPorts P a u→False)
    {s:ℕ}{A:Fin s→Fin s→K}{b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17):27≤s:=by
  by_cases nz:backSeed1 A b=0
  · exact odd17_zero_stage_bound_of_gate gate ha ho nz
  · exact ordered_erk17_nonzero_stage_bound ha ho nz

theorem ordered_erk17_stage_bound_of_norm_pair
    (cert:Order15GoodPrimePair (nodeMomentNorm 7 5 1 0) (nodeMomentNorm 7 5 2 0) 210 210)
    {s:ℕ}{A:Fin s→Fin s→K}{b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17):27≤s:=
  ordered_erk17_stage_bound_of_pencil_gate (odd_pencil_impossible_of_pair cert) ha ho

end RKCert.Paired.FiniteMidpoint
