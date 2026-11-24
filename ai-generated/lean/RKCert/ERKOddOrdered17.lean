module
public import RKCert.ERKOddBoundGate
public import RKCert.ERK17Norm.Pair

@[expose] public section
/-! # Explicit RK order seventeen over an ordered field needs twenty-seven stages -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.FixedPolynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_erk17_stage_bound
    {s:ℕ}{A:Fin s→Fin s→K}{b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17):27≤s:=
  ordered_erk17_stage_bound_of_norm_pair ERK17.OddPencil7K5E0 ha ho

end RKCert.Paired.FiniteMidpoint
