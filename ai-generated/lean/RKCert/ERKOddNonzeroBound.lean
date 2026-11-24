module
public import RKCert.ERKOddBroadBound
public import RKCert.ERKOddLocalFiveClose
public import RKCert.ERKOddLocalFourClose

@[expose] public section
/-! # All native order-17 exclusions with nonzero first adjoint -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired.Clock RKCert.Paired.ReverseHull RKCert.Endpoint
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_erk17_nonzero_stage_bound
    {s:ℕ}{A:Fin s→Fin s→K}{b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(nz:backSeed1 A b≠0):27≤s:=by
  by_contra! small
  have lo:=odd_rank_floor_from_eight (q:=8) ha ho (by decide)
  have s26:s=26:=by omega
  subst s
  have S:OddBalanced (s:=25) A b 8:=balanced_odd_ranks ha ho (by decide) (by decide)
  rcases balanced_odd_broad_or_local ha ho (by decide) (by decide) S nz with few|⟨wide,_⟩
  · obtain ⟨r,U,τ,B⟩:=odd17_local_linear_band ha ho S nz few
    rcases B.forward_mask_rank ha ho S with h|⟨e,h,g,f⟩
    · exact B.five_forward_masks_impossible ha ho S nz h
    · subst r
      exact B.four_forward_masks_impossible ha ho S nz h g f
  · exact (not_le_of_gt small) (ordered_erk17_broad_linear_stage_bound ha ho wide)

end RKCert.Paired.FiniteMidpoint
