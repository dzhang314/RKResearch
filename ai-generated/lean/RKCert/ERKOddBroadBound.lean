module
public import RKCert.ERKOddBroadScalar

@[expose] public section
/-! # Native numerical exclusion for a genuinely broad first adjoint -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired.Clock RKCert.Paired.ReverseHull RKCert.Endpoint
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_erk17_broad_linear_stage_bound
    {s:ℕ}{A:Fin s→Fin s→K}{b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (wide:9≤(headSites (mirror A) (backSeed1 A b)).card):
    27≤s:=by
  by_contra! small
  have lo:=odd_rank_floor_from_eight (q:=8) ha ho (by decide)
  have s26:s=26:=by omega
  subst s
  have nz:backSeed1 A b≠0:=by
    intro z
    rw [z] at wide
    simp [headSites] at wide
  have S:OddBalanced (s:=25) A b 8:=balanced_odd_ranks ha ho (by decide) (by decide)
  have W:=balanced_odd_broad_or_local ha ho (by decide) (by decide) S nz
  rcases W with bad|⟨n,whole⟩
  · change (headSites (mirror A) (backSeed1 A b)).card≤2 at bad
    omega
  have C:BroadLinearCover A b 8 7:=
    broad_linear_cover_of_orbit (by decide) (show 8<(headSites (mirror A) (backSeed1 A b)).card from wide) whole
  exact C.impossible ha ho S
end RKCert.Paired.FiniteMidpoint

