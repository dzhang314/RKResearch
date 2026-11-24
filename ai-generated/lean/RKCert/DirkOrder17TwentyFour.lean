module
public import RKCert.Dirk17OnlyEarly
public import RKCert.Dirk17EarlySurplus
@[expose] public section
namespace RKCert.Paired
open Module Terminal RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- Unrestricted DIRK of full rooted-tree order at least 17 requires 24
original stages over any characteristic-zero field with no square root of -6.
Neither a chosen order nor positivity of tableau data is required. -/
theorem dirk_order17_twenty_four_no_sqrt_neg_six (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:17≤p) (field:¬∃z:K,z^2= -6):24≤s:=by
  have paid:HasTreeOrderAtLeast A b 17:=fun t ht=>ho t (ht.trans hp)
  have floor:=odd_floor (m:=8) (by decide) ha paid
  by_contra! short
  have eq:s=23:=by omega
  subst s
  obtain ⟨anc,sur⟩:=Seventeen.only_early ha paid (noExceptionalRatio_iff.mpr field)
  exact Seventeen.no_early ha paid anc sur

/-- Ordered characteristic-zero fields; in particular the field of real
numbers. No sign hypotheses are imposed on individual RK coefficients. -/
theorem dirk_order17_twenty_four_ordered_field {L:Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    {A:Fin s→Fin s→L} {b:Vec L s} (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:17≤p):24≤s:=
  dirk_order17_twenty_four_no_sqrt_neg_six ha ho hp (noExceptionalRatio_iff.mp noExceptionalRatio_ordered)

end RKCert.Paired
