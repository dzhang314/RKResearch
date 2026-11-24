module
public import RKCert.Dirk17NonC2
public import RKCert.Dirk17NoMinimal
@[expose] public section
namespace RKCert.Paired.Seventeen
open Module RKCert.EndpointPhysical
variable {K:Type*} [Field K] [CharZero K] {A:Fin 23→Fin 23→K} {b:Vec K 23}
/-- Exact remaining case for a 23-row order-17 tableau over fields
without a square root of -6. This asserts necessity, not p17 ≥24. -/
theorem only_early (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 17) (field:NoExceptionalRatio K):
    q₂ (mat A) (nodes A) 1=0 ∧ 4≤finrank K (marked A 17 5):=by
  have anc:=no_nonC2 ha ho
  exact ⟨anc,by by_contra! short;exact no_minimal ha ho anc field (by omega)⟩
end RKCert.Paired.Seventeen
