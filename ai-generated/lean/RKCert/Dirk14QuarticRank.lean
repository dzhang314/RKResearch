module
public import RKCert.Dirk14QuarticPhysical
public import RKCert.DirkEvenFifthFloor
public import RKCert.PortNativeGate
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
variable {K:Type*} [Field K] [CharZero K] {A:Fin 18→Fin 18→K} {b:Vec K 18}

/-- The fixed divisor certificate discharges the last option of the original
physical quartic port at p14/s18, including every local and collision case. -/
theorem order14_quartic_hidden (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 14)
    {f:Vec K 18} (hf:f∈zeroSpace A 4) : b*f=0 ∧ tau A b*f=0 := by
  rcases order14_quartic_reduction ha ho hf with pay|⟨Z,Q,u,zm,dz,dv,hu,zu,dq,qn,gs,l₁,l₂⟩
  · exact pay
  · exact False.elim (qn (RKCert.PortRank.lobatto7_marked_factor_quartic_five Z Q u zm dv dz hu zu dq gs l₁ l₂))

/-- Every surviving original p14/s18 chart has exact fourth/fifth ranks
and only two possible forward invariant dimensions. -/
theorem order14_forward_rank_chart (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 14) :
    finrank K (zeroSpace A 4)=2 ∧ finrank K (zeroSpace A 5)=4 ∧
    ∃U:Submodule K (Vec K 18),U≤zeroSpace A 5 ∧ U.map (diag (nodes A))≤U ∧
      (∀W:Submodule K (Vec K 18),W≤zeroSpace A 7 → W.map (diag (nodes A))≤W → W≤U) ∧
      2≤finrank K U ∧ finrank K U≤3 :=
  quartic_rank_dispatch (s:=17) (m:=7) (by decide) ha ho (by decide)
    (fun _ hv=>order14_quartic_hidden ha ho hv)
end RKCert.Paired.Terminal
