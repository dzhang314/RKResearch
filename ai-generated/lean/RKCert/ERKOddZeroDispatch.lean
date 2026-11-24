module
public import RKCert.ERKOddFourPortScalar
public import RKCert.ERKOddZeroFourClose

@[expose] public section
/-! # Exact remaining scalar obligation for the zero linear adjoint case -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.FiniteMidpoint RKCert.Paired.ReverseHull RKCert.Paired.Clock
open Polynomial
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem odd17_zero_gate (gate:∀(P:K[X])(a u:K),OddPencilPorts P a u→False)
    {A:Fin 26→Fin 26→K}{b:Vec K 26}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(zero:backSeed1 A b=0):False:=by
  have S:OddBalanced (s:=25) A b 8:=balanced_odd_ranks ha ho (by decide) (by decide)
  have Z:=balanced_odd_zero_reverse ha ho (by decide) (by decide) S zero
  have k:=odd17_hidden_rank_five ha ho S Z
  obtain ⟨W,θ,P,B⟩:=odd17_zero_five_actual_ports ha ho S Z k
  classical
  by_cases origin:(0:K)∈headSites (nodes A) W
  · obtain ⟨a,u,port⟩:=B.pencil_ports ha origin
    exact gate P a u port
  · exact B.no_origin_clock ha origin

theorem odd17_zero_stage_bound_of_gate (gate:∀(P:K[X])(a u:K),OddPencilPorts P a u→False)
    {s:ℕ}{A:Fin s→Fin s→K}{b:Vec K s}
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(zero:backSeed1 A b=0):27≤s:=by
  by_contra! bad
  have lo:=odd_rank_floor_from_eight (q:=8) ha ho (by decide)
  have exact:s=26:=by omega
  subst s
  exact odd17_zero_gate gate ha ho zero

end RKCert.Paired.ERKOddHidden

