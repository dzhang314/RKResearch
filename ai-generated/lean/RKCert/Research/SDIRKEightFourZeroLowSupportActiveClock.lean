import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Scalar receipts for the paid-field four-zero low-support active-clock exclusion.
The stage flags, geometric finite census, and characteristic transfer are separate. -/
namespace RKResearch.Certified.SDIRKEightFourZeroLowSupportActiveClock

theorem consecutive_reverse_supported_reads {R : Type*} [CommRing R]
    {tap earlyR earlyP diffR diffP : R}
    (hr : diffR = tap * earlyR) (hp : diffP = tap * earlyP) :
    earlyR * diffP - earlyP * diffR = 0 := by
  rw [hr, hp]
  ring

theorem actual_fifth_clock_cross {R : Type*} [CommRing R]
    {tap x₄ gDelta D N : R}
    (hD : tap * gDelta = D) (hN : tap * x₄ * gDelta = N) :
    x₄ * D = N := by
  rw [← hD, ← hN]
  ring

def reverseGate3 {R : Type*} [CommRing R] (v t : R) : R :=
  (2*v^2-4*v-1)*t^3 + (-18*v^2+30*v+9)*t^2 +
    (48*v^2-60*v-21)*t - 24*v^2+24*v+9

theorem zero_third_cubic_gate {R : Type*} [CommRing R] (v : R) :
    reverseGate3 v (1+2*v) =
      2*(2*v^2-4*v-1)*(4*v^3-12*v^2+3*v+2) := by
  unfold reverseGate3
  ring

theorem literal_projection_products :
    (47553061737266675712 : Nat) = 2^34*3^7*1265639 ∧
    (1792251967911949825877867417632473164185337856 : Nat) =
      2^80*3^14*1174307*263949107 ∧
    (78815638671875 : Nat) = 5^9*7^9 ∧
    (10115550406874288451305478598026275634765625 : Nat) = 5^18*7^36 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFourZeroLowSupportActiveClock
