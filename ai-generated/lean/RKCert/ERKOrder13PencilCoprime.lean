module
public import RKCert.ERKOrder13PencilStepA4
public import RKCert.ERKOrder13PencilStepB5

@[expose] public section
namespace RKCert.Paired.FiniteMidpoint.Pencil13
open RKCert.DenseCommonRoot

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option maxSynthPendingDepth 10000

open RKCert.GoodPrimeDense
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
variable {K:Type*} [Field K] [CharZero K]
private def bez1B3Extra : List ℤ := [-2,-2,-2,-6,-8,-8,4,-8,8,0,7,2,-7,6,-8,-3,5,7,1,5,-2,7]
private def bez2B3Extra : List ℤ := [-4,1,-7,5,-7,7,-8,-8,-1,-6,1,1,0,5,6,-1,-5,6,2,-4,1,-4,7,-6,-2,1,2,4,0,4,5,8,7,5,-1,-4,7,-3,-6,-7]
private theorem checkedB3Extra : modCheck (p:=17) A4Rest B3Extra bez1B3Extra bez2B3Extra := by
  decide +kernel

private theorem commonB3Extra (u:K) (r0:GoodPrimeDense.read (Int.castRingHom K) u A4Rest=0) :
    GoodPrimeDense.read (Int.castRingHom K) u B3Extra≠0 := by
  have h:=no_common_read (p:=17) A4Rest B3Extra bez1B3Extra bez2B3Extra 40 22
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide) checkedB3Extra u
  exact h.resolve_left (not_not_intro r0)

private def bez1B4Extra : List ℤ := [-3,-5,-7,1,-4,6,-8,-1,1,0,-7,7,-6,-5,-1,8,-8,5,4,7,-5,5,5,-8,3,-7,1,0,-3,-6,0,0,4,-1,-4,4,-4,5,-1,0,0,-4,-8,-1]
private def bez2B4Extra : List ℤ := [8,0,4,5,7,4,-7,4,-1,-6,4,7,0,4,-7,8,1,6,4,0,-5,-4,-7,-1,1,-4,3,2,-3,-2,2,7,0,6,-2,2,1,3,-1,2]
private theorem checkedB4Extra : modCheck (p:=17) A4Rest B4Extra bez1B4Extra bez2B4Extra := by
  decide +kernel

private theorem commonB4Extra (u:K) (r0:GoodPrimeDense.read (Int.castRingHom K) u A4Rest=0) :
    GoodPrimeDense.read (Int.castRingHom K) u B4Extra≠0 := by
  have h:=no_common_read (p:=17) A4Rest B4Extra bez1B4Extra bez2B4Extra 40 44
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide) checkedB4Extra u
  exact h.resolve_left (not_not_intro r0)

private def bez1B5Rest : List ℤ := [-3,-3,8,8,2,-2,-6,-4,-5,-7,1,6,7,8,-3,-2,5,0,8,-8,-7,-2,-8,7,-6,-2,-4,7,-7,-3,-2,2,-4,0,1,-8,-2,-8,5,-5,-8,8,2,-5,-1,-8,0,0,3,-7,-6,-3,-8,2,4,2,8,0,6,6,-5,2,-3,8,8,-3,-6,4,-5,1,-7,5,6,5,-5,1,-1,3,-1,-1,3,-8,1,6,-1,2,1,-6,-2,3,-1,1,-3,2,-6,-4,-3,-4,3,-8,-4,3,6,-5,0,-6,8,-7,-3,2,-3,-6,4,2,3,-6,-4,-4,4,1,-8]
private def bez2B5Rest : List ℤ := [5,0,3,-6,-6,-5,2,4,-4,-6,4,-5,-8,6,-1,-4,2,3,-3,-6,-8,7,0,8,-2,8,-1,1,-1,-2,-2,-5,-3,0,0,-2,-7,-7,-5,-6]
private theorem checkedB5Rest : modCheck (p:=17) A4Rest B5Rest bez1B5Rest bez2B5Rest := by
  decide +kernel

private theorem commonB5Rest (u:K) (r0:GoodPrimeDense.read (Int.castRingHom K) u A4Rest=0) :
    GoodPrimeDense.read (Int.castRingHom K) u B5Rest≠0 := by
  have h:=no_common_read (p:=17) A4Rest B5Rest bez1B5Rest bez2B5Rest 40 121
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide) checkedB5Rest u
  exact h.resolve_left (not_not_intro r0)

theorem no_common_tape (u v:K) (un:u≠0) (an:GoodPrimeDense.read (Int.castRingHom K) u anchor≠0)
    (om:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v omitted=0)
    (m₀:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v firstMoment=0)
    (m₁:GoodPrimeDense.read (GoodPrimeDense.read (Int.castRingHom K) u) v crossMoment=0) : False := by
  have eA1 := propagateA1 u v un an om m₀
  have eA2 := propagateA2 u v un an m₀ eA1
  have eA3 := propagateA3 u v un an eA1 eA2
  have eA4 := propagateA4 u v un an eA2 eA3
  have a0 : GoodPrimeDense.read (Int.castRingHom K) u A4Rest=0 := by
    simpa only [A4,GoodPrimeDense.read,mul_zero,add_zero] using eA4
  have eB1 := propagateB1 u v un an m₁ om
  have eB2 := propagateB2 u v un an om eB1
  have eB3 := propagateB3 u v un an eB1 eB2 (commonB3Extra u a0)
  have eB4 := propagateB4 u v un an eB2 eB3 (commonB4Extra u a0)
  have eB5 := propagateB5 u v un an eB3 eB4
  apply commonB5Rest u a0
  simpa only [B5,GoodPrimeDense.read,mul_zero,add_zero] using eB5

end RKCert.Paired.FiniteMidpoint.Pencil13
