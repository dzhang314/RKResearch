module

public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace RKResearch.Certified.ERK10MirrorScheduleMod19

def center (a b : ZMod 19) : ZMod 19 :=
  45*a^2+16*a*b-13*b^2

def side (a b : ZMod 19) : ZMod 19 :=
  64*a^5+372*a^4*b-65*a^3*b^2-187*a^2*b^3-21*a*b^4+13*b^5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem center_projective :
    ∀ a b : ZMod 19, (a≠0 ∨ b≠0) → center a b≠0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem side_projective :
    ∀ a b : ZMod 19, (a≠0 ∨ b≠0) → side a b≠0 := by decide +kernel

end RKResearch.Certified.ERK10MirrorScheduleMod19

#print axioms RKResearch.Certified.ERK10MirrorScheduleMod19.center_projective
#print axioms RKResearch.Certified.ERK10MirrorScheduleMod19.side_projective
