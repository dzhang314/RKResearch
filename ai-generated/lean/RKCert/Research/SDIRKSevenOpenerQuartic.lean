module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Finite polar receipt for the canonical SDIRK7 opener quartic

Geometric smoothness and the canonical specialization argument are
separate; this module checks the exact finite arithmetic obstruction. -/

namespace RKResearch.Certified.SDIRKSevenOpenerQuartic

abbrev P := Fin 5 × Fin 5 × Fin 5
def coords (p : P) : ZMod 5 × ZMod 5 × ZMod 5 :=
  (p.1.val,p.2.1.val,p.2.2.val)

def quartic (p : P) : ZMod 5 :=
  let (a,b,c) := coords p
  6*a^3*b-6*a^3*c+12*a^2*b^2-36*a^2*b*c+18*a^2*c^2+
    6*a*b^3-21*a*b^2*c+27*a*b*c^2-9*a*c^3-
    2*b^3*c+5*b^2*c^2-4*b*c^3+c^4

def polar (v p : P) : ZMod 5 :=
  let (a,b,c) := coords p
  let (x,y,z) := coords v
  x*(18*a^2*b-18*a^2*c+24*a*b^2-72*a*b*c+36*a*c^2+
    6*b^3-21*b^2*c+27*b*c^2-9*c^3)+
  y*(6*a^3+24*a^2*b-36*a^2*c+18*a*b^2-42*a*b*c+27*a*c^2-
    6*b^2*c+10*b*c^2-4*c^3)+
  z*(-6*a^3-36*a^2*b+36*a^2*c-21*a*b^2+54*a*b*c-27*a*c^2-
    2*b^3+10*b^2*c-12*b*c^2+4*c^3)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 16000 in
/-- Every rational residue center off the quartic violates the
required vanishing of its polar on the uniquely determined axis. -/
theorem no_polar_center : ∀ p : P, quartic p≠0 →
    ∃ v : P, polar v p=0 ∧ polar p v≠0 := by
  decide +kernel

end RKResearch.Certified.SDIRKSevenOpenerQuartic
