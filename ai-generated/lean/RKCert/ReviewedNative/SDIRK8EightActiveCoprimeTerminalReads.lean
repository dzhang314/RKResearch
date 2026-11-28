module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveCoprimeTerminalReads

/-- At the actual marked fifth tap, both residuals have the same
coefficient. Their cleared cross is valid whether or not the
marked clock repeats a physically silent predecessor. -/
theorem markedSixthRead {R : Type*} [CommRing R]
    (α a f h p q n v d : R)
    (hv : v=α*a*f) (hd : d=α*a*(h-p)) (hq : q*h=n) :
    q*f*d+v*(q*p-n)=0 := by
  linear_combination (q*p-n)*hv+q*f*hd+α*a*f*hq

/-- With the actual affine reverse multiplier zero at the terminal,
the arithmetic rear relation is polynomial and does not invert a
cleared arithmetic factor. -/
theorem terminalGaussArithmetic {R : Type*} [CommRing R]
    (m scale k k₈ H J h₉ h₈ : R)
    (h₉read : h₉=scale*k*m) (h₈read : h₈=2*scale*k₈*m)
    (hk : H*k₈= -k*J) :
    H*h₈+2*J*h₉=0 := by
  linear_combination 2*J*h₉read+H*h₈read+2*scale*m*hk

#print axioms markedSixthRead
#print axioms terminalGaussArithmetic

end RKCert.ReviewedNative.SDIRK8EightActiveCoprimeTerminalReads
