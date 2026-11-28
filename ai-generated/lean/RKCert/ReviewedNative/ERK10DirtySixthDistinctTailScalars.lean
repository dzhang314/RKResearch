module

public import RKCert.ReviewedNative.ERK10DirtySixthRelay
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

public section

namespace RKResearch.Certified.ERK10DirtySixthDistinctTailScalars

open RKResearch FiniteRootedTree ERK10DirtySixthRelay
open scoped Matrix FiniteRootedTree

def source0 : FiniteRootedTree := bushyTree 6
def source1 : FiniteRootedTree := bushyTree 2 ◂ bushyTree 4
def source2 : FiniteRootedTree := .leaf ◂ bushyTree 5

/-- X, X², X³ coefficients of the three actual size-six sources,
before dividing by the common decoder and stage scaling. -/
def num (t : FiniteRootedTree) (j : Fin 5) : ℤ :=
  -(PInt j ⬝ᵥ replayStage (fun v => AInt *ᵥ v) t)

def minor (f g h : Fin 5 → ℤ) : ℤ :=
  f 1*(g 2*h 3-g 3*h 2)-f 2*(g 1*h 3-g 3*h 1)+f 3*(g 1*h 2-g 2*h 1)

set_option maxHeartbeats 12000000 in
theorem nonzero_source_minor :
    1728 * minor (num source0) (num source1) (num source2) =
      11 * (756*(1224720 : ℤ)^5)^3 := by
  decide +kernel

theorem latest_live_scalar (c b u : ℚ)
    (h1 : u=(1-c)*b) (h2 : u=(1-c^2)*b/2) :
    (1-c)^2*b=0 := by
  linear_combination -(2 : ℚ)*h1+2*h2

end RKResearch.Certified.ERK10DirtySixthDistinctTailScalars

#print axioms RKResearch.Certified.ERK10DirtySixthDistinctTailScalars.nonzero_source_minor
#print axioms RKResearch.Certified.ERK10DirtySixthDistinctTailScalars.latest_live_scalar
