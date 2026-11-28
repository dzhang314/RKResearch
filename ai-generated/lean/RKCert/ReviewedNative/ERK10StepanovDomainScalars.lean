/-! Ring identities for the extension degrees and conjugate roots of the
literal Stepanov width-fifteen tableau. The Hensel and faithfully flat
arguments are separate mathematical proofs. -/
namespace RKResearch.ERK10StepanovDomainScalars
open Lean.Grind

variable {R : Type} [CommRing R]

theorem radicand_norm (y : R) (hy : y^2 = 7) :
    (147+42*y)*(147-42*y) = 21^3 := by grind

theorem recovery_factor (y : R) (hy : y^2 = 7) :
    (y-2)*(y+2) = 3 := by grind

theorem conjugate_numerator (x y : R) (hx : x^2 = 3) (hy : y^2 = 7) :
    (21*x*y)^2 = 21^3 := by grind

end RKResearch.ERK10StepanovDomainScalars
#print axioms RKResearch.ERK10StepanovDomainScalars.radicand_norm
#print axioms RKResearch.ERK10StepanovDomainScalars.recovery_factor
#print axioms RKResearch.ERK10StepanovDomainScalars.conjugate_numerator
