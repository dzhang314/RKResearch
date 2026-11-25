module

import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData

open RKResearch.Certified
open scoped Matrix

namespace RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper

example (v : Fin 27 → ℤ) : actInt v = AInt *ᵥ v := actInt_eq v
example (v : Fin 27 → ℤ) : outInt v = bInt ⬝ᵥ v := outInt_eq v
example : A.IsLowerTriangular := lowerTriangular
example (i : Fin 27) : A i i = 1/9 := common_diagonal i
example : stageScale = coreMultiplier * RationalStrictSDIRKQ5CompressedCore.physicalScale :=
  shared_scale

#print axioms RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper.actInt_eq
#print axioms RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper.outInt_eq
#print axioms RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper.shared_scale

end RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper
