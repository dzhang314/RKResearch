module

import RKCert.ReviewedNative.ERK8FourOffCleanPrimitive

open RKResearch Polynomial
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape

example {K : Type*} [Field K] [CharZero K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ j l, j≤l → A j l=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=ERKTaggedHorizon.band A 2)
    (nOff : (OneOff.offKnots A).card=4)
    {iH iX : Fin 10} {z : K} (L : CleanPrimitivePlacement A b iH iX z)
    {P R : K[X]} (hd : P.natDegree≤2) (hnz : P≠0)
    (fit : ∀ j, OneOff.g A j≠0 → P.eval (nodes A j)=OneOff.g A j)
    (term : CleanTerminalProfile A (quartic (nodes A iH) (nodes A iX) z) R) :
    ∃ theta k, NormalizedShape P (nodes A iH) (nodes A iX) z theta k :=
  clean_shape_from_actual_prefix ha ho hF nOff L hd hnz fit term

#print axioms RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape.coefficients_of_clean_tap
#print axioms RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape.shared_clean_primitive
#print axioms RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape.clean_shape_from_actual_prefix
