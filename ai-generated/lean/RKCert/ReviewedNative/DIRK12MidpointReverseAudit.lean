module

import RKCert.ReviewedNative.DIRK12MidpointReverseProfile
import RKCert.ReviewedNative.DIRK12MidpointReversePhysicalLow

open RKResearch.Certified.Graded
open RKResearch.Certified.DIRK12MidpointReverse
open RKResearch.Certified.DIRK12MidpointRealInterval
open RKResearch.Certified.DirectedRatBox

open scoped Matrix

example (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Actual.profileH x f=Actual.baryVector x f :=
  Actual.actual_H_eq x f hx hf

example (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) (m : Nat) (hm : m≤7) :
    row (Actual.profileH x f) ((nodes (Actual.assembled x f).tableau)^m)=0 :=
  Actual.actual_H_silent x f hx hf m hm

example (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    mat (Actual.assembled x f).tableau.transpose (Actual.profileG x f)=
      (Actual.d x f/2) • Actual.profileG x f+Actual.profileH x f :=
  Actual.actual_pair_identity x f hx hf

example (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) (m : Nat) (hm : m≤7) :
    DualSupport12.forward (Actual.assembled x f).tableau m 11=
      DualSupport12.forward (Actual.assembled x f).tableau m 13 :=
  Actual.actual_pair_forward x f hx hf m hm

#print axioms Physical.physical_read
#print axioms Physical.error_visible
#print axioms Actual.mass_d
#print axioms Actual.mass_v
#print axioms Actual.mass_u
#print axioms Actual.actual_H_eq
#print axioms Actual.actual_pair_forward
