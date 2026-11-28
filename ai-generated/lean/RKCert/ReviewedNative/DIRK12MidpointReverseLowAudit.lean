module

import RKCert.ReviewedNative.DIRK12MidpointReverseActualLow

open RKResearch.Certified.Graded
open RKResearch.Certified.DIRK12MidpointReverse
open RKResearch.Certified.DIRK12MidpointRealInterval
open RKResearch.Certified.DirectedRatBox

open scoped Matrix

section
variable (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
  (hx0 : realX x=0) (hf0 : realF x f=0)

local notation "Areal" => (RKResearch.Certified.DIRK12MidpointForward.Feed.tableau (Actual.assembled x f))
local notation "Breal" => (RKResearch.Certified.DIRK12MidpointForward.Feed.b (Actual.assembled x f))

example : DualSupport12.reverse Areal Breal 0=0 :=
  Actual.reverse_grade1 x f hx hf hx0 hf0

example : DualSupport12.reverse Areal Breal 1=0 :=
  Actual.reverse_grade2 x f hx hf hx0 hf0

example : DualSupport12.reverse Areal Breal 2=(3:ℝ) • Actual.profileG x f :=
  Actual.reverse_grade3 x f hx hf hx0 hf0

example : DualSupport12.reverse Areal Breal 3=(4:ℝ) •
      ((3*Actual.d x f/2) • Actual.profileG x f+
        Seed.lambda (Actual.r x f) • Actual.profileH x f) :=
  Actual.reverse_grade4 x f hx hf hx0 hf0

example (j : Fin 3) (m : Nat) (hm : m≤7) :
    row (DualSupport12.reverse Areal Breal (j.val+1)) ((nodes Areal)^m)=0 :=
  Actual.reverse_low_silent x f hx hf hx0 hf0 j m hm

end

#print axioms Actual.real_reverse_ghost_read
#print axioms Actual.installed_is_five
#print axioms Actual.reverse_grade1
#print axioms Actual.reverse_grade2
#print axioms Actual.reverse_grade3
#print axioms Actual.reverse_grade4
#print axioms Actual.reverse_low_silent
