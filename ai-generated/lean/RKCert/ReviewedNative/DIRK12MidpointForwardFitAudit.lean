module

import RKCert.ReviewedNative.DIRK12MidpointForwardActualNodal

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointReverse
open RKResearch.Certified.DIRK12MidpointForward RKResearch.Certified.DIRK12MidpointRealInterval
open RKResearch.Certified.DirectedRatBox RKResearch.Certified.DIRK12MidpointProbes
open RKResearch.Certified.DIRK12MidpointShape

open scoped Matrix Polynomial

section
variable (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
  (hx0 : realX x=0) (hf0 : realF x f=0)

local notation "Areal" => (Feed.tableau (Actual.assembled x f))
local notation "Breal" => (Feed.b (Actual.assembled x f))

example (m : Nat) (hm : m < 5) :
    DualSupport12.forward Areal m ∈ forwardBand ℝ (m+1) :=
  Actual.assembled_fw_primitive x f hx hf hx0 hf0 m hm

example (i : Fin 15) (hi : ¬ghostRow i) (ht : i≠terminal) :
    DualSupport12.forward Areal 5 i=Actual.quinticScale x*actualProfile Areal 1 i :=
  Actual.actual_quintic_profile x f hx hf hx0 hf0 i hi ht

example : row Breal (DualSupport12.forward Areal 5)=0 :=
  Actual.actual_quintic_output x f hx hf hx0 hf0

example (i : Fin 15) (hi : ¬ghostRow i) (ht : i≠terminal) :
    mat Areal (Actual.nodalInput x f) i=
      Vector.evalVector (1-nodes Areal) (Actual.nodalImage x f) i :=
  Actual.actual_nodal_image x f hx hf hx0 hf0 i hi ht

example :
    row (DualSupport12.moment Areal Breal 4) (mat Areal (Actual.nodalInput x f))=
      row (DualSupport12.moment Areal Breal 4)
        (Vector.evalVector (1-nodes Areal) (fromOne (openingNodal x f))) :=
  Actual.actual_nodal_fourth_read x f hx hf hx0 hf0

end

#print axioms Actual.assembled_fw_primitive
#print axioms Actual.actual_quintic_profile
#print axioms Actual.actual_quintic_bridge
#print axioms Actual.actual_nodal_image
#print axioms Actual.actual_nodal_fourth_read
