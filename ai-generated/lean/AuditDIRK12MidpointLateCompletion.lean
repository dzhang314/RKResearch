module
import RKCert.ReviewedNative.DIRK12MidpointRealLateCompletion

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DIRK12MidpointForward.Late
open RKResearch.Certified.DIRK12MidpointRealInterval RKResearch.Certified.DirectedRatBox

theorem auditThreeRealLateCoordinates
    (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ) (w : Fin 15 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (early : ∀ i : Fin 15, i.val<10 → (realFeed x f alpha mu nu L).b i*w i=0)
    (pair : w 11=w 13)
    (moments : ∀ k : Fin 3, row (DualSupport12.moment (realFeed x f alpha mu nu L).tableau
      (realFeed x f alpha mu nu L).b (k.val+1)) w=0) :
    w 10=0 ∧ w 11=0 ∧ w 12=0 ∧ w 13=0 :=
  real_late_profile x f alpha mu nu L hx hf w early pair moments

#print axioms auditThreeRealLateCoordinates
#print axioms RKResearch.Certified.DIRK12MidpointForward.Late.real_late_primitive
