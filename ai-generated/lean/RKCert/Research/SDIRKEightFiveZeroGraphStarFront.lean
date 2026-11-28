import Mathlib.Tactic.Ring

namespace RKResearch.Certified.SDIRKEightFiveZeroGraphStarFront

theorem star_baseline_first_zero_cubic {R : Type*} [CommRing R] (x : R) :
    (6*x^2-6*x-x^3)-(12*x-6-3*x^2)=-(x^3-9*x^2+18*x-6) := by ring

end RKResearch.Certified.SDIRKEightFiveZeroGraphStarFront
