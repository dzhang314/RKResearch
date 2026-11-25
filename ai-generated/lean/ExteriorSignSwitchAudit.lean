import RKCert.ReviewedNative.ExteriorSignSwitch
import RKCert.ReviewedNative.ReviewedQuadratureUnboundedCensus
import Lean.Elab.Tactic.Omega

open RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.EffectiveDonors RKResearch.Certified.Graded.SignedQuadrature
open RKCert.ReviewedNative.FormalSignedQuadrature
open RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch
open scoped Classical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {p s : ℕ} {A : Matrix (Fin s) (Fin s) K} {w : Fin s → K}
    (ho : HasOrder p A w) :
    let T := activeAggregates (nodes A) w
    let mu := clockMass (nodes A) w
    p ≤ 2*((T \ exteriorSites T).filter (fun x => 0 < mu x)).card+
      exteriorSignSwitchCost T mu := by
  by_cases h : p=0
  · simp [h]
  have pos : 0<p := Nat.pos_of_ne_zero h
  have law := (unit_law ho pos).exterior_sign_switch_budget
  have suc : p-1+1=p := by omega
  simpa only [suc] using law

#check @RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch.switchRoots_card
#check @RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch.switchMask_degree
#check @RKCert.ReviewedNative.FormalSignedQuadrature.UnitLaw.exterior_sign_switch_budget
#print axioms RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch.switchMask_exterior_nonpos
#print axioms RKCert.ReviewedNative.FormalSignedQuadrature.UnitLaw.exterior_sign_switch_budget
