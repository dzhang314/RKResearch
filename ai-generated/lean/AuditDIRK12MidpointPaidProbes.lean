module
import RKCert.ReviewedNative.DIRK12MidpointPaidNodalProbes

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointShape
open RKResearch.Certified.DIRK12MidpointProbes RKResearch.Certified.DIRK12MidpointRealInterval
open RKResearch.Certified.DirectedRatBox

theorem auditNodalPaidProbes (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ghostRow i → 1-nodes A i=site x f (stageTag i)) :
    ∀ k : Fin 3, row (DualSupport12.moment A (physicalWeight x f) (k.val+1))
      (fun i => (nodalTarget x f).eval (1-nodes A i))=0 :=
  actual_nodal_probe hx hf hx0 hf0 A clocks

theorem auditRealMixedTapProbes (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ghostRow i → 1-nodes A i=site x f (stageTag i))
    (a : Fin 3 → ℝ) (j : Fin 4) :
    row (DualSupport12.moment A (physicalWeight x f) (j.val+1))
      (∑ d : Fin 3, a d • actualProfile A d)=0 :=
  probe_combo_positive A _ (scalar_and_star_with_physical_weights hx hf hx0 hf0 A clocks).1 a j

#print axioms auditNodalPaidProbes
#print axioms auditRealMixedTapProbes
