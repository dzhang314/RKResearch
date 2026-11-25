module

import RKCert.ReviewedNative.FiniteBandUnroll

open RKResearch RKResearch.FiniteSeries RKResearch.FiniteSeries.RankUnroll
open scoped Matrix

/- Paid reference agreement uses the actual matrix and terminal readout. -/
example {ι K : Type*} [Fintype ι] [Field K] {M : Matrix ι ι K} {lead D : ℕ}
    (F : Frames M lead D) (w : ι → K) (t : FiniteRootedTree)
    (ht : treeHeight t ≤ D) (ord : (t.order : ℕ) ≤ lead+D) :
    unrollWeights F w ⬝ᵥ Φ t (unrollMatrix F) = w ⬝ᵥ Φ t M :=
  readout_eq_on_band F w t ht ord

/- With the unconditional frame choice, taller output is zero at any order. -/
example {ι K : Type*} [Fintype ι] [Field K] (M : Matrix ι ι K) (lead D : ℕ)
    (w : ι → K) (t : FiniteRootedTree) (high : D < treeHeight t) :
    unrollWeights (chosenFrames M lead D) w ⬝ᵥ Φ t (unrollMatrix (chosenFrames M lead D)) = 0 :=
  readout_zero_of_height (chosenFrames M lead D) w t high

#print axioms RKResearch.FiniteSeries.RankUnroll.readout_eq_on_band
#print axioms RKResearch.FiniteSeries.RankUnroll.readout_zero_of_height
