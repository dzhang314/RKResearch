import RKCert.ReviewedNative.CausalDefectPrefix

/-! Standalone typed audit of the measured generic core; no band client. -/
open Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.DefectPrefix
open scoped Classical Matrix

section
variable {K : Type*} [Field K] {s d n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {k : Fin s}

example (ha : ∀ i j, i ≤ j → A i j = 0)
    (paid : ∀ P : K[X], P.natDegree ≤ d →
      mat A (fun i => g A i * P.eval (nodes A i)) k = 0)
    (coh : ∀ {i l : Fin s}, i ∈ earlierOffRows A k → l ∈ earlierOffRows A k →
      nodes A i = nodes A l → g A i = g A l)
    (receipt : (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0) :
    d + 2 ≤ (activeOffKnots A k).card ∧ Nonempty (TriangularPrefix A k (d + 2)) := by
  refine paid_prefix_pivots ha ?_ coh receipt
  intro P hp
  have eq : defectColumn A P = (fun i => g A i * P.eval (nodes A i)) := by
    funext i
    simp only [defectColumn, diag_apply, evalNodes_apply]
  rw [eq]
  exact paid P hp

example (W : TriangularPrefix A k n) :
    StrictMono W.pivot ∧ (∀ u, W.pivot u < k) ∧
      (∀ u i, i < W.pivot u → g A i * (W.polynomial u).eval (nodes A i) = 0) ∧
      (∀ u, g A (W.pivot u) * (W.polynomial u).eval (nodes A (W.pivot u)) ≠ 0) ∧
      LinearIndependent K (fun u => prefixRestrict k.isLt.le
        (fun i => g A i * (W.polynomial u).eval (nodes A i))) := by
  have eq (u : Fin n) :
      defectColumn A (W.polynomial u) = (fun i => g A i * (W.polynomial u).eval (nodes A i)) := by
    funext i
    simp only [defectColumn, diag_apply, evalNodes_apply]
  refine ⟨W.ordered, W.before, ?_, ?_, ?_⟩
  · intro u i hi
    simpa only [eq] using W.earlierZero u i hi
  · intro u
    simpa only [eq] using W.atPivot u
  · simpa only [eq] using W.independent
end

#print axioms RKResearch.Certified.Graded.DefectPrefix.paid_prefix_pivots
