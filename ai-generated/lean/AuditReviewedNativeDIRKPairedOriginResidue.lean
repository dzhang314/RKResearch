import RKCert.ReviewedNative.DIRKPairedOriginResidue

/-! Typed audit of the raw two-polynomial and physical-row boundary only. -/
open Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.PairedOrigin
open scoped Classical Matrix

section
variable {K : Type*} [Field K]

example (γ : K) (P : K[X]) :
    receiptPoly γ (X * P) = X * receiptPoly γ P - C γ * P :=
  receiptPoly_X_mul γ P

example (γ x : K) (hγ : γ ≠ 0) :
    let G : K[X] := X * (X - C γ)^2
    let H : K[X] := X * G
    ((G - C γ * G.derivative).eval x = 0 ∧
      (H - C γ * H.derivative).eval x = 0) ↔ x = γ := by
  simpa only [receiptPoly, nextPrimitive, originPrimitive] using pair_receipt_zero_iff γ x hγ

example {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (γ : K)
    (upper : ∀ i, (0 : Fin (n+1)) < i → A 0 i = 0) (diagonal : A 0 0 = γ) :
    stageResidual A (originPrimitive γ) 0 = 0 ∧ stageResidual A (nextPrimitive γ) 0 = 0 :=
  paired_actual_origin_clean A upper diagonal

example {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {k : Fin s} {γ : K}
    (hγ : γ ≠ 0) (upper : ∀ i, k < i → A k i = 0) (diagonal : A k k = γ)
    (cleanG : stageResidual A (originPrimitive γ) k = 0)
    (cleanH : stageResidual A (nextPrimitive γ) k = 0)
    (nonorigin : nodes A k ≠ γ)
    (earlier : ∀ i, i < k → stageResidual A (originPrimitive γ) i = 0 →
      stageResidual A (nextPrimitive γ) i = 0 → nodes A i = γ) :
    let S := (Finset.Iio k).filter (fun i =>
      ¬ (stageResidual A (originPrimitive γ) i = 0 ∧ stageResidual A (nextPrimitive γ) i = 0))
    (∑ i ∈ S, A k i * (originPrimitive γ).derivative.eval (nodes A i)) ≠ 0 ∨
      (∑ i ∈ S, A k i * (nextPrimitive γ).derivative.eval (nodes A i)) ≠ 0 := by
  simpa only [earlierJointOffRows] using
    paired_offReceipt_ne_of_first_nonorigin hγ upper diagonal cleanG cleanH nonorigin earlier

end

#print axioms RKResearch.Certified.Graded.PairedOrigin.receiptPoly_X_mul
#print axioms RKResearch.Certified.Graded.PairedOrigin.pair_receipt_zero_iff
#print axioms RKResearch.Certified.Graded.PairedOrigin.paired_actual_origin_clean
#print axioms RKResearch.Certified.Graded.PairedOrigin.paired_offReceipt_ne_of_first_nonorigin
