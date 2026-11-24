import RKCert.ReviewedNative.GradedGrowth
import RKCert.ReviewedNative.GradedPrefix
import RKCert.ReviewedNative.GradedProducts
import RKCert.ReviewedNative.GradedPrimitives

open RKResearch RKResearch.Certified.Graded
open scoped Matrix

section
variable {K : Type*} [Field K] {s q p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
variable (strict : ∀ i j, i ≤ j → A i j = 0)

example (ho : HasOrder A b p) (paid : q+1 ≤ p) (mid : 2*q ≤ p) :
    Module.finrank K (treeSpace A q)=q+1+Module.finrank K (zeroSpace A q) :=
  explicit_midpoint_rank_eq strict ho paid mid

example (ho : HasOrder A b p) (paid : q+2 ≤ p) :
    q ≤ Module.finrank K (zeroSpace A (q+1)) := zeroSpace_finrank strict ho paid

example (i : Fin (s+1)) (nz : (A *ᵥ 1) i ≠ 0)
    (clean : ∀ v ∈ zeroSpace A q, v i = 0) :
    HasOrder (((A *ᵥ 1) i)⁻¹ • A.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le))
      (fun j : Fin i.val => ((A *ᵥ 1) i)⁻¹ * A i (Fin.castLE i.isLt.le j)) q :=
  exact_receiver_prefix_order strict i q nz clean

example [CharZero K] {P:Polynomial K} (hp:P.natDegree≤q) :
    mat A (evalNodes A P)-evalNodes A (primitive P)∈zeroSpace A (q+1) :=
  primitive_defect A P hp
end
