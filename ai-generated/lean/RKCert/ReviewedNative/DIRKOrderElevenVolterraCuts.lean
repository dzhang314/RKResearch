module

public import RKCert.ReviewedNative.DIRKSeedReduction
public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.RowAnnihilator
import Mathlib.Tactic.Ring

@[expose] public section

/-! Paid forward and backward grade-four Volterra cuts for actual order
eleven. These are the structural inputs of the five-dirty-side argument;
the finite polynomial elimination is separate. -/
namespace RKResearch.Certified.Graded.OrderElevenVolterra

open RKResearch Module Reverse
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Paid first-support cutoff; neither the nonzero pivot nor nonzero
diagonal are assumed in this form. -/
theorem forward_cut (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    {u : Fin s → K} (hu : u∈treeSpace A 4) {i : Fin s} (pre : ∀ j < i, u j=0) :
    volterra A u∈zeroSpace A 6 ∧
      (∀ j < i, volterra A u j=0) ∧ volterra A u i=-(A i i)^2*u i := by
  refine ⟨volterra_treeSpace ho 4 (by decide) hu,?_,volterra_pivot ha i u pre⟩
  intro j hj
  rw [volterra_pivot ha j u (fun k hk => pre k (hk.trans hj)),pre j hj,mul_zero]

/-- Physical row version: complement the clock and transpose the actual
matrix, without division by any ordinary output weight. -/
def reverseComm (A : Matrix (Fin s) (Fin s) K) : (Fin s → K) →ₗ[K] (Fin s → K) :=
  (diag (reflectedClock A)).comp (mat A.transpose)
    - (mat A.transpose).comp (diag (reflectedClock A))
    - (mat A.transpose).comp (mat A.transpose)

theorem transpose_identity (w u : Fin s → K) :
    row (reverseComm A w) u = row w (volterra A u) := by
  have hy (v : Fin s → K) : diag (reflectedClock A) v = v-diag (nodes A) v := by
    ext i
    simp only [diag_apply,Pi.sub_apply,Pi.one_apply]
    ring
  simp only [reverseComm,volterra,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,
    row_diag,row_mat_transpose,hy]
  ring

theorem backward_pivot (ha : A.IsLowerTriangular) (i : Fin s)
    (v : Fin s → K) (after : ∀ j, i < j → v j=0) :
    reverseComm A v i=-(A i i)^2*v i := by
  have hz (j : Fin s) (hij : i < j) : mat A.transpose v j = 0 := by
    rw [transpose_mat_pivot ha j v (fun l hl => after l (hij.trans hl)),after j hij,mul_zero]
  have hp (j : Fin s) (hij : i < j) : diag (reflectedClock A) v j = 0 := by
    rw [diag_apply,after j hij,mul_zero]
  simp only [reverseComm,LinearMap.sub_apply,LinearMap.comp_apply,Pi.sub_apply]
  rw [diag_apply,transpose_mat_pivot ha i v after,
    transpose_mat_pivot ha i _ hp,transpose_mat_pivot ha i _ hz,
    transpose_mat_pivot ha i v after,diag_apply]
  ring

/-- The genuine reflected commutator applied to one order-four weighted
input annihilates the order-four tree column space. -/
theorem backward_paid (ho : HasOrder 11 A b)
    {z : Fin s → K} (hz : z∈treeSpace A 4) :
    reverseComm A (diag b z)∈annih (treeSpace A 4) := by
  apply mem_annih.mpr
  intro u hu
  rw [transpose_identity]
  have R := volterra_treeSpace ho 4 (by decide) hu
  have B := zeroSpace_mul_treeSpace ho (by decide) R hz
  have M : probe A b 0 (volterra A u * z) = 0 :=
    probe_zeroSpace ho (k:=0) (by decide) B
  have Ms : (∑ i, b i * (volterra A u i * z i))=0 := by
    simpa only [probe,row_apply,dotProduct,Pi.mul_apply,pow_zero,mul_one] using M
  simp only [row_apply,dotProduct,diag_apply]
  rw [←Ms]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A true zero terminal column also debits the reverse commutator. -/
theorem backward_terminal_zero (t : Fin s) (hc : ∀ i, A i t=0) (w : Fin s → K) :
    reverseComm A w t=0 := by
  have z (v : Fin s → K) : mat A.transpose v t=0 := by
    simp only [mat_apply,Matrix.mulVec_apply_eq_sum,Matrix.transpose_apply,hc,zero_mul,
      Finset.sum_const_zero]
  simp only [reverseComm,LinearMap.sub_apply,LinearMap.comp_apply,Pi.sub_apply,diag_apply,
    z,mul_zero,sub_zero]

end RKResearch.Certified.Graded.OrderElevenVolterra
