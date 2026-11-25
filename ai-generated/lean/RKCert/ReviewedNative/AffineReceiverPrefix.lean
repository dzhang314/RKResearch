module

public import RKCert.ReviewedNative.GradedPrefix
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A normalized affine probe earns actual prefix order

Every row and every coefficient is indexed by the original tableau.
No paid endpoint, midpoint rank, or coefficient-field order is needed.
-/
namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped BigOperators Matrix FiniteRootedTree
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {l : Fin s→K}
variable {x : K} {cut : Fin s}

/-- A signed affine combination of original rows at one clock, with all
active indices at or before the displayed original cut. -/
structure ClockAffineProbe (A : Matrix (Fin s) (Fin s) K)
    (l : Fin s→K) (x : K) (cut : Fin s) : Prop where
  afterCut : ∀ i, cut<i → l i=0
  atClock : ∀ i, l i≠0 → nodes A i=x
  mass : (∑ i,l i)=1

/-- The literal combined row of the original A, before any scaling. -/
def affineReceiverRow (A : Matrix (Fin s) (Fin s) K) (l : Fin s→K) : Fin s→K :=
  fun j=>∑ i,l i*A i j

theorem affineReceiverRow_pairing (A : Matrix (Fin s) (Fin s) K)
    (l z : Fin s→K) :
    affineReceiverRow A l ⬝ᵥ z=l ⬝ᵥ (A *ᵥ z) := by
  simp only [affineReceiverRow,dotProduct,Matrix.mulVec,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem ClockAffineProbe.row_tail (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (j : Fin s) (past : cut.val≤j.val) :
    affineReceiverRow A l j=0 := by
  have cj : cut≤j := past
  unfold affineReceiverRow
  apply Finset.sum_eq_zero
  intro i _
  by_cases later : cut<i
  · rw [P.afterCut i later,zero_mul]
  · rw [strict i j ((le_of_not_gt later).trans cj),mul_zero]

theorem ClockAffineProbe.power_pairing (P : ClockAffineProbe A l x cut) (n : ℕ) :
    row l (fun i=>(nodes A i)^n)=x^n := by
  classical
  rw [row_apply,dotProduct]
  calc
    _ = ∑ i : Fin s,l i*x^n := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases live : l i≠0
      · rw [P.atClock i live]
      · have z : l i=0 := not_not.mp live
        simp only [z,zero_mul]
    _ = _ := by rw [←Finset.sum_mul,P.mass,one_mul]

/-- A common clock makes the actual signed row a left eigenprobe for C. -/
theorem ClockAffineProbe.diag_pairing (P : ClockAffineProbe A l x cut) (v : Fin s→K) :
    row l (diag (nodes A) v)=x*row l v := by
  classical
  simp only [row_apply,dotProduct,diag_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases live : l i≠0
  · rw [P.atClock i live]
    ring
  · have z : l i=0 := not_not.mp live
    simp only [z,zero_mul,mul_zero]

/-- The original prefix before the latest possible probe row has the
full native order q after the literal clock normalization. -/
theorem ClockAffineProbe.prefix_hasOrder
    (P : ClockAffineProbe A l x cut)
    (strict : ∀ i j,i≤j→A i j=0) (nz : x≠0) (q : ℕ)
    (paid : ∀ v∈zeroSpace A q, row l v=0) :
    HasOrder q (x⁻¹ • prefixMatrix A cut.isLt.le)
      (fun j : Fin cut.val=>x⁻¹*affineReceiverRow A l (Fin.castLE cut.isLt.le j)) := by
  intro T hT
  let r := x⁻¹
  let B := prefixMatrix A cut.isLt.le
  let b₀ : Fin cut.val→K := fun j=>r*affineReceiverRow A l (Fin.castLE cut.isLt.le j)
  have hz := paid _ (zeroSpace_mono A hT (rootStageResidual_mem A T))
  change row l ((T.factorial:K) • (A *ᵥ Φ T A) -
      (fun i=>(nodes A i)^(T.order:ℕ)))=0 at hz
  rw [map_sub,map_smul,smul_eq_mul,P.power_pairing,sub_eq_zero] at hz
  have z : (T.factorial:K)*(affineReceiverRow A l ⬝ᵥ Φ T A)=x^(T.order:ℕ) := by
    simpa only [row_apply,affineReceiverRow_pairing] using hz
  have scal : r*r^((T.order:ℕ)-1)=r^(T.order:ℕ) := by
    rw [←pow_succ']
    congr 1
    have hp := T.order.pos
    omega
  have mass : b₀ ⬝ᵥ Φ T (r•B)=r^(T.order:ℕ)*(affineReceiverRow A l ⬝ᵥ Φ T A) := by
    unfold B
    rw [Φ_smul,Φ_prefix strict cut.isLt.le,dotProduct]
    simp only [b₀,Pi.smul_apply,smul_eq_mul,prefixRestrict_apply]
    have term (j : Fin cut.val) :
        r*affineReceiverRow A l (Fin.castLE cut.isLt.le j) *
          (r^((T.order:ℕ)-1)*Φ T A (Fin.castLE cut.isLt.le j)) =
        r^(T.order:ℕ)*(affineReceiverRow A l (Fin.castLE cut.isLt.le j) *
          Φ T A (Fin.castLE cut.isLt.le j)) := by
      rw [←scal]
      ac_rfl
    rw [Finset.sum_congr rfl (fun j _=>term j),←Finset.mul_sum]
    rw [sum_prefix_zero_tail cut.isLt.le (fun j=>affineReceiverRow A l j*Φ T A j)
      (fun j hj=>by rw [P.row_tail strict j hj,zero_mul])]
    rfl
  change (T.factorial:K)*(b₀ ⬝ᵥ Φ T (r•B))=1
  rw [mass,mul_left_comm,z,←mul_pow]
  simp [r,nz]

end
end RKResearch.Certified.Graded
