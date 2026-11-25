module

public import RKCert.ReviewedNative.HankelPaidMonicBasis

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The paid residual determines the finite restart tent

All residual tests have an explicit cap matching the requested width.
The next antidiagonal is only assumed nonzero when it can occur. -/
namespace RKResearch.Certified.Graded.HankelPaidRestart

open Matrix Polynomial HankelPaidMonicBasis HankelAntiTriangularRank
open scoped Matrix Polynomial BigOperators

noncomputable section
variable {K : Type*} [Field K]

def nullity (J : K[X] →ₗ[K] K) (w : ℕ) : ℕ := w-(hankel J w).rank

def residual (J : K[X] →ₗ[K] K) (B : K[X]) (k : ℕ) : K :=
  J (X^k*B)

private def afterRestart {r q : ℕ} (B : K[X]) (i : Fin (r+q)) : K[X] :=
  ((finSumFinEquiv (m := r) (n := q)).symm i).elim (fun j : Fin r => X^j.val) (fun j : Fin q => X^j.val*B)

@[simp] private theorem afterRestart_left {r q : ℕ} (B : K[X]) (i : Fin r) :
    afterRestart (r := r) (q := q) B (Fin.castAdd q i)=X^i.val := by
  simp [afterRestart]

@[simp] private theorem afterRestart_right {r q : ℕ} (B : K[X]) (i : Fin q) :
    afterRestart (r := r) (q := q) B (Fin.natAdd r i)=X^i.val*B := by
  simp [afterRestart]

private theorem afterRestart_monic_and_degree {r q : ℕ} {B : K[X]}
    (bm : B.Monic) (bd : B.natDegree=r) (i : Fin (r+q)) :
    (afterRestart (r := r) (q := q) B i).Monic ∧
      (afterRestart (r := r) (q := q) B i).natDegree=i.val := by
  let e : Fin r ⊕ Fin q ≃ Fin (r+q) := finSumFinEquiv
  obtain ⟨j,rfl⟩ := e.surjective i
  rcases j with j | j
  · change (afterRestart (r := r) (q := q) B (Fin.castAdd q j)).Monic ∧
      (afterRestart (r := r) (q := q) B (Fin.castAdd q j)).natDegree=(Fin.castAdd q j).val
    simp only [afterRestart_left,Fin.val_castAdd,natDegree_X_pow,and_true]
    exact monic_X_pow _
  · change (afterRestart (r := r) (q := q) B (Fin.natAdd r j)).Monic ∧
      (afterRestart (r := r) (q := q) B (Fin.natAdd r j)).natDegree=(Fin.natAdd r j).val
    rw [afterRestart_right]
    refine ⟨(monic_X_pow _).mul bm,?_⟩
    rw [natDegree_mul (monic_X_pow _).ne_zero bm.ne_zero,natDegree_X_pow,bd,Fin.val_natAdd,Nat.add_comm]

private def residualBlock (J : K[X] →ₗ[K] K) (B : K[X]) (q : ℕ) :
    Matrix (Fin q) (Fin q) K :=
  fun i j => J ((X^i.val*B)*(X^j.val*B))

private theorem residualBlock_front (J : K[X] →ₗ[K] K) {B : K[X]}
    {r q s : ℕ} (bm : B.Monic) (bd : B.natDegree=r)
    (zeros : ∀ k, k<r+s → k+r≤2*(r+q)-2 → residual J B k=0)
    (i j : Fin q) (order : i.val+j.val≤s) :
    residualBlock J B q i j = residual J B (r+(i.val+j.val)) := by
  have hi := i.isLt
  have hj := j.isLt
  have top : B.coeff r=1 := by rw [← bd,coeff_natDegree,bm.leadingCoeff]
  let L : K[X] := ∑ k ∈ Finset.range r, C (B.coeff k)*X^k
  have expansion : B=X^r+L := by
    have h := B.as_sum_range_C_mul_X_pow' (n := r+1) (by rw [bd]; omega)
    rw [Finset.sum_range_succ,top,map_one,one_mul] at h
    simpa only [L,add_comm] using h
  let k := i.val+j.val
  have paidLow : J (L*(X^k*B))=0 := by
    rw [show L*(X^k*B) = ∑ t ∈ Finset.range r, (C (B.coeff t)*X^t)*(X^k*B) by
      simp only [L,Finset.sum_mul],map_sum]
    apply Finset.sum_eq_zero
    intro t ht
    have tlt := Finset.mem_range.mp ht
    have term : (C (B.coeff t)*X^t)*(X^k*B)=C (B.coeff t)*(X^(t+k)*B) := by
      rw [pow_add (X : K[X]) t k]
      ac_rfl
    have test : J (X^(t+k)*B)=0 := by
      apply zeros
      all_goals
        dsimp only [k]
        omega
    rw [term,← Polynomial.smul_eq_C_mul,map_smul,test,smul_zero]
  change J ((X^i.val*B)*(X^j.val*B)) = J (X^(r+k)*B)
  calc
    _ = J (B*(X^k*B)) := by
      congr 1
      dsimp only [k]
      rw [pow_add]
      ac_rfl
    _ = J ((X^r+L)*(X^k*B)) := congrArg (fun U : K[X] => J (U*(X^k*B))) expansion
    _ = _ := by rw [add_mul,map_add,paidLow,add_zero,← mul_assoc,← pow_add]

/-- Exact scalar matrix rank on a visible tent. The residual zeros
are confined to raw masked degree 2(r+q)−2. If there is no
anti-diagonal within that band, `live` is vacuous. -/
theorem rank_from_paid_residual (J : K[X] →ₗ[K] K) {B : K[X]} {r q s : ℕ}
    (qs : q≤s+1) (lead : (hankel J r).det≠0) (bm : B.Monic) (bd : B.natDegree=r)
    (zeros : ∀ k, k<r+s → k+r≤2*(r+q)-2 → residual J B k=0)
    (live : s+1<2*q → residual J B (r+s)≠0) :
    (hankel J (r+q)).rank=r+(2*q-(s+1)) := by
  let Powers := afterRestart (r := r) (q := q) B
  let e : Fin r ⊕ Fin q ≃ Fin (r+q) := finSumFinEquiv
  let G := pairGram J Powers Powers
  let C := residualBlock J B q
  have ortho (i : Fin r) (j : Fin q) : J ((X:K[X])^i.val*(X^j.val*B))=0 := by
    rw [← mul_assoc,← pow_add]
    apply zeros
    all_goals
      have il := i.isLt
      have jl := j.isLt
      omega
  have shape : G.submatrix e e = Matrix.fromBlocks (hankel J r) 0 0 C := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change J (Powers (Fin.castAdd q i)*Powers (Fin.castAdd q j)) =
          J ((X:K[X])^i.val*X^j.val)
        simp only [Powers,afterRestart_left]
      | inr j =>
        change J (Powers (Fin.castAdd q i)*Powers (Fin.natAdd r j))=0
        simpa only [Powers,afterRestart_left,afterRestart_right] using ortho i j
    | inr i =>
      cases j with
      | inl j =>
        change J (Powers (Fin.natAdd r i)*Powers (Fin.castAdd q j))=0
        simp only [Powers,afterRestart_right,afterRestart_left]
        rw [mul_comm]
        exact ortho j i
      | inr j =>
        change J (Powers (Fin.natAdd r i)*Powers (Fin.natAdd r j)) =
          J ((X^i.val*B)*(X^j.val*B))
        simp only [Powers,afterRestart_right]
  have tail : C.rank=2*q-(s+1) := by
    apply rank_delayed_antidiagonal qs
    · intro i j ij
      change residualBlock J B q i j=0
      rw [residualBlock_front J bm bd zeros i j ij.le]
      apply zeros
      all_goals
        have il := i.isLt
        have jl := j.isLt
        omega
    · intro i j ij
      change residualBlock J B q i j≠0
      rw [residualBlock_front J bm bd zeros i j ij.le,ij]
      apply live
      have il := i.isLt
      have jl := j.isLt
      omega
  have same : G.rank = (hankel J (r+q)).rank :=
    rank_pairGram_of_monic_degrees J Powers
      (fun i => (afterRestart_monic_and_degree bm bd i).1)
      (fun i => (afterRestart_monic_and_degree bm bd i).2)
  have seed : (hankel J r).rank=r := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero lead
  rw [← same,← Matrix.rank_submatrix G e e,shape,rank_fromBlocks_zero_cross,seed,tail]

theorem nullity_from_paid_residual (J : K[X] →ₗ[K] K) {B : K[X]} {r q s : ℕ}
    (qs : q≤s+1) (lead : (hankel J r).det≠0) (bm : B.Monic) (bd : B.natDegree=r)
    (zeros : ∀ k, k<r+s → k+r≤2*(r+q)-2 → residual J B k=0)
    (live : s+1<2*q → residual J B (r+s)≠0) :
    nullity J (r+q)=min q (s+1-q) := by
  unfold nullity
  rw [rank_from_paid_residual J qs lead bm bd zeros live]
  by_cases h : q≤s+1-q
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (show s+1-q≤q by omega)]
    omega

end
end RKResearch.Certified.Graded.HankelPaidRestart
