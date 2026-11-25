module

public import RKCert.ReviewedNative.Explicit
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A common-diagonal tall-tree obstruction at any paid width

The shifted tableau is strictly lower triangular. The reviewed tall-tree
formula for its zero stage column then gives a single binomial relation
among the paid tall moments of the original tableau. -/

namespace RKResearch

open FiniteRootedTree
open scoped Matrix BigOperators

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}

private def tallMatrixMoment (b : Fin s → K) : Matrix (Fin s) (Fin s) K →ₗ[K] K where
  toFun M := b ⬝ᵥ (M *ᵥ 1)
  map_add' M N := by rw [Matrix.add_mulVec,dotProduct_add]
  map_smul' c M := by
    simp only [RingHom.id_apply,Matrix.smul_mulVec,dotProduct_smul]

/-- The ordinary tall moment in the reviewed tableau. No characteristic
assumption is necessary: its factorial is a unit because order is paid. -/
theorem HasOrder.tall_moment_eq_inv_factorial (ho : HasOrder p A b) (k : ℕ)
    (pay : k+1 ≤ p) :
    b ⬝ᵥ ((A^k) *ᵥ 1) = 1 / (((k+1).factorial : ℕ) : K) := by
  let n : ℕ+ := ⟨k+1,Nat.succ_pos k⟩
  have hp : ((tallTree n).order : ℕ) ≤ p := by
    rw [order_tallTree]
    exact pay
  have h := ho (tallTree n) hp
  rw [factorial_tallTree,Φ_tallTree] at h
  change (((k+1).factorial : ℕ) : K) *
    (b ⬝ᵥ ((A^(k+1-1)) *ᵥ 1)) = 1 at h
  rw [Nat.add_sub_cancel] at h
  have hn : (((k+1).factorial : ℕ) : K) ≠ 0 := (IsUnit.of_mul_eq_one _ h).ne_zero
  exact (eq_div_iff hn).mpr (by rw [mul_comm]; exact h)

/-- When s≤m, the m-th tall column of the shifted tableau is zero.
This handles smaller and empty tableaux without physically padding. -/
theorem shifted_common_diagonal_tall_zero (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = γ) (m : ℕ) (hs : s ≤ m) :
    ((A+(-γ) • (1 : Matrix (Fin s) (Fin s) K)) ^ m) *ᵥ (1 : Fin s → K) = 0 := by
  let T : Matrix (Fin s) (Fin s) K := A+(-γ) • 1
  have hT (i j : Fin s) (hij : i ≤ j) : T i j = 0 := by
    rcases eq_or_lt_of_le hij with rfl | h
    · simp [T,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,hc]
    · simp [T,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_ne h.ne,ha h]
  let n : ℕ+ := ⟨m+1,Nat.succ_pos m⟩
  funext i
  have hi : i.val+1 < (n : ℕ) := by
    change i.val+1 < m+1
    have := i.isLt
    omega
  have he := Certified.phi_tallTree_eq_zero hT n i hi
  rw [Φ_tallTree] at he
  change ((T^(m+1-1)) *ᵥ (1 : Fin s → K)) i = 0 at he
  rw [Nat.add_sub_cancel] at he
  exact he

/-- Universal binomial obstruction on a diagonal when the paid order
exceeds the chosen exponent and it is at least the number of stages. -/
theorem HasOrder.common_diagonal_tall_binomial_obstruction (ho : HasOrder p A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) (m : ℕ)
    (hs : s ≤ m) (hp : m+1 ≤ p) :
    (∑ k ∈ Finset.range (m+1), (m.choose k : K) * (-γ)^(m-k) /
      (((k+1).factorial : ℕ) : K)) = 0 := by
  let D : Matrix (Fin s) (Fin s) K := (-γ) • 1
  let F := tallMatrixMoment b
  have hz : F ((A+D)^m) = 0 := by
    change b ⬝ᵥ (((A+(-γ) • (1 : Matrix (Fin s) (Fin s) K))^m) *ᵥ 1) = 0
    rw [shifted_common_diagonal_tall_zero ha hc m hs,dotProduct_zero]
  have com : Commute A D := by
    change A*((-γ) • (1 : Matrix (Fin s) (Fin s) K)) =
      ((-γ) • (1 : Matrix (Fin s) (Fin s) K))*A
    rw [Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul]
  have bin := com.add_pow' m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => m.choose i • (A^i*D^j)) m] at bin
  rw [bin,map_sum] at hz
  have dPow (j : ℕ) : D^j = (-γ)^j • (1 : Matrix (Fin s) (Fin s) K) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ,ih,Matrix.smul_mul,one_mul]
      change (-γ)^j • ((-γ) • (1 : Matrix (Fin s) (Fin s) K)) = (-γ)^(j+1) • 1
      rw [smul_smul,← pow_succ]
  calc
    (∑ k ∈ Finset.range (m+1), (m.choose k : K) * (-γ)^(m-k) /
      (((k+1).factorial : ℕ) : K)) =
        ∑ k ∈ Finset.range (m+1), F (m.choose k • (A^k*D^(m-k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k+1 ≤ p := by
        have := Finset.mem_range.mp hk
        omega
      have hm : F (A^k) = 1 / (((k+1).factorial : ℕ) : K) :=
        ho.tall_moment_eq_inv_factorial k hk'
      rw [dPow,Matrix.mul_smul,mul_one,map_nsmul,map_smul,hm,nsmul_eq_mul,smul_eq_mul]
      ring
    _ = 0 := hz

end RKResearch
