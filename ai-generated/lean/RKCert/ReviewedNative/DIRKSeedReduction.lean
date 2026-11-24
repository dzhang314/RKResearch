module

public import RKCert.ReviewedNative.CausalStage
public import RKCert.ReviewedNative.ReflectedMoments
public import RKCert.ReviewedNative.ChangeCoefficients

public section

/-! # DIRK two-seed reduction to the strict causal lemma

The diagonal of the tableau itself need not vanish. Instead its commutator
with the clock is strictly causal. The two physical seeds give precisely
the one-seed input for this commutator and the *squared* clock. -/

namespace RKResearch.Certified.Graded

open RKResearch
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}

/-- The usual two DIRK seeds force the clocked vector into an invariant
subspace. This is only an adapter to the strict one-seed causal theorem;
there is no second coordinate induction. -/
theorem mem_of_invariant_dirk_two_seeds (ord : Fin s ≃ Fin s)
    (N : (Fin s → K) →ₗ[K] (Fin s → K)) (a y v : Fin s → K)
    (hdiag : ∀ i x, (∀ j, (ord j).val < (ord i).val → x j = 0) → N x i = a i * x i)
    (U : Submodule K (Fin s → K))
    (hN : ∀ x ∈ U, N x ∈ U) (hY : ∀ x ∈ U, diag y x ∈ U)
    (h₂ : (2:K) • N (diag y v) - diag y (diag y v) ∈ U)
    (h₃ : (3:K) • N (diag y (diag y v)) - diag y (diag y (diag y v)) ∈ U) :
    diag y v ∈ U := by
  let Y := diag y
  let N' : (Fin s → K) →ₗ[K] (Fin s → K) := (3:K) • (Y.comp N - N.comp Y)
  let v' : Fin s → K := fun i => (y i)⁻¹ * v i
  have hz : diag (y^2) v' = Y v := by
    ext i
    change (y i)^2 * ((y i)⁻¹ * v i) = y i * v i
    by_cases hy : y i = 0
    · simp [hy]
    · calc
        (y i)^2 * ((y i)⁻¹ * v i) = y i * ((y i * (y i)⁻¹) * v i) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hy, one_mul]
  have hyy (x : Fin s → K) : diag (y^2) x = Y (Y x) := by
    ext i
    change (y i)^2 * x i = y i * (y i * x i)
    rw [pow_two, mul_assoc]
  have hcausal : Causal ord N' := by
    intro i x hx
    have hfirst := hdiag i x hx
    have hsecond := hdiag i (Y x) (fun j hj => by change y j * x j = 0; rw [hx j hj, mul_zero])
    change (3:K) * (y i * N x i - N (Y x) i) = 0
    rw [hfirst, hsecond]
    change (3:K) * (y i * (a i * x i) - a i * (y i * x i)) = 0
    ring
  have hN' (x : Fin s → K) (hx : x ∈ U) : N' x ∈ U :=
    U.smul_mem _ (U.sub_mem (hY _ (hN _ hx)) (hN _ (hY _ hx)))
  have hcomb :
      (2:K) • N' (Y v) - Y (Y (Y v)) =
        (3:K) • Y ((2:K) • N (Y v) - Y (Y v)) -
          (2:K) • ((3:K) • N (Y (Y v)) - Y (Y (Y v))) := by
    rw [map_sub, map_smul]
    ext i
    simp only [N', LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hseed : (2:K) • N' (diag (y^2) v') - diag (y^2) (diag (y^2) v') ∈ U := by
    rw [hz, hyy, hcomb]
    exact U.sub_mem (U.smul_mem _ (hY _ h₂)) (U.smul_mem _ h₃)
  have out := mem_of_invariant_seed ord N' hcausal (y^2) v' U hN'
    (fun x hx => by rw [hyy]; exact hY _ (hY _ hx)) hseed
  rwa [hz] at out

/-- Reverse chronology: the first possibly nonzero coordinate of the
transpose sees exactly the original diagonal entry. -/
theorem transpose_mat_pivot {A : Matrix (Fin s) (Fin s) K} (ha : A.IsLowerTriangular)
    (i : Fin s) (x : Fin s → K) (hx : ∀ j, i < j → x j = 0) :
    mat A.transpose x i = A i i * x i := by
  rw [mat_apply, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_single i
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hji | hij
    · have hz : A j i = 0 := ha hji
      rw [Matrix.transpose_apply, hz, zero_mul]
    · rw [hx j hij, mul_zero]
  · simp

/-- The actual ordinary quadratic/cubic defects are sufficient for the
native DIRK forward no-plateau step. -/
theorem forward_dirk_seeds_force_nodes {A : Matrix (Fin s) (Fin s) K}
    (ha : A.IsLowerTriangular) (U : Submodule K (Fin s → K))
    (hN : ∀ x ∈ U, mat A x ∈ U)
    (hY : ∀ x ∈ U, diag (nodes A) x ∈ U)
    (h₂ : monomialStageDefect A 1 ∈ U) (h₃ : monomialStageDefect A 2 ∈ U) :
    nodes A ∈ U := by
  let y := nodes A
  let Y := diag y
  have hy : Y (1 : Fin s → K) = y := by ext i; simp only [Y, diag_apply, Pi.one_apply, mul_one]
  have hy2 : Y (Y (1 : Fin s → K)) = y^2 := by
    rw [hy]
    ext i
    exact (pow_two _).symm
  have hy3 : Y (Y (Y (1 : Fin s → K))) = y^3 := by
    rw [hy2]
    ext i
    change y i * y i^2 = y i^3
    ring
  have h₂' : (2:K) • mat A (Y 1) - Y (Y 1) ∈ U := by
    rw [hy2, hy]
    convert h₂ using 1
    ext i
    simp only [monomialStageDefect, pow_one, Pi.smul_apply, Pi.sub_apply, Pi.pow_apply,
      mat_apply, smul_eq_mul, Nat.reduceAdd, Nat.cast_ofNat, y, nodes]
  have h₃' : (3:K) • mat A (Y (Y 1)) - Y (Y (Y 1)) ∈ U := by
    rw [hy3, hy2]
    convert h₃ using 1
    ext i
    simp only [monomialStageDefect, Pi.smul_apply, Pi.sub_apply, Pi.pow_apply,
      mat_apply, smul_eq_mul, Nat.reduceAdd, Nat.cast_ofNat, y, nodes]
  have h := mem_of_invariant_dirk_two_seeds (Equiv.refl _) (mat A) (fun i => A i i)
    y 1 (fun i x hx => lowerTriangular_mulVec_pivot ha i x hx) U hN hY h₂' h₃'
  change Y (1 : Fin s → K) ∈ U at h
  rwa [hy] at h

/-- The actual D(2) and D(3) rows supply the reverse no-plateau input.
There is no common-diagonal, nonsingularity or distinct-node premise. -/
theorem reverse_dirk_seeds_force_clock {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : A.IsLowerTriangular) (U : Submodule K (Fin s → K))
    (hN : ∀ x ∈ U, mat A.transpose x ∈ U)
    (hY : ∀ x ∈ U, diag (reflectedClock A) x ∈ U)
    (h₂ : reflectedStageRow A b 1 ∈ U) (h₃ : reflectedStageRow A b 2 ∈ U) :
    diag (reflectedClock A) b ∈ U := by
  let y := reflectedClock A
  let Y := diag y
  have hw₁ : reflectedStageWeight A b 1 = Y b := by
    ext i
    change b i * y i^1 = y i * b i
    rw [pow_one, mul_comm]
  have hw₂ : reflectedStageWeight A b (1+1) = Y (Y b) := by
    ext i
    change b i * y i^2 = y i * (y i * b i)
    ring
  have hw₃ : reflectedStageWeight A b (2+1) = Y (Y (Y b)) := by
    ext i
    change b i * y i^3 = y i * (y i * (y i * b i))
    ring
  have h₂' : (2:K) • mat A.transpose (Y b) - Y (Y b) ∈ U := by
    simpa only [reflectedStageRow, mat_apply, hw₁, hw₂, Nat.reduceAdd, Nat.cast_ofNat] using h₂
  have h₃' : (3:K) • mat A.transpose (Y (Y b)) - Y (Y (Y b)) ∈ U := by
    simpa only [reflectedStageRow, mat_apply, hw₂, hw₃, Nat.reduceAdd,
      Nat.cast_ofNat] using h₃
  exact mem_of_invariant_dirk_two_seeds Fin.revPerm (mat A.transpose) (fun i => A i i)
    y b (fun i x hx => transpose_mat_pivot ha i x (fun j hj => hx j (Fin.rev_lt_rev.mpr hj)))
    U hN hY h₂' h₃'

end RKResearch.Certified.Graded
