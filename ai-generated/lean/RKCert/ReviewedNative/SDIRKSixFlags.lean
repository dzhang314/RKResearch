module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix
variable {K : Type*} [Field K] {s p : ℕ}

def adjResidual (A : Matrix (Fin s) (Fin s) K) (b : (Fin s → K)) : (Fin s → K) →ₗ[K] K :=
  (row b).comp (mat A) + (row b).comp (diag (nodes A)) - row b

/-- The raw adjoint consistency defect kills every affordable genuine stage tree. -/
theorem adjResidual_tree {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder p A b) (t : FiniteRootedTree) (hk : (t.order:ℕ)+1 ≤ p) :
    adjResidual A b (Φ t A) = 0 := by
  let d := ((t.order:ℕ):K)
  let f := ((t.forestFactorial:ℕ):K)
  have a := ho (.leaf ◂ t) (by simp only [order, PNat.add_coe, PNat.one_coe]; omega)
  have c := ho (t ◂ .leaf) (by simp only [order, PNat.add_coe, PNat.one_coe]; omega)
  have w := ho t (by omega)
  have pu : Φ (.leaf ◂ t) A = mat A (Φ t A) := by simp
  have pc : Φ (t ◂ .leaf) A = diag (nodes A) (Φ t A) := by ext i; simp [mul_comm]
  simp only [pu,pc,factorial, order, forestFactorial, PNat.add_coe, PNat.mul_coe, PNat.one_coe,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, one_mul, mul_one] at a c w
  change (1+d)*(d*f) * row b (mat A (Φ t A)) = 1 at a
  change (d+1)*f * row b (diag (nodes A) (Φ t A)) = 1 at c
  change d*f * row b (Φ t A) = 1 at w
  apply ((IsUnit.of_mul_eq_one _ a).mul_left_cancel)
  change (1+d)*(d*f)*(row b (mat A (Φ t A))+row b (diag (nodes A) (Φ t A))-row b (Φ t A)) = _
  linear_combination a + d*c - (d+1)*w

theorem adjResidual_space {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)}
    (ho : HasOrder p A b) (a : ℕ) (hp : a+2≤p) :
    treeSpace A a ≤ LinearMap.ker (adjResidual A b) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  exact adjResidual_tree ho t (by omega)

theorem order_six_grade_ranks {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hd : ∀ i, A i i ≠ 0) :
    (List.range 6).map (fun j => Module.finrank K (treeSpace A j)) = [1,2,4,5,6,6] := by
  let v := fun j => Module.finrank K (treeSpace A j)
  have up (j : ℕ) : v j ≤ 6 := by
    simpa only [v,Module.finrank_fin_fun] using (Submodule.finrank_le (treeSpace A j))
  have low (j : ℕ) (hj : j+1≤6) : parityCensus 6 j ≤ v j := parityCensus_le_finrank ho ha hd j hj
  have h₀ := low 0 (by decide); have h₁ := low 1 (by decide)
  have h₂ := low 2 (by decide); have h₃ := low 3 (by decide)
  have h₄ := low 4 (by decide); have h₅ := low 5 (by decide)
  change 1 ≤ v 0 at h₀; change 2 ≤ v 1 at h₁; change 4 ≤ v 2 at h₂
  change 5 ≤ v 3 at h₃; change 6 ≤ v 4 at h₄; change 6 ≤ v 5 at h₅
  have e₀ := nonsingular_rank_step ho ha hd 0 2 (by decide) (by decide)
  have e₁ := nonsingular_rank_step ho ha hd 1 2 (by decide) (by decide)
  have e₂ := nonsingular_rank_step ho ha hd 2 1 (by decide) (by decide)
  have e₃ := nonsingular_rank_step ho ha hd 3 0 (by decide) (by decide)
  change 3+v 0≤v 2 at e₀; change 3+v 1≤v 3 at e₁
  change 2+v 2≤v 4 at e₂; change 1+v 3≤v 5 at e₃
  have h4 := up 4; have h5 := up 5
  change [v 0,v 1,v 2,v 3,v 4,v 5]=_
  rw [show v 0=1 by omega,show v 1=2 by omega,show v 2=4 by omega,
    show v 3=5 by omega,show v 4=6 by omega,show v 5=6 by omega]

theorem order_six_grade_four_top {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hd : ∀ i, A i i ≠ 0) :
    treeSpace A 4 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [show Module.finrank K ((Fin 6 → K))=6 by simp]
  apply le_antisymm
  · simpa only [Module.finrank_fin_fun] using Submodule.finrank_le (treeSpace A 4)
  · exact parityCensus_le_finrank ho ha hd 4 (by decide)

theorem order_six_D1 {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hd : ∀ i, A i i ≠ 0) :
    adjResidual A b = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ treeSpace A 4 := by rw [order_six_grade_four_top ho ha hd]; exact trivial
  exact adjResidual_space ho 4 (by decide) hx

/-- The priced Volterra image annihilates the actual weighted clock probes. -/
theorem probe_commutator {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {j k : ℕ}
    (ho : HasOrder p A b) (hk : k+j+3 ≤ p) {x} (hx : x ∈ treeSpace A j) :
    probe A b k (volterra A x) = 0 :=
  probe_zeroSpace ho (by omega) (volterra_treeSpace ho j (by omega) hx)

end RKResearch.Certified.Graded.SDIRKSix

