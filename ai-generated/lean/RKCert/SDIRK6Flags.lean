module

public import RKCert.SDIRKStageFloor
public import RKCert.Field

@[expose] public section

namespace RKCert.Paired.SDIRK
open RKCert.Paired
variable {K : Type*} [Field K] {s p : ℕ}

def adjResidual (A : Fin s → Fin s → K) (b : Vec K s) : Vec K s →ₗ[K] K :=
  (row b).comp (mat A) + (row b).comp (diag (nodes A)) - row b

/-- The raw adjoint consistency defect kills every affordable genuine stage tree. -/
theorem adjResidual_tree {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (hk : t.order+1 ≤ p) :
    adjResidual A b (stageWeight A t) = 0 := by
  let ta := t.attach .leaf
  let tc := Tree.attach .leaf t
  have h₁ := ho ta (by dsimp [ta, Tree.order]; omega)
  have h₂ := ho tc (by dsimp [tc, Tree.order]; omega)
  have h₀ := ho t (by omega)
  simp only [Tree.density, ta, tc, Tree.order, Tree.childDensityProduct, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, one_mul, mul_one] at h₀ h₁ h₂
  have hu : ((t.order:K)+1)*((t.order:K)*(t.childDensityProduct:K)) ≠ 0 := by
    apply (IsUnit.of_mul_eq_one _ h₁).ne_zero
  have hh : adjResidual A b (stageWeight A t) = weight A b ta + weight A b tc - weight A b t := by
    change (∑ i, b i * mat A (stageWeight A t) i) + (∑ i, b i * diag (nodes A) (stageWeight A t) i) - _ = _
    simp only [ta,tc,weight,stageWeight,mat_apply,diag_apply,nodes,mul_one,row_apply]
  rw [hh]
  apply (mul_eq_zero.mp (show ((t.order:K)+1)*((t.order:K)*(t.childDensityProduct:K)) *
    (weight A b ta + weight A b tc - weight A b t) = 0 from ?_)).resolve_left hu
  dsimp [ta,tc]
  linear_combination h₁ + (t.order:K)*h₂ - ((t.order:K)+1)*h₀

theorem adjResidual_space {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (a : ℕ) (hp : a+2≤p) :
    treeSpace A a ≤ LinearMap.ker (adjResidual A b) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  exact adjResidual_tree ho t (by omega)

theorem order_six_grade_ranks {A : Fin 6 → Fin 6 → K} {b : Vec K 6}
    (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hd : ∀ i, A i i ≠ 0) :
    (List.range 6).map (fun j => Module.finrank K (treeSpace A j)) = [1,2,4,5,6,6] := by
  let v := fun j => Module.finrank K (treeSpace A j)
  have up (j : ℕ) : v j ≤ 6 := by
    simpa only [v,Vec,Module.finrank_fin_fun] using (Submodule.finrank_le (treeSpace A j))
  have low (j : ℕ) (hj : j+1≤6) : census 6 j ≤ v j := census_le ho ha hd j hj
  have h₀ := low 0 (by decide); have h₁ := low 1 (by decide)
  have h₂ := low 2 (by decide); have h₃ := low 3 (by decide)
  have h₄ := low 4 (by decide); have h₅ := low 5 (by decide)
  change 1 ≤ v 0 at h₀; change 2 ≤ v 1 at h₁; change 4 ≤ v 2 at h₂
  change 5 ≤ v 3 at h₃; change 6 ≤ v 4 at h₄; change 6 ≤ v 5 at h₅
  have e₀ := stage_rank_step ho ha hd 0 2 (by decide) (by decide)
  have e₁ := stage_rank_step ho ha hd 1 2 (by decide) (by decide)
  have e₂ := stage_rank_step ho ha hd 2 1 (by decide) (by decide)
  have e₃ := stage_rank_step ho ha hd 3 0 (by decide) (by decide)
  change 3+v 0≤v 2 at e₀; change 3+v 1≤v 3 at e₁
  change 2+v 2≤v 4 at e₂; change 1+v 3≤v 5 at e₃
  have h4 := up 4; have h5 := up 5
  change [v 0,v 1,v 2,v 3,v 4,v 5]=_
  rw [show v 0=1 by omega,show v 1=2 by omega,show v 2=4 by omega,
    show v 3=5 by omega,show v 4=6 by omega,show v 5=6 by omega]

theorem order_six_grade_four_top {A : Fin 6 → Fin 6 → K} {b : Vec K 6}
    (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hd : ∀ i, A i i ≠ 0) :
    treeSpace A 4 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [show Module.finrank K (Vec K 6)=6 by simp [Vec]]
  apply le_antisymm
  · simpa only [Vec,Module.finrank_fin_fun] using Submodule.finrank_le (treeSpace A 4)
  · exact census_le ho ha hd 4 (by decide)

theorem order_six_D1 {A : Fin 6 → Fin 6 → K} {b : Vec K 6}
    (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hd : ∀ i, A i i ≠ 0) :
    adjResidual A b = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ treeSpace A 4 := by rw [order_six_grade_four_top ho ha hd]; exact trivial
  exact adjResidual_space ho 4 (by decide) hx

end RKCert.Paired.SDIRK

