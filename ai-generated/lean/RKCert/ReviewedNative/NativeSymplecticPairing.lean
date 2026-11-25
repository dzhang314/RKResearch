module

public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.RowAnnihilator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.Graded

open RKResearch FiniteRootedTree
open scoped BigOperators FiniteRootedTree Matrix

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K]

def positiveCross (A : Matrix ι ι K) (b : ι → K) :
    (ι → K) →ₗ[K] (ι → K) →ₗ[K] K :=
  (dotProductBilin K K).compl₁₂ (diag b) (mat A)

def symplecticPair (A : Matrix ι ι K) (b : ι → K) :
    (ι → K) →ₗ[K] (ι → K) →ₗ[K] K :=
  positiveCross A b + (positiveCross A b).flip -
    (LinearMap.mul K K).compl₁₂ (row b) (row b)

private theorem positiveCross_apply (A : Matrix ι ι K) (b x z : ι → K) :
    positiveCross A b x z = row b (x*mat A z) := by
  change (diag b x) ⬝ᵥ (mat A z)=row b (x*mat A z)
  simp only [row_apply,dotProduct,diag_apply,Pi.mul_apply,mul_assoc]

theorem symplecticPair_apply (A : Matrix ι ι K) (b x z : ι → K) :
    symplecticPair A b x z =
      row b (x*mat A z)+row b (z*mat A x)-row b x*row b z := by
  simp only [symplecticPair,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.flip_apply,
    LinearMap.compl₁₂_apply,LinearMap.mul_apply',positiveCross_apply]

theorem symplecticPair_comm (A : Matrix ι ι K) (b x z : ι → K) :
    symplecticPair A b x z = symplecticPair A b z x := by
  simp only [symplecticPair_apply]
  ring

theorem symplecticPair_coordinate [DecidableEq ι] (A : Matrix ι ι K)
    (b : ι → K) (i j : ι) :
    symplecticPair A b (Pi.single i 1) (Pi.single j 1) =
      b i*A i j+b j*A j i-b i*b j := by
  have one (i : ι) (v : ι → K) : row b (Pi.single i (1 : K) * v)=b i*v i := by
    rw [row_apply,dotProduct]
    calc
      _ = b i * (((Pi.single i (1 : K) : ι → K) * v) i) := by
        apply Finset.sum_eq_single i
        · intro k _ ki
          simp [Pi.single_eq_of_ne ki]
        · simp
      _ = _ := by simp
  rw [symplecticPair_apply,one,one,mat_apply,mat_apply,
    Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  simp only [row_apply,dotProduct_single_one,Matrix.col_apply]

variable [CharZero K]

private theorem phi_mass {A : Matrix ι ι K} {b : ι → K} {p : ℕ}
    (ho : HasOrder p A b) (t : FiniteRootedTree) (ht : (t.order:ℕ)≤p) :
    row b (Φ t A)=1/((t.factorial:ℕ):K) := by
  have f0 : ((t.factorial:ℕ):K)≠0 := Nat.cast_ne_zero.mpr t.factorial.ne_zero
  exact (eq_div_iff f0).mpr (by simpa only [row_apply,mul_comm] using ho t ht)

private theorem symplecticPair_two_trees {A : Matrix ι ι K} {b : ι → K} {p : ℕ}
    (ho : HasOrder p A b) (t u : FiniteRootedTree)
    (paid : (t.order:ℕ)+(u.order:ℕ)≤p) :
    symplecticPair A b (Φ t A) (Φ u A)=0 := by
  have graft (t u : FiniteRootedTree) : Φ t A*mat A (Φ u A)=Φ (t ◂ u) A := rfl
  have a0 : ((t.order:ℕ):K)≠0 := Nat.cast_ne_zero.mpr t.order.ne_zero
  have b0 : ((u.order:ℕ):K)≠0 := Nat.cast_ne_zero.mpr u.order.ne_zero
  have f0 : ((t.forestFactorial:ℕ):K)≠0 := Nat.cast_ne_zero.mpr t.forestFactorial.ne_zero
  have g0 : ((u.forestFactorial:ℕ):K)≠0 := Nat.cast_ne_zero.mpr u.forestFactorial.ne_zero
  have ab : ((t.order:ℕ):K)+((u.order:ℕ):K)≠0 := by
    rw [←Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by have h := t.order.ne_zero; omega)
  have ba : ((u.order:ℕ):K)+((t.order:ℕ):K)≠0 := by rwa [add_comm]
  rw [symplecticPair_apply,graft,graft,
    phi_mass ho (t ◂ u) (by simpa only [order,PNat.add_coe] using paid),
    phi_mass ho (u ◂ t) (by simpa only [order,PNat.add_coe,Nat.add_comm] using paid),
    phi_mass ho t (by omega),phi_mass ho u (by omega)]
  simp only [factorial,order,forestFactorial,PNat.mul_coe,PNat.add_coe,Nat.cast_add,Nat.cast_mul]
  field_simp [a0,b0,f0,g0,ab,ba] <;> ring

/-- Exact ordered-tree grade cost; neither explicitness nor actual
symplecticity of the tableau is a premise. -/
theorem symplecticPair_zero_on_paid_tree_spaces
    {A : Matrix ι ι K} {b : ι → K} {p m n : ℕ}
    (ho : HasOrder p A b) (pay : m+n+2≤p) {x z : ι → K}
    (hx : x∈treeSpace A m) (hz : z∈treeSpace A n) :
    symplecticPair A b x z=0 := by
  suffices h : symplecticPair A b x z∈(⊥:Submodule K K) from by rwa [Submodule.mem_bot] at h
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ (symplecticPair A b) _ _ _ hx hz
  rintro _ ⟨t,ht,rfl⟩ _ ⟨u,hu,rfl⟩
  rw [Submodule.mem_bot]
  exact symplecticPair_two_trees ho t u (by omega)

end
end RKResearch.Certified.Graded
