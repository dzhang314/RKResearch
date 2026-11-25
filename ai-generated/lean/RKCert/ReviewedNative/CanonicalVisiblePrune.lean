module

public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Source-only gate on a split coordinate algebra. Contexts allow all
coordinate multipliers, as justified after coalescing by the separate
profile adapter. No full-series uniqueness is asserted here. -/
namespace RKResearch.CanonicalVisibility

open RKResearch FiniteRootedTree RKResearch.Certified.Graded
open RKResearch.Certified.Graded.Reverse
open scoped Classical Matrix FiniteRootedTree BigOperators

noncomputable section
variable {ι K : Type*} [Fintype ι] [Field K]
variable (A : Matrix ι ι K) (b : ι → K)

/-- Finite paths carrying stage i to a nonzero output. A step uses
the directed input edge i→j when Aⱼᵢ is nonzero. -/
inductive Visible (M : Matrix ι ι K) (w : ι → K) : ι → Prop where
  | output (i : ι) : w i ≠ 0 → Visible M w i
  | step {i j : ι} : M j i ≠ 0 → Visible M w j → Visible M w i

theorem weight_eq_zero_off {i : ι} (off : ¬ Visible A b i) : b i = 0 := by
  by_contra nz
  exact off (.output i nz)

theorem entry_eq_zero_off {i j : ι} (hit : Visible A b i) (off : ¬ Visible A b j) :
    A i j = 0 := by
  by_contra nz
  exact off (.step nz hit)

/-- Each constructor adds its indicated operation at the input end. -/
inductive Context (ι K : Type*) where
  | empty
  | through : Context ι K → Context ι K
  | multiply : (ι → K) → Context ι K → Context ι K

def Context.eval (M : Matrix ι ι K) : Context ι K → (ι → K) →ₗ[K] (ι → K)
  | .empty => LinearMap.id
  | .through C => (Context.eval M C).comp (mat M)
  | .multiply u C => (Context.eval M C).comp (diag u)

def invisible : Submodule K (ι → K) :=
  ⨅ C : Context ι K, ((row b).comp (C.eval A)).ker

theorem mem_invisible {v : ι → K} :
    v ∈ invisible A b ↔ ∀ C : Context ι K, row b (C.eval A v) = 0 := by
  simp only [invisible, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]

theorem invisible_readout_zero {v : ι → K} (hv : v ∈ invisible A b) : row b v = 0 :=
  (mem_invisible A b).mp hv .empty

theorem mat_mem_invisible {v : ι → K} (hv : v ∈ invisible A b) :
    mat A v ∈ invisible A b :=
  (mem_invisible A b).mpr fun C => (mem_invisible A b).mp hv (.through C)

theorem mul_mem_invisible (u : ι → K) {v : ι → K} (hv : v ∈ invisible A b) :
    u*v ∈ invisible A b :=
  (mem_invisible A b).mpr fun C => (mem_invisible A b).mp hv (.multiply u C)

def invisibleIdeal : Ideal (ι → K) where
  carrier := (invisible A b : Set (ι → K))
  zero_mem' := (invisible A b).zero_mem
  add_mem' := fun hx hy => (invisible A b).add_mem hx hy
  smul_mem' u v hv := by
    change u*v ∈ invisible A b
    exact mul_mem_invisible A b u hv

theorem ideal_le_invisibleIdeal (J : Ideal (ι → K))
    (stable : ∀ v ∈ J, mat A v ∈ J) (kill : ∀ v ∈ J, row b v = 0) :
    J ≤ invisibleIdeal A b := by
  intro v hv
  change v ∈ invisible A b
  apply (mem_invisible A b).mpr
  intro C
  apply kill
  induction C generalizing v with
  | empty => exact hv
  | through C ih =>
    apply ih
    exact stable _ hv
  | multiply u C ih =>
    apply ih
    have uv : u*v ∈ J := by simpa only [smul_eq_mul] using J.smul_mem u hv
    exact uv

theorem invisibleIdeal_greatest :
    IsGreatest {J : Ideal (ι → K) |
      (∀ v ∈ J, mat A v ∈ J) ∧ (∀ v ∈ J, row b v = 0)} (invisibleIdeal A b) := by
  refine ⟨⟨fun _ hv => mat_mem_invisible A b hv, fun _ hv => invisible_readout_zero A b hv⟩, ?_⟩
  intro J hJ
  exact ideal_le_invisibleIdeal A b J hJ.1 hJ.2

private theorem gate_coordinate (i : ι) (v : ι → K) :
    coordinate (K:=K) i*v = v i • coordinate i := by
  classical
  funext j
  by_cases same : j=i
  · subst j
    simp [coordinate, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  · simp [coordinate, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne same]

private theorem mat_coordinate (i j : ι) : mat A (coordinate (K:=K) j) i = A i j := by
  classical
  rw [mat_apply, coordinate, Matrix.mulVec_single_one, Matrix.col_apply]

/-- A path gives an actual one-hole readout extracting precisely one
coordinate times a nonzero scalar, even when b at the source is zero. -/
theorem path_readout {i : ι} (hit : Visible A b i) :
    ∃ C : Context ι K, ∃ a : K, a ≠ 0 ∧
      ∀ v : ι → K, row b (C.eval A v) = a*v i := by
  induction hit with
  | output i nz =>
    refine ⟨.multiply (coordinate i) .empty, b i, nz, ?_⟩
    intro v
    change row b (coordinate i*v) = b i*v i
    simp only [gate_coordinate, map_smul, row_coordinate, smul_eq_mul] <;> ac_rfl
  | @step i j edge seen ih =>
    obtain ⟨C, a, nz, law⟩ := ih
    refine ⟨.multiply (coordinate i) (.through C), a*A j i, mul_ne_zero nz edge, ?_⟩
    intro v
    change row b (C.eval A (mat A (coordinate i*v))) = (a*A j i)*v i
    rw [law]
    simp only [gate_coordinate, map_smul, Pi.smul_apply, smul_eq_mul, mat_coordinate] <;> ac_rfl

private theorem mat_zero_visible {v : ι → K} (hv : ∀ i, Visible A b i → v i = 0)
    (i : ι) (hi : Visible A b i) : mat A v i = 0 := by
  rw [mat_apply, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases seen : Visible A b j
  · rw [hv j seen, mul_zero]
  · rw [entry_eq_zero_off A b hi seen, zero_mul]

private theorem context_zero_visible (C : Context ι K) {v : ι → K}
    (hv : ∀ i, Visible A b i → v i = 0) : ∀ i, Visible A b i → C.eval A v i = 0 := by
  induction C generalizing v with
  | empty => exact hv
  | through C ih =>
    apply ih
    exact mat_zero_visible A b hv
  | multiply u C ih =>
    apply ih
    intro i hi
    simp only [diag_apply, hv i hi, mul_zero]

private theorem row_zero_visible {v : ι → K} (hv : ∀ i, Visible A b i → v i = 0) :
    row b v = 0 := by
  rw [row_apply, dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases seen : Visible A b i
  · rw [hv i seen, mul_zero]
  · rw [weight_eq_zero_off A b seen, zero_mul]

theorem mem_invisible_iff_zero_on_visible {v : ι → K} :
    v ∈ invisible A b ↔ ∀ i, Visible A b i → v i = 0 := by
  constructor
  · intro hv i hi
    obtain ⟨C, a, nz, law⟩ := path_readout A b hi
    have read := (mem_invisible A b).mp hv C
    rw [law] at read
    exact (mul_eq_zero.mp read).resolve_left nz
  · intro hv
    exact (mem_invisible A b).mpr fun C =>
      row_zero_visible A b (context_zero_visible A b C hv)

theorem mem_invisibleIdeal_iff {v : ι → K} :
    v ∈ invisibleIdeal A b ↔ ∀ i, Visible A b i → v i = 0 :=
  mem_invisible_iff_zero_on_visible A b

theorem coordinate_mem_invisibleIdeal_iff (i : ι) :
    coordinate (K:=K) i ∈ invisibleIdeal A b ↔ ¬ Visible A b i := by
  rw [mem_invisibleIdeal_iff]
  constructor
  · intro h hit
    have bad := h i hit
    simp [coordinate] at bad
  · intro off j hj
    have ne : j≠i := fun eq => off (eq ▸ hj)
    simp [coordinate, Pi.single_eq_of_ne ne]

def visibleSet : Finset ι :=
  Finset.univ.filter (Visible A b)

theorem mem_visibleSet (i : ι) : i ∈ visibleSet A b ↔ Visible A b i := by
  simp [visibleSet]

abbrev VisibleIndex := ↥(visibleSet A b)

def pruneRestrict (v : ι → K) (i : VisibleIndex A b) : K := v i.val

def prunedMatrix : Matrix (VisibleIndex A b) (VisibleIndex A b) K :=
  fun i j => A i.val j.val

def prunedWeight (i : VisibleIndex A b) : K := b i.val

private theorem sum_visible_of_off (f : ι → K) (zero : ∀ i, ¬ Visible A b i → f i = 0) :
    (∑ i : VisibleIndex A b, f i.val) = ∑ i, f i := by
  rw [Finset.sum_coe_sort (visibleSet A b)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ off
  exact zero i (fun hit => off ((mem_visibleSet A b i).mpr hit))

theorem pruned_mulVec (v : ι → K) :
    prunedMatrix A b *ᵥ pruneRestrict A b v = pruneRestrict A b (A *ᵥ v) := by
  funext i
  simp only [prunedMatrix, pruneRestrict, Matrix.mulVec_apply_eq_sum]
  exact sum_visible_of_off A b (fun j => A i.val j*v j) (fun j off => by
    rw [entry_eq_zero_off A b ((mem_visibleSet A b i.val).mp i.property) off, zero_mul])

private theorem pruneRestrict_mul (v w : ι → K) :
    pruneRestrict A b (v*w) = pruneRestrict A b v * pruneRestrict A b w := rfl

theorem Φ_pruned (t : FiniteRootedTree) :
    Φ t (prunedMatrix A b) = pruneRestrict A b (Φ t A) := by
  induction t with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    simp only [Φ, ht, hu, pruned_mulVec, pruneRestrict_mul]

theorem pruned_scalar_output (t : FiniteRootedTree) :
    prunedWeight A b ⬝ᵥ Φ t (prunedMatrix A b) = b ⬝ᵥ Φ t A := by
  rw [Φ_pruned]
  simp only [prunedWeight, pruneRestrict, dotProduct]
  exact sum_visible_of_off A b (fun i => b i*Φ t A i) (fun i off => by
    rw [weight_eq_zero_off A b off, zero_mul])

theorem pruned_hasOrder_iff (p : ℕ) :
    HasOrder p (prunedMatrix A b) (prunedWeight A b) ↔ HasOrder p A b := by
  constructor
  · intro h t ht
    simpa only [pruned_scalar_output A b t] using h t ht
  · intro h t ht
    change (t.factorial : K) * (prunedWeight A b ⬝ᵥ Φ t (prunedMatrix A b)) = 1
    rw [pruned_scalar_output]
    exact h t ht

private theorem visible_pruned_of_path {i : ι} (hi : Visible A b i) :
    Visible (prunedMatrix A b) (prunedWeight A b) ⟨i, (mem_visibleSet A b i).mpr hi⟩ := by
  induction hi with
  | output i nz => exact .output _ nz
  | @step i j e hj ih =>
    refine Visible.step (j:=⟨j, (mem_visibleSet A b j).mpr hj⟩) ?_ ih
    change A j i ≠ 0
    exact e

theorem visible_pruned (i : VisibleIndex A b) :
    Visible (prunedMatrix A b) (prunedWeight A b) i :=
  visible_pruned_of_path A b ((mem_visibleSet A b i.val).mp i.property)

theorem invisible_pruned_eq_bot :
    invisible (prunedMatrix A b) (prunedWeight A b) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  funext i
  exact (mem_invisible_iff_zero_on_visible _ _).mp hv i (visible_pruned A b i)

end
end RKResearch.CanonicalVisibility
