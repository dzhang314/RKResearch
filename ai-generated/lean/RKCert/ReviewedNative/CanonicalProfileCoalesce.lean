module

public import RKCert.ReviewedNative.CausalMerge
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.NativeCoordinateClassAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Source-only first gate for the canonical realization: coalescing the
actual full-profile classes preserves every rooted output. No pruning,
minimality, or uniqueness is asserted in this module. -/
namespace RKResearch.CanonicalProfile

open RKResearch FiniteRootedTree RKResearch.Certified.Graded
open RKResearch.Certified.Graded.PhysicalCensus
open scoped Classical BigOperators FiniteRootedTree Matrix

noncomputable section
variable {K : Type*} [Field K] {s n : ℕ}

def profile (A : Matrix (Fin s) (Fin s) K) (i : Fin s) : FiniteRootedTree → K :=
  fun t => Φ t A i

/-- Label equality is precisely agreement on all literal tree stage columns.
The representative need not be earliest for the scalar-series theorem. -/
structure Partition (A : Matrix (Fin s) (Fin s) K) (n : ℕ) where
  label : Fin s → Fin n
  rep : Fin n → Fin s
  label_rep : ∀ a, label (rep a) = a
  label_eq_iff : ∀ i j, label i = label j ↔ ∀ t : FiniteRootedTree, Φ t A i = Φ t A j

def profileValues (A : Matrix (Fin s) (Fin s) K) : Finset (FiniteRootedTree → K) :=
  Finset.univ.image (profile A)

private def profileIndex (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    ↥(profileValues A) :=
  ⟨profile A i, Finset.mem_image_of_mem (profile A) (Finset.mem_univ i)⟩

private theorem profileIndex_surjective (A : Matrix (Fin s) (Fin s) K) :
    Function.Surjective (profileIndex A) := by
  intro f
  have mem : f.val ∈ (Finset.univ : Finset (Fin s)).image (profile A) := f.property
  obtain ⟨i, _, eq⟩ := Finset.mem_image.mp mem
  exact ⟨i, Subtype.ext eq⟩

/-- The unordered finite image of the full profiles is enough for existence.
There is no algorithmic or chronological claim about this choice. -/
@[no_expose] def canonicalPartition (A : Matrix (Fin s) (Fin s) K) : Partition A (profileValues A).card := by
  let e : ↥(profileValues A) ≃ Fin (profileValues A).card :=
    (Fintype.equivFin (↥(profileValues A))).trans (finCongr (by simp only [Fintype.card_coe]))
  let label : Fin s → Fin (profileValues A).card := fun i => e (profileIndex A i)
  have onto : Function.Surjective label := e.surjective.comp (profileIndex_surjective A)
  refine ⟨label, fun a => Classical.choose (onto a), fun a => Classical.choose_spec (onto a), ?_⟩
  intro i j
  constructor
  · intro eq t
    have same : profileIndex A i = profileIndex A j := e.injective eq
    exact congrArg (fun x : ↥(profileValues A) => x.val t) same
  · intro agree
    change e (profileIndex A i) = e (profileIndex A j)
    apply congrArg e
    apply Subtype.ext
    funext t
    exact agree t

def reachable (A : Matrix (Fin s) (Fin s) K) : Submodule K (Fin s → K) :=
  Submodule.span K (Set.range fun t : FiniteRootedTree => Φ t A)

theorem tree_mem_reachable (A : Matrix (Fin s) (Fin s) K) (t : FiniteRootedTree) :
    Φ t A ∈ reachable A :=
  Submodule.subset_span ⟨t, rfl⟩

theorem one_mem_reachable (A : Matrix (Fin s) (Fin s) K) : 1 ∈ reachable A := by
  exact tree_mem_reachable A .leaf

theorem treeSpace_le_reachable (A : Matrix (Fin s) (Fin s) K) (q : ℕ) :
    treeSpace A q ≤ reachable A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, _, rfl⟩
  exact tree_mem_reachable A t

variable {A : Matrix (Fin s) (Fin s) K}

theorem mat_mem_reachable {v : Fin s → K} (hv : v ∈ reachable A) :
    mat A v ∈ reachable A := by
  have closed : reachable A ≤ (reachable A).comap (mat A) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change mat A (Φ t A) ∈ reachable A
    simpa only [Φ, one_mul, mat_apply] using tree_mem_reachable A (.leaf ◂ t)
  exact closed hv

theorem mul_mem_reachable {v w : Fin s → K} (hv : v ∈ reachable A) (hw : w ∈ reachable A) :
    v*w ∈ reachable A := by
  rw [← LinearMap.mul_apply' (R:=K)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _
    (LinearMap.mul K (Fin s → K)) _ _ _ hv hw
  rintro _ ⟨t, rfl⟩ _ ⟨u, rfl⟩
  rw [LinearMap.mul_apply' (R:=K), ← Φ_rootedSum]
  exact tree_mem_reachable A _

namespace Partition

variable (P : Partition A n)

theorem agree_of_mem {v : Fin s → K} (hv : v ∈ reachable A) {i j : Fin s}
    (same : P.label i = P.label j) : v i = v j := by
  let test : (Fin s → K) →ₗ[K] K :=
    LinearMap.proj (R:=K) (φ:=fun _ : Fin s => K) i -
      LinearMap.proj (R:=K) (φ:=fun _ : Fin s => K) j
  have below : reachable A ≤ test.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change Φ t A i - Φ t A j = 0
    exact sub_eq_zero.mpr ((P.label_eq_iff i j).mp same t)
  have h := below hv
  change v i - v j = 0 at h
  exact sub_eq_zero.mp h

private theorem separates (i j : Fin s) (different : P.label i ≠ P.label j) :
    ∃ v ∈ reachable A, v i ≠ v j := by
  by_contra absent
  apply different
  apply (P.label_eq_iff i j).mpr
  intro t
  by_contra ne
  exact absent ⟨Φ t A, tree_mem_reachable A t, ne⟩

/-- Reuse the reviewed finite coordinate algebra separator; it works
over finite fields and does not need a single generic separating vector. -/
theorem indicator_mem (a : Fin n) :
    labelSlice P.label (1 : Fin s → K) a ∈ reachable A := by
  have inside := labelSlice_mem_of_coordinate_separation
    (V:=reachable A) (lab:=P.label) (e:=(1 : Fin s → K))
    (fun _ hx _ hy => mul_mem_reachable hx hy) (one_mem_reachable A)
    (fun _ hv _ _ _ _ same => P.agree_of_mem hv same)
    (fun i j _ _ ne => P.separates i j ne) (P.rep a) (by simp)
  simpa only [P.label_rep] using inside

/-- The full tree span contains every class-constant coordinate vector. -/
theorem mem_reachable_iff (v : Fin s → K) :
    v ∈ reachable A ↔ ∀ i j, P.label i=P.label j → v i=v j := by
  constructor
  · intro hv i j same
    exact P.agree_of_mem hv same
  · intro agree
    let f : Fin s → K := ∑ a : Fin n, v (P.rep a) • labelSlice P.label (1 : Fin s → K) a
    have inside : f ∈ reachable A := by
      apply (reachable A).sum_mem
      intro a _
      exact (reachable A).smul_mem _ (P.indicator_mem a)
    have eq : f=v := by
      funext i
      simp only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, labelSlice_apply, Pi.one_apply]
      rw [Finset.sum_eq_single_of_mem (P.label i) (Finset.mem_univ _)]
      · simpa only [if_pos rfl, ite_true, mul_one] using agree _ _ (P.label_rep (P.label i))
      · intro a _ ne
        rw [if_neg ne.symm, mul_zero]
    rwa [eq] at inside

theorem sum_into_class_eq {i j : Fin s} (same : P.label i = P.label j) (a : Fin n) :
    (∑ l ∈ Finset.univ.filter (fun l => P.label l=a), A i l) =
      ∑ l ∈ Finset.univ.filter (fun l => P.label l=a), A j l := by
  have read (k : Fin s) : mat A (labelSlice P.label (1 : Fin s → K) a) k =
      ∑ l ∈ Finset.univ.filter (fun l => P.label l=a), A k l := by
    simp only [mat_apply, Matrix.mulVec_apply_eq_sum, labelSlice_apply, Pi.one_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_filter]
  have h := P.agree_of_mem (mat_mem_reachable (P.indicator_mem a)) same
  simpa only [read] using h

def aggregateMatrix : Matrix (Fin n) (Fin n) K :=
  causalMergeMatrix A P.rep P.label

theorem aggregateMatrix_value (i : Fin s) (a : Fin n) :
    P.aggregateMatrix (P.label i) a = ∑ l ∈ Finset.univ.filter (fun l => P.label l=a), A i l := by
  exact P.sum_into_class_eq (P.label_rep (P.label i)) a

def aggregateWeight (b : Fin s → K) (a : Fin n) : K :=
  ∑ i ∈ Finset.univ.filter (fun i => P.label i=a), b i

theorem Φ_aggregate (t : FiniteRootedTree) :
    Φ t P.aggregateMatrix = fun a => Φ t A (P.rep a) := by
  refine Φ_causalMerge (A:=A) (e:=P.rep) (r:=P.label) (q:=(t.order : ℕ)) ?_ t (by omega)
  intro v hv i
  exact P.agree_of_mem (treeSpace_le_reachable A _ hv) (P.label_rep (P.label i))

theorem Φ_pullback (t : FiniteRootedTree) (i : Fin s) :
    Φ t P.aggregateMatrix (P.label i) = Φ t A i := by
  rw [P.Φ_aggregate t]
  exact (P.label_eq_iff _ _).mp (P.label_rep (P.label i)) t

private theorem aggregate_weight_eval (b : Fin s → K) (v : Fin n → K) :
    P.aggregateWeight b ⬝ᵥ v = b ⬝ᵥ (fun i => v (P.label i)) := by
  simp only [aggregateWeight, dotProduct]
  rw [← Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ) (g:=P.label)
    (fun i _ => Finset.mem_univ _) (fun i => b i * v (P.label i))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (Finset.mem_filter.mp hi).2]

/-- Actual raw rooted outputs, not just a finite list of order conditions. -/
theorem scalar_output (b : Fin s → K) (t : FiniteRootedTree) :
    P.aggregateWeight b ⬝ᵥ Φ t P.aggregateMatrix = b ⬝ᵥ Φ t A := by
  rw [P.aggregate_weight_eval]
  exact congrArg (fun v : Fin s → K => b ⬝ᵥ v) (funext (P.Φ_pullback t))

theorem hasOrder_iff (b : Fin s → K) (p : ℕ) :
    HasOrder p P.aggregateMatrix (P.aggregateWeight b) ↔ HasOrder p A b := by
  constructor
  · intro h t ht
    simpa only [P.scalar_output b t] using h t ht
  · intro h t ht
    change (t.factorial : K) * (P.aggregateWeight b ⬝ᵥ Φ t P.aggregateMatrix) = 1
    rw [P.scalar_output b t]
    exact h t ht

end Partition
end
end RKResearch.CanonicalProfile
