module

public import RKCert.ReviewedNative.CanonicalVisiblePrune
public import RKCert.ReviewedNative.GradedProducts
import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-! Source-only candidate. The span of paired literal stage columns is
the comparison object. No free commutative tree syntax is introduced. -/
namespace RKResearch.CanonicalUniqueness

open RKResearch FiniteRootedTree RKResearch.Certified.Graded
open RKResearch.Certified.Graded.Reverse RKResearch.CanonicalVisibility
open scoped Classical Matrix FiniteRootedTree BigOperators

noncomputable section
variable {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]

/-- Literal one-hole words with multipliers that are individual reviewed trees. -/
inductive TreeWord where
  | empty
  | through : TreeWord → TreeWord
  | multiply : FiniteRootedTree → TreeWord → TreeWord

def TreeWord.insert : TreeWord → FiniteRootedTree → FiniteRootedTree
  | .empty, t => t
  | .through C, t => C.insert (.leaf ◂ t)
  | .multiply u C, t => C.insert (u # t)

def TreeWord.context (A : Matrix ι ι K) : TreeWord → Context ι K
  | .empty => .empty
  | .through C => .through (TreeWord.context A C)
  | .multiply u C => .multiply (Φ u A) (TreeWord.context A C)

theorem TreeWord.eval_tree (A : Matrix ι ι K) (C : TreeWord) (t : FiniteRootedTree) :
    (C.context A).eval A (Φ t A) = Φ (C.insert t) A := by
  induction C generalizing t with
  | empty => rfl
  | through C ih =>
    change (C.context A).eval A (mat A (Φ t A)) = Φ (C.insert (.leaf ◂ t)) A
    have h : mat A (Φ t A) = Φ (.leaf ◂ t) A := by simp only [mat_apply, Φ, one_mul]
    rw [h]
    exact ih _
  | multiply u C ih =>
    change (C.context A).eval A (Φ u A * Φ t A) = Φ (C.insert (u # t)) A
    rw [← Φ_rootedSum]
    exact ih _

def treeSpan (A : Matrix ι ι K) : Submodule K (ι → K) :=
  Submodule.span K (Set.range fun t : FiniteRootedTree => Φ t A)

variable (A : Matrix ι ι K) (B : Matrix κ κ K)
variable (b : ι → K) (d : κ → K)

theorem same_treeWord (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (C : TreeWord) (t : FiniteRootedTree) :
    row b ((C.context A).eval A (Φ t A)) = row d ((C.context B).eval B (Φ t B)) := by
  simpa only [TreeWord.eval_tree, row_apply] using same (C.insert t)

def pairedSpan : Submodule K ((ι → K) × (κ → K)) :=
  Submodule.span K (Set.range fun t : FiniteRootedTree => (Φ t A, Φ t B))

private theorem pair_tree (t : FiniteRootedTree) : (Φ t A, Φ t B) ∈ pairedSpan A B :=
  Submodule.subset_span ⟨t, rfl⟩

private theorem pair_act {x : ι → K} {y : κ → K} (h : (x,y) ∈ pairedSpan A B) :
    (mat A x, mat B y) ∈ pairedSpan A B := by
  let L := (mat A).prodMap (mat B)
  have closed : pairedSpan A B ≤ (pairedSpan A B).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change (mat A (Φ t A), mat B (Φ t B)) ∈ pairedSpan A B
    simpa only [Φ, one_mul, mat_apply] using pair_tree A B (.leaf ◂ t)
  exact closed h

private theorem pair_mul {x u : ι → K} {y v : κ → K}
    (h : (x,y) ∈ pairedSpan A B) (g : (u,v) ∈ pairedSpan A B) :
    (x*u,y*v) ∈ pairedSpan A B := by
  change (x,y)*(u,v) ∈ pairedSpan A B
  rw [← LinearMap.mul_apply' (R:=K)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _
    (LinearMap.mul K ((ι → K) × (κ → K))) _ _ _ h g
  rintro _ ⟨t, rfl⟩ _ ⟨q, rfl⟩
  rw [LinearMap.mul_apply' (R:=K)]
  change (Φ t A * Φ q A, Φ t B * Φ q B) ∈ pairedSpan A B
  simpa only [Φ_rootedSum] using pair_tree A B (t # q)

private theorem pair_onto_left (full : treeSpan A = ⊤) (x : ι → K) :
    ∃ y, (x,y) ∈ pairedSpan A B := by
  let fst := LinearMap.fst K (ι → K) (κ → K)
  have cover : treeSpan A ≤ (pairedSpan A B).map fst := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact Submodule.mem_map_of_mem (pair_tree A B t)
  have hx : x ∈ treeSpan A := by rw [full]; trivial
  obtain ⟨⟨u,v⟩, hu, rfl⟩ := Submodule.mem_map.mp (cover hx)
  exact ⟨v, hu⟩

private theorem pair_onto_right (full : treeSpan B = ⊤) (y : κ → K) :
    ∃ x, (x,y) ∈ pairedSpan A B := by
  let snd := LinearMap.snd K (ι → K) (κ → K)
  have cover : treeSpan B ≤ (pairedSpan A B).map snd := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact Submodule.mem_map_of_mem (pair_tree A B t)
  have hy : y ∈ treeSpan B := by rw [full]; trivial
  obtain ⟨⟨u,v⟩, hu, rfl⟩ := Submodule.mem_map.mp (cover hy)
  exact ⟨u, hu⟩

theorem pair_readout (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    {x : ι → K} {y : κ → K} (h : (x,y) ∈ pairedSpan A B) : row b x = row d y := by
  let L := (row b).comp (LinearMap.fst K (ι → K) (κ → K)) -
    (row d).comp (LinearMap.snd K (ι → K) (κ → K))
  have closed : pairedSpan A B ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change row b (Φ t A) - row d (Φ t B) = 0
    exact sub_eq_zero.mpr (same t)
  have hz := closed h
  change row b x - row d y = 0 at hz
  exact sub_eq_zero.mp hz

/-- A multiplier on the left can be matched on the right using any
simultaneous linear combination of literal tree columns lifting it. -/
private theorem pair_context_left (full : treeSpan A = ⊤) (C : Context ι K) :
    ∃ D : Context κ K, ∀ x y, (x,y) ∈ pairedSpan A B →
      (C.eval A x,D.eval B y) ∈ pairedSpan A B := by
  induction C with
  | empty => exact ⟨.empty, fun _ _ h => h⟩
  | through C ih =>
    obtain ⟨D, moves⟩ := ih
    exact ⟨.through D, fun x y h => moves (mat A x) (mat B y) (pair_act A B h)⟩
  | multiply u C ih =>
    obtain ⟨D, moves⟩ := ih
    obtain ⟨v, uv⟩ := pair_onto_left A B full u
    exact ⟨.multiply v D, fun x y h => moves (u*x) (v*y) (pair_mul A B uv h)⟩

private theorem pair_context_right (full : treeSpan B = ⊤) (C : Context κ K) :
    ∃ D : Context ι K, ∀ x y, (x,y) ∈ pairedSpan A B →
      (D.eval A x,C.eval B y) ∈ pairedSpan A B := by
  induction C with
  | empty => exact ⟨.empty, fun _ _ h => h⟩
  | through C ih =>
    obtain ⟨D, moves⟩ := ih
    exact ⟨.through D, fun x y h => moves (mat A x) (mat B y) (pair_act A B h)⟩
  | multiply v C ih =>
    obtain ⟨D, moves⟩ := ih
    obtain ⟨u, uv⟩ := pair_onto_right A B full v
    exact ⟨.multiply u D, fun x y h => moves (u*x) (v*y) (pair_mul A B uv h)⟩

private theorem left_eq_zero (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (full : treeSpan A = ⊤) (obs : invisible A b = ⊥)
    {x : ι → K} (h : (x,(0 : κ → K)) ∈ pairedSpan A B) : x = 0 := by
  have hx : x ∈ invisible A b := by
    apply (mem_invisible A b).mpr
    intro C
    obtain ⟨D, moves⟩ := pair_context_left A B full C
    simpa only [map_zero] using pair_readout A B b d same (moves _ _ h)
  rw [obs] at hx
  exact (Submodule.mem_bot K).mp hx

private theorem right_eq_zero (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (full : treeSpan B = ⊤) (obs : invisible B d = ⊥)
    {y : κ → K} (h : ((0 : ι → K),y) ∈ pairedSpan A B) : y = 0 := by
  have hy : y ∈ invisible B d := by
    apply (mem_invisible B d).mpr
    intro C
    obtain ⟨D, moves⟩ := pair_context_right A B full C
    simpa only [map_zero] using (pair_readout A B b d same (moves _ _ h)).symm
  rw [obs] at hy
  exact (Submodule.mem_bot K).mp hy

private theorem unique_right (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (full : treeSpan B = ⊤) (obs : invisible B d = ⊥)
    {x : ι → K} {y z : κ → K} (h : (x,y) ∈ pairedSpan A B)
    (g : (x,z) ∈ pairedSpan A B) : y=z := by
  have p := (pairedSpan A B).sub_mem h g
  change (x-x,y-z) ∈ pairedSpan A B at p
  rw [sub_self] at p
  exact sub_eq_zero.mp (right_eq_zero A B b d same full obs p)

private theorem coordinate_same (i : ι) : coordinate (K:=K) i i = 1 := by
  classical
  simp [coordinate]

private theorem coordinate_off {i j : ι} (ne : j≠i) : coordinate (K:=K) i j = 0 := by
  classical
  simp [coordinate, Pi.single_eq_of_ne ne]

private theorem coordinate_gate (i : ι) (v : ι → K) :
    coordinate (K:=K) i*v = v i • coordinate i := by
  funext j
  by_cases h : j=i
  · subst j
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, coordinate_same, one_mul, mul_one]
  · simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, coordinate_off h, zero_mul, mul_zero]

private theorem sum_coordinate : (∑ i : ι, coordinate (K:=K) i) = 1 := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · exact coordinate_same j
  · intro i _ ne
    exact coordinate_off ne.symm

private theorem mat_coordinate (M : Matrix ι ι K) (i j : ι) :
    mat M (coordinate (K:=K) j) i = M i j := by
  classical
  rw [mat_apply, coordinate, Matrix.mulVec_single_one, Matrix.col_apply]

/-- Two fully reachable, split-observable tableaux for the same literal
rooted series differ by a stage permutation. -/
theorem permutation_of_same_series
    (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (fullA : treeSpan A = ⊤) (fullB : treeSpan B = ⊤)
    (obsA : invisible A b = ⊥) (obsB : invisible B d = ⊥) :
    ∃ e : κ ≃ ι, (∀ j k, B j k = A (e j) (e k)) ∧ ∀ j, d j = b (e j) := by
  choose f pairs using fun i : ι => pair_onto_left A B fullA (coordinate (K:=K) i)
  have allSum : (∑ i, f i) = (1 : κ → K) := by
    have inside : (∑ i : ι, (coordinate (K:=K) i,f i)) ∈ pairedSpan A B := by
      apply (pairedSpan A B).sum_mem
      intro i _
      exact pairs i
    have sumPair : (∑ i, (coordinate (K:=K) i, f i)) = ((1 : ι → K),∑ i, f i) := by
      apply Prod.ext
      · change (LinearMap.fst K (ι → K) (κ → K)) (∑ i, (coordinate (K:=K) i, f i)) = _
        rw [map_sum]
        exact sum_coordinate
      · change (LinearMap.snd K (ι → K) (κ → K)) (∑ i, (coordinate (K:=K) i, f i)) = _
        simp only [map_sum, LinearMap.snd_apply]
    rw [sumPair] at inside
    exact unique_right A B b d same fullB obsB inside (pair_tree A B .leaf)
  have atLeast (j : κ) : ∃ i, f i j ≠ 0 := by
    by_contra absent
    have off (i : ι) : f i j = 0 := by
      by_contra nz
      exact absent ⟨i,nz⟩
    exact zero_ne_one (by simpa only [Finset.sum_apply, Pi.one_apply, off,
      Finset.sum_const_zero] using congrFun allSum j)
  choose g picked using atLeast
  have coord {x : ι → K} {y : κ → K} (h : (x,y) ∈ pairedSpan A B) (j : κ) :
      y j = x (g j) := by
    have p := pair_mul A B (pairs (g j)) h
    rw [coordinate_gate] at p
    have q := (pairedSpan A B).smul_mem (x (g j)) (pairs (g j))
    change (x (g j) • coordinate (g j),x (g j) • f (g j)) ∈ pairedSpan A B at q
    have eq := congrFun (unique_right A B b d same fullB obsB p q) j
    change f (g j) j * y j = x (g j) * f (g j) j at eq
    exact mul_left_cancel₀ (picked j) (eq.trans (mul_comm _ _))
  have inj : Function.Injective g := by
    intro j k hk
    by_contra ne
    obtain ⟨x,hx⟩ := pair_onto_right A B fullB (coordinate (K:=K) j)
    have l := coord hx j
    have r := coord hx k
    rw [coordinate_same] at l
    rw [coordinate_off (fun h : k = j => ne h.symm), ←hk] at r
    exact one_ne_zero (l.trans r.symm)
  have onto : Function.Surjective g := by
    intro i
    by_contra absent
    have z : f i = 0 := by
      funext j
      exact (coord (pairs i) j).trans (coordinate_off (fun eq => absent ⟨j,eq⟩))
    have p := pairs i
    rw [z] at p
    have zero := left_eq_zero A B b d same fullA obsA p
    exact one_ne_zero (by simpa only [coordinate_same, Pi.zero_apply] using congrFun zero i)
  let e : κ ≃ ι := Equiv.ofBijective g ⟨inj,onto⟩
  have pairedIndicator (j : κ) : (coordinate (K:=K) (e j),coordinate (K:=K) j) ∈ pairedSpan A B := by
    have eq : f (e j) = coordinate (K:=K) j := by
      funext k
      have atK : f (e j) k = coordinate (K:=K) (e j) (e k) := coord (pairs (e j)) k
      rw [atK]
      by_cases same : k=j
      · subst k
        simp only [coordinate_same]
      · rw [coordinate_off (fun hit => same (e.injective hit)), coordinate_off same]
    rw [←eq]
    exact pairs (e j)
  refine ⟨e, ?_, ?_⟩
  · intro j k
    have act := coord (pair_act A B (pairedIndicator k)) j
    have eg : e j = g j := rfl
    rw [eg]
    simpa only [mat_coordinate] using act
  · intro j
    simpa only [row_coordinate] using (pair_readout A B b d same (pairedIndicator j)).symm

end
end RKResearch.CanonicalUniqueness
