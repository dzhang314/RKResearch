module

public import RKCert.ReviewedNative.NonsingularNodalPackets
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Fin.Embedding

@[expose] public section

/-! # Nonsingular triangular nodal cutoffs in both directions

An invariant coordinate cut pays the effective primal and dual rank in
opposite directions.  Any polynomial mask can be used.  For a finite
cover of the clocks the product of its distinct linear factors gives the
degree exactly, even when some weights are zero or cancel one another.
-/

namespace RKResearch.Certified.Graded
open Module Polynomial
open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] {s p k : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Restriction to the specified physical stages. -/
def cutRestrict (K : Type*) [Field K] (S : Finset (Fin s)) :
    (Fin s → K) →ₗ[K] (S → K) :=
  LinearMap.pi (fun i : S => LinearMap.proj i.val)

/-- Vectors supported on the complement of S. -/
def cutZeroSpace (K : Type*) [Field K] (S : Finset (Fin s)) : Submodule K (Fin s → K) :=
  (cutRestrict K S).ker

theorem mem_cutZeroSpace (S : Finset (Fin s)) (v : Fin s → K) :
    v ∈ cutZeroSpace K S ↔ ∀ i ∈ S, v i = 0 := by
  change cutRestrict K S v = 0 ↔ _
  constructor
  · intro h i hi
    exact congrFun h (⟨i,hi⟩ : S)
  · intro h
    funext i
    exact h i.val i.property

theorem cutRestrict_surjective (K : Type*) [Field K] (S : Finset (Fin s)) :
    Function.Surjective (cutRestrict K S) := by
  intro w
  refine ⟨fun i => if hi : i ∈ S then w ⟨i,hi⟩ else 0,?_⟩
  funext i
  change (if hi : i.val ∈ S then w ⟨i.val,hi⟩ else 0) = w i
  rw [dif_pos i.property]

theorem finrank_cutZeroSpace (K : Type*) [Field K] (S : Finset (Fin s)) :
    finrank K (cutZeroSpace K S) = s-S.card := by
  have h := (cutRestrict K S).finrank_range_add_finrank_ker
  have hr : finrank K (cutRestrict K S).range = S.card := by
    rw [LinearMap.range_eq_top.mpr (cutRestrict_surjective K S),finrank_top,
      Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
  rw [hr,Module.finrank_fin_fun] at h
  change S.card + finrank K (cutZeroSpace K S) = s at h
  omega

theorem finrank_cutZeroSpace_annihilator (K : Type*) [Field K] (S : Finset (Fin s)) :
    finrank K (cutZeroSpace K S).dualAnnihilator = S.card := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (cutZeroSpace K S)
  have hs : S.card ≤ s := by
    simpa only [Fintype.card_fin] using S.card_le_univ
  rw [finrank_cutZeroSpace,Module.finrank_fin_fun] at h
  omega

/-- A chronology cut is invariant: every earlier stage of a row in S is
also in S, so the clocks and the lower triangular tableau preserve its
complementary coordinate support. -/
theorem cutZeroSpace_volterra_le (ha : A.IsLowerTriangular) (S : Finset (Fin s))
    (hS : ∀ i ∈ S, ∀ j ≤ i, j ∈ S) :
    (cutZeroSpace K S).map (volterra A) ≤ cutZeroSpace K S := by
  let W := cutZeroSpace K S
  have hdiag (v : Fin s → K) (hv : v ∈ W) : diag (nodes A) v ∈ W := by
    apply (mem_cutZeroSpace S _).mpr
    intro i hi
    rw [diag_apply,(mem_cutZeroSpace S _).mp hv i hi,mul_zero]
  have hmat (v : Fin s → K) (hv : v ∈ W) : mat A v ∈ W := by
    apply (mem_cutZeroSpace S _).mpr
    intro i hi
    rw [mat_apply]
    change (∑ j, A i j * v j) = 0
    apply Finset.sum_eq_zero
    intro j _
    rcases le_or_gt j i with hj | hj
    · rw [(mem_cutZeroSpace S _).mp hv j (hS i hi j hj),mul_zero]
    · rw [@ha i j hj,zero_mul]
  rintro _ ⟨v,hv,rfl⟩
  change diag (nodes A) (mat A v) - mat A (diag (nodes A) v) - mat A (mat A v) ∈ W
  exact W.sub_mem (W.sub_mem (hdiag _ (hmat _ hv)) (hmat _ (hdiag _ hv))) (hmat _ (hmat _ hv))

/-- Primal cutoff for an arbitrary invariant coordinate complement.  No
triangularity is needed beyond the two explicitly stated Volterra facts. -/
theorem nodalColumn_cut_of_coordinate (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (S : Finset (Fin s))
    (hS : (cutZeroSpace K S).map (volterra A) ≤ cutZeroSpace K S)
    (P : K[X]) (hP : P ≠ 0) (hp : 2*P.natDegree < p)
    (hzero : ∀ i ∈ S, P.eval (nodes A i) = 0) :
    nonsingularStageFloor (p-2*P.natDegree) ≤ s-S.card := by
  rw [← finrank_cutZeroSpace K S]
  apply nodalColumn_cut_subspace ho hR P hP hp _ hS
  intro Q
  apply (mem_cutZeroSpace S _).mpr
  intro i hi
  simp only [nodalColumn_apply,Polynomial.eval_mul,hzero i hi,zero_mul]

/-- Dual cutoff for the same invariant coordinate complement.  Only
the active individual output weights outside S need to have their
clock killed by P; zero weights require no division or guard. -/
theorem nodalRow_cut_of_coordinate (ho : RKResearch.HasOrder p A b)
    (hR : Function.Injective (volterra A)) (S : Finset (Fin s))
    (hS : (cutZeroSpace K S).map (volterra A) ≤ cutZeroSpace K S)
    (P : K[X]) (hP : P ≠ 0) (hp : 2*P.natDegree < p)
    (hzero : ∀ i ∉ S, b i ≠ 0 → P.eval (nodes A i) = 0) :
    nonsingularStageFloor (p-2*P.natDegree) ≤ S.card := by
  rw [← finrank_cutZeroSpace_annihilator K S]
  apply nodalRow_cut_subspace ho hR P hP hp _ hS
  intro Q
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro v hv
  rw [nodalRow_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ S
  · rw [(mem_cutZeroSpace S _).mp hv i hi,mul_zero]
  · by_cases hb : b i = 0
    · simp only [hb,zero_mul]
    · simp only [Polynomial.eval_mul,hzero i hi hb,zero_mul,mul_zero]

/-- The monic polynomial with the given distinct field elements as nodes. -/
def cutNodalPolynomial (U : Finset K) : K[X] :=
  ∏ x ∈ U, (X - C x)

theorem cutNodalPolynomial_ne_zero (U : Finset K) : cutNodalPolynomial U ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun x _ => Polynomial.X_sub_C_ne_zero x)

@[simp]
theorem natDegree_cutNodalPolynomial (U : Finset K) :
    (cutNodalPolynomial U).natDegree = U.card := by
  unfold cutNodalPolynomial
  rw [Polynomial.natDegree_prod U (fun x : K => (X - C x : K[X])) (fun x _ => X_sub_C_ne_zero x)]
  simp only [natDegree_X_sub_C,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]

theorem cutNodalPolynomial_eval_zero {U : Finset K} {x : K} (hx : x ∈ U) :
    (cutNodalPolynomial U).eval x = 0 := by
  unfold cutNodalPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero hx
  simp

/-- A downward closed head with clocks covered by U must leave enough
later stages to carry the real masked primal packet. -/
theorem nonsingular_head_clock_cut (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0)
    (S : Finset (Fin s)) (hS : ∀ i ∈ S, ∀ j ≤ i, j ∈ S)
    (U : Finset K) (hp : 2*U.card < p) (cover : ∀ i ∈ S, nodes A i ∈ U) :
    nonsingularStageFloor (p-2*U.card) ≤ s-S.card := by
  let P := cutNodalPolynomial U
  have hd : P.natDegree = U.card := natDegree_cutNodalPolynomial U
  rw [← hd] at hp ⊢
  exact nodalColumn_cut_of_coordinate ho (volterra_injective ha hn) S
    (cutZeroSpace_volterra_le ha S hS) P (cutNodalPolynomial_ne_zero U) hp
    (fun i hi => cutNodalPolynomial_eval_zero (cover i hi))

/-- If the *active* clocks after a downward closed head are covered by
U, enough earlier physical stages must carry the actual masked rows. -/
theorem nonsingular_tail_active_clock_cut (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0)
    (S : Finset (Fin s)) (hS : ∀ i ∈ S, ∀ j ≤ i, j ∈ S)
    (U : Finset K) (hp : 2*U.card < p)
    (cover : ∀ i ∉ S, b i ≠ 0 → nodes A i ∈ U) :
    nonsingularStageFloor (p-2*U.card) ≤ S.card := by
  let P := cutNodalPolynomial U
  have hd : P.natDegree = U.card := natDegree_cutNodalPolynomial U
  rw [← hd] at hp ⊢
  exact nodalRow_cut_of_coordinate ho (volterra_injective ha hn) S
    (cutZeroSpace_volterra_le ha S hS) P (cutNodalPolynomial_ne_zero U) hp
    (fun i hi hb => cutNodalPolynomial_eval_zero (cover i hi hb))

/-- The first k positions of a tableau with s stages. -/
def chronologicalHead (hk : k ≤ s) : Finset (Fin s) :=
  (Finset.univ : Finset (Fin k)).map (Fin.castLEEmb hk)

@[simp]
theorem chronologicalHead_card (hk : k ≤ s) : (chronologicalHead hk).card = k := by
  rw [chronologicalHead,Finset.card_map,Finset.card_univ,Fintype.card_fin]

theorem mem_chronologicalHead (hk : k ≤ s) (i : Fin s) :
    i ∈ chronologicalHead hk ↔ i.val < k := by
  rw [chronologicalHead,Finset.mem_map]
  constructor
  · rintro ⟨j,_,rfl⟩
    exact j.isLt
  · intro hi
    refine ⟨⟨i.val,hi⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    rfl

theorem chronologicalHead_downward (hk : k ≤ s) :
    ∀ i ∈ chronologicalHead hk, ∀ j ≤ i, j ∈ chronologicalHead hk := by
  intro i hi j hj
  change j.val ≤ i.val at hj
  exact (mem_chronologicalHead hk j).mpr (lt_of_le_of_lt hj ((mem_chronologicalHead hk i).mp hi))

/-- Actual distinct physical clocks in the chronological prefix. -/
def headPhysicalClocks (A : Matrix (Fin s) (Fin s) K) (hk : k ≤ s) : Finset K := by
  classical
  exact (chronologicalHead hk).image (nodes A)

/-- Actual distinct clocks with a live individual output in the
chronological suffix. They are not grouped by their total weight. -/
def tailActiveClocks (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (hk : k ≤ s) : Finset K := by
  classical
  exact ((Finset.univ \ chronologicalHead hk).filter (fun i => b i ≠ 0)).image (nodes A)

/-- The two directional all-order cutoffs on the same chronological
split. Either conclusion can be used without the other one's budget
being positive. -/
theorem nonsingular_chronological_clock_cut (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) (hk : k ≤ s) :
    (2*(headPhysicalClocks A hk).card < p →
      nonsingularStageFloor (p-2*(headPhysicalClocks A hk).card) ≤ s-k) ∧
    (2*(tailActiveClocks A b hk).card < p →
      nonsingularStageFloor (p-2*(tailActiveClocks A b hk).card) ≤ k) := by
  classical
  let S := chronologicalHead hk
  constructor
  · intro hp
    have h := nonsingular_head_clock_cut ho ha hn S (chronologicalHead_downward hk)
      (headPhysicalClocks A hk) hp (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    simpa only [S,chronologicalHead_card] using h
  · intro hp
    have hcover (i : Fin s) (hi : i ∉ S) (hb : b i ≠ 0) :
        nodes A i ∈ tailActiveClocks A b hk := by
      exact Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hi⟩,hb⟩,rfl⟩
    have h := nonsingular_tail_active_clock_cut ho ha hn S (chronologicalHead_downward hk)
      (tailActiveClocks A b hk) hp hcover
    simpa only [S,chronologicalHead_card] using h

end
end RKResearch.Certified.Graded
