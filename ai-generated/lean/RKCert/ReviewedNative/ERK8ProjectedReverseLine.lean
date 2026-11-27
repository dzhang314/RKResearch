module

public import RKCert.ReviewedNative.ERKUniform
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option

@[expose] public section

/-! Chronological line elimination and low-dimensional clock projection for
strict explicit order problems. No assumption of distinct physical clocks
is used outside the projected predecessor sites. -/
namespace RKResearch.Certified.Graded.Reverse

open Module
open scoped Matrix BigOperators
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] {s p : Nat}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- If the first reverse seed is zero, the second cannot be an invariant
one-dimensional line with zero transpose image in a paid strict method. -/
theorem no_stationary_second_seed
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (hp : 4 ≤ p)
    (h₀ : firstSeed A b = 0)
    (hA : mat A.transpose (quadraticSeed A b) = 0)
    (hC : diag (reflectedClock A) (quadraticSeed A b) ∈ K ∙ quadraticSeed A b) :
    False := by
  let q := quadraticSeed A b
  have one : back A b 1 = K ∙ q := by
    change (K ∙ firstSeed A b) ⊔ (K ∙ firstSeed A b).map (mat A.transpose) ⊔
      (K ∙ firstSeed A b).map (diag (reflectedClock A)) ⊔ (K ∙ q) = K ∙ q
    simp [h₀]
  have two : back A b 2 ≤ K ∙ q := by
    change back A b 1 ⊔ (back A b 1).map (mat A.transpose) ⊔
      (back A b 1).map (diag (reflectedClock A)) ⊔ (K ∙ q) ≤ K ∙ q
    rw [one]
    refine sup_le (sup_le (sup_le le_rfl ?_) ?_) le_rfl
    · apply Submodule.map_le_iff_le_comap.mpr
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      change mat A.transpose (quadraticSeed A b) ∈ K ∙ q
      rw [hA]
      exact (K ∙ q).zero_mem
    · exact Submodule.map_le_iff_le_comap.mpr
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hC)
  have hhi := Submodule.finrank_mono two
  have hlo := back_finrank ha ho 2 hp
  have hline : finrank K (K ∙ q) ≤ 1 := by
    by_cases hz : q = 0
    · rw [hz, Submodule.span_zero_singleton, finrank_bot]; decide
    · rw [finrank_span_singleton hz]
  omega

/-- The transpose of a strict tableau cannot send a row weight beyond
the last physical row where that weight is nonzero. At that last row,
its image is zero as well. -/
theorem strict_transpose_zero_of_tail {w : Fin s → K} {j : Fin s}
    (ha : ∀ i k, i ≤ k → A i k = 0) (hw : ∀ i, j < i → w i = 0) :
    ∀ k, j ≤ k → mat A.transpose w k = 0 := by
  intro k hk
  rw [mat_apply, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : j < i
  · rw [hw i hi, mul_zero]
  · rw [Matrix.transpose_apply, ha i k ((le_of_not_gt hi).trans hk), zero_mul]

/-- If the latest source lies at a nonzero coordinate of the destination
line, chronology kills the entire destination restriction, not just one
of its coordinates. -/
theorem strict_transpose_line_zero_at_tail {w l : Fin s → K} {j : Fin s}
    (ha : ∀ i k, i ≤ k → A i k = 0) (hw : ∀ i, j < i → w i = 0)
    (S : Finset (Fin s)) (hS : j ∈ S) (hj : l j ≠ 0)
    (β : K) (line : ∀ k ∈ S, mat A.transpose w k = β * l k) :
    ∀ k ∈ S, mat A.transpose w k = 0 := by
  have hz : β * l j = 0 := (line j hS).symm.trans (strict_transpose_zero_of_tail ha hw j le_rfl)
  have hb : β = 0 := (mul_eq_zero.mp hz).resolve_right hj
  intro k hk
  rw [line k hk, hb, zero_mul]

/-- Transposed Vandermonde uniqueness for any finite indexed set
of distinct clock sites. This also applies when a single aggregate
site is represented by an extra Option index. -/
theorem vanishing_moments_zero {ι : Type*} [Fintype ι] {c m : ι → K}
    (hc : Function.Injective c)
    (hm : ∀ k < Fintype.card ι, (∑ i, m i * c i ^ k) = 0) : m = 0 := by
  classical
  funext i
  let E : Finset ι := Finset.univ.erase i
  let F : Polynomial K := ∏ j ∈ E, (Polynomial.X - Polynomial.C (c j))
  have leD : F.natDegree ≤ E.card := by
    calc
      _ ≤ ∑ j ∈ E, (Polynomial.X - Polynomial.C (c j)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ = _ := by simp
  have card : E.card = Fintype.card ι - 1 := Finset.card_erase_of_mem (Finset.mem_univ i)
  have pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have ltD : F.natDegree < Fintype.card ι := by omega
  have hsum : (∑ j, m j * F.eval (c j)) = 0 := by
    simp_rw [Polynomial.eval_eq_sum_range' ltD, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    have eq : (∑ j, m j * (F.coeff k * c j ^ k)) =
        F.coeff k * (∑ j, m j * c j ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [eq, hm k (Finset.mem_range.mp hk), mul_zero]
  have ev (j : ι) : F.eval (c j) = ∏ k ∈ E, (c j - c k) := by
    simp [F, Polynomial.eval_prod]
  have off (j : ι) (hj : j ≠ i) : F.eval (c j) = 0 := by
    rw [ev]
    have hjE : j ∈ E := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
    exact Finset.prod_eq_zero hjE (sub_self (c j))
  have on : F.eval (c i) ≠ 0 := by
    rw [ev]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hc h).symm)
  rw [Finset.sum_eq_single i] at hsum
  · exact (mul_eq_zero.mp hsum).resolve_right on
  · intro j hj hne
    rw [off j hne, mul_zero]
  · simp

/-- At a paid degree bound, physical taps supported only on a distinct
prefix of that length must be zero. -/
theorem projected_prefix_zero {c r : Fin s → K} (P : Finset (Fin s)) (q : Nat)
    (hcard : P.card ≤ q) (hc : Set.InjOn c P)
    (hs : ∀ i ∉ P, r i = 0)
    (hm : ∀ k < q, (∑ i, r i * c i ^ k) = 0) : r = 0 := by
  classical
  have e : (fun i : P => r i) = 0 := by
    apply vanishing_moments_zero (c := fun i : P => c i)
    · intro i j eq
      exact Subtype.ext (hc i.property j.property eq)
    · intro k hk
      rw [Fintype.card_coe] at hk
      have qsum : (∑ i ∈ P, r i * c i ^ k) = ∑ i, r i * c i ^ k :=
        Finset.sum_subset (Finset.subset_univ P) (fun i _ hi => by rw [hs i hi, zero_mul])
      rw [Finset.sum_coe_sort P (fun i : Fin s => r i * c i ^ k), qsum,
        hm k (hk.trans_le hcard)]
  funext i
  by_cases hi : i∈P
  · exact congrFun e ⟨i,hi⟩
  · exact hs i hi

/-- A single additional aggregate site is treated as one more column,
not as any number of physical copies at that clock. -/
theorem vanishing_moments_zero_with_site {ι : Type*} [Fintype ι] {c r : ι → K}
    (hc : Function.Injective c) (f a : K) (hf : ∀ i, c i ≠ f)
    (hm : ∀ k < Fintype.card ι + 1, (∑ i, r i * c i ^ k) + a * f ^ k = 0) :
    r = 0 ∧ a = 0 := by
  let V : Option ι → K := fun o => o.elim f c
  let W : Option ι → K := fun o => o.elim a r
  have inj : Function.Injective V := by
    intro i j q
    cases i <;> cases j
    · rfl
    · exact (hf _ q.symm).elim
    · exact (hf _ q).elim
    · exact congrArg some (hc q)
  have h : W = 0 := by
    apply vanishing_moments_zero (c := V) inj
    intro k hk
    rw [Fintype.card_option] at hk
    rw [univ_option, Finset.sum_insertNone]
    exact (add_comm _ _).trans (hm k hk)
  exact ⟨funext (fun i => congrFun h (some i)), congrFun h none⟩

/-- At most one extra predecessor clock may be carried by a line of
several physical coordinates, provided its aggregate mass is nonzero
and its clock is outside the distinct physical predecessor sites. -/
theorem projected_prefix_with_line_zero {c r l : Fin s → K}
    (P S : Finset (Fin s)) (q : Nat) (f β : K)
    (hcard : P.card + 1 ≤ q) (hdisj : Disjoint P S) (hc : Set.InjOn c P)
    (hf : ∀ i ∈ P, c i ≠ f) (hmass : (∑ i ∈ S, l i) ≠ 0)
    (hmono : ∀ i ∈ S, c i ≠ f → l i = 0)
    (hline : ∀ i ∈ S, r i = β * l i)
    (hs : ∀ i ∉ P, i ∉ S → r i = 0)
    (hm : ∀ k < q, (∑ i, r i * c i ^ k) = 0) : r = 0 := by
  classical
  have e := vanishing_moments_zero_with_site (c := fun i : P => c i)
    (r := fun i : P => r i) (fun i j eq => Subtype.ext (hc i.property j.property eq))
    f (β * ∑ i ∈ S, l i) (fun i => hf i i.property) ?_
  · have hβ : β = 0 := (mul_eq_zero.mp e.2).resolve_right hmass
    funext i
    by_cases hi : i∈P
    · exact congrFun e.1 ⟨i,hi⟩
    · by_cases hS : i∈S
      · rw [hline i hS, hβ, zero_mul, Pi.zero_apply]
      · exact hs i hi hS
  · intro k hk
    rw [Fintype.card_coe] at hk
    have sumS : (∑ i∈S, r i * c i ^ k) = (β * ∑ i ∈ S, l i) * f ^ k := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hline i hi]
      by_cases eq : c i = f
      · rw [eq]
      · rw [hmono i hi eq, mul_zero, zero_mul, zero_mul]
    have hsum : (∑ i ∈ P ∪ S, r i * c i ^ k) = ∑ i, r i * c i ^ k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hnot : i ∉ P ∧ i ∉ S := by simpa using hi
      rw [hs i hnot.1 hnot.2, zero_mul]
    rw [Finset.sum_union hdisj, sumS, hm k (hk.trans_le hcard)] at hsum
    rwa [Finset.sum_coe_sort P (fun i : Fin s => r i * c i ^ k)]

end RKResearch.Certified.Graded.Reverse

#print axioms RKResearch.Certified.Graded.Reverse.no_stationary_second_seed
#print axioms RKResearch.Certified.Graded.Reverse.strict_transpose_line_zero_at_tail
#print axioms RKResearch.Certified.Graded.Reverse.projected_prefix_zero

#print axioms RKResearch.Certified.Graded.Reverse.projected_prefix_with_line_zero
