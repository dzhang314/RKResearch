module

public import RKCert.ReviewedNative.DIRKOrderElevenThirteenCubicRank
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Genuine first clean reverse read with a one-clock core.
The weighted rank/support result feeding the row cut is stated explicitly. -/
namespace RKResearch.Certified.Graded.OrderElevenLocalCore

open RKResearch Reverse
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private def read (A : Matrix (Fin s) (Fin s) K) (v : Fin s → K) (i : Fin s) : K :=
  ∑ j, A j i*v j

private theorem read_eq (v : Fin s → K) (i : Fin s) :
    read A v i = mat A.transpose v i := by
  simp only [read,mat_apply,Matrix.mulVec_apply_eq_sum,Matrix.transpose_apply]

private theorem one_clock_literal_cut (ha : A.IsLowerTriangular)
    (d2 : reflectedStageRow A b 1=0) (u : Fin s) (V : K) (hV : V≠0)
    (hu : b u≠0) (hy : reflectedClock A u≠0)
    (tail : ∀ j, u < j → b j=0 ∨ reflectedClock A j=0 ∨ reflectedClock A j=V)
    (gz : reflectedStageRow A b 2 u=0)
    (rgz : mat A.transpose (reflectedStageRow A b 2) u=0) : False := by
  classical
  let y := reflectedClock A
  let W := reflectedStageWeight A b
  let G := reflectedStageRow A b 2
  have two (i : Fin s) : (2:K)*read A (W 1) i = W 2 i := by
    rw [read_eq]
    have h := congrFun d2 i
    simpa only [reflectedStageRow,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      Pi.zero_apply,mat_apply,Nat.reduceAdd,Nat.cast_ofNat,sub_eq_zero,W] using h
  have three (i : Fin s) : G i=(3:K)*read A (W 2) i-W 3 i := by
    rw [read_eq]
    simp only [G,reflectedStageRow,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      mat_apply,Nat.reduceAdd,Nat.cast_ofNat,W]
  have wt (n : ℕ) (i : Fin s) : W n i=b i*y i^n := rfl
  have wtwo (i : Fin s) (hui : u < i) : W 2 i=V*W 1 i := by
    rw [wt,wt]
    rcases tail i hui with h|h|h
    · rw [h]; ring
    · change y i=0 at h; rw [h]; ring
    · change y i=V at h; rw [h]; ring
  have wthree (i : Fin s) (hui : u < i) : W 3 i=V^2*W 1 i := by
    rw [wt,wt]
    rcases tail i hui with h|h|h
    · rw [h]; ring
    · change y i=0 at h; rw [h]; ring
    · change y i=V at h; rw [h]; ring
  have rt (i : Fin s) (hui : u < i) : read A (W 2) i=V*read A (W 1) i := by
    rw [read,read,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i ≤ j
    · rw [wtwo j (lt_of_lt_of_le hui h)]; ring
    · rw [ha (lt_of_not_ge h)]; ring
  have gt (i : Fin s) (hui : u < i) : G i=V^2/2*W 1 i := by
    rw [three,rt i hui,wthree i hui]
    linear_combination (3*V/2)*((two i).trans (wtwo i hui))
  let S := (Finset.univ : Finset (Fin s)).erase u
  have split (v : Fin s → K) : read A v u=(∑ j ∈ S, A j u*v j)+A u u*v u := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ u)).symm
  have compareG : (∑ j ∈ S, A j u*G j)=V^2/2*(∑ j ∈ S, A j u*W 1 j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have ne : j≠u := (Finset.mem_erase.mp hj).1
    rcases lt_or_gt_of_ne ne with h|h
    · rw [ha h]; ring
    · rw [gt j h]; ring
  have tailZero : (∑ j ∈ S, A j u*W 1 j)=0 := by
    have z : read A G u=0 := by rw [read_eq]; exact rgz
    rw [split,show G u=0 from gz,mul_zero,add_zero,compareG] at z
    exact (mul_eq_zero.mp z).resolve_left (div_ne_zero (pow_ne_zero _ hV) (by norm_num))
  have compare2 : (∑ j ∈ S, A j u*W 2 j)=V*(∑ j ∈ S, A j u*W 1 j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have ne : j≠u := (Finset.mem_erase.mp hj).1
    rcases lt_or_gt_of_ne ne with h|h
    · rw [ha h]; ring
    · rw [wtwo j h]; ring
  have h1 := two u
  rw [split,tailZero,zero_add,wt,wt] at h1
  have h2 := three u
  rw [show G u=0 from gz,split,compare2,tailZero,mul_zero,zero_add,wt,wt] at h2
  have f1 : (b u*y u)*(2*A u u-y u)=0 := by
    linear_combination h1
  have f2 : (b u*y u^2)*(3*A u u-y u)=0 := by
    linear_combination -h2
  have l1 := (mul_eq_zero.mp f1).resolve_left (mul_ne_zero hu hy)
  have l2 := (mul_eq_zero.mp f2).resolve_left (mul_ne_zero hu (pow_ne_zero _ hy))
  apply hy
  linear_combination -3*l1+2*l2

/-- A live nonzero clean receiver cannot have only a single weighted
nonzero core clock later, if the actual grade-six annihilator is zero
on that receiver. The paid cubic and its unary reverse image then both
vanish there. -/
theorem no_core_only_first_clean (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (d2 : reflectedStageRow A b 1=0) (u : Fin s) (V : K) (hV : V≠0)
    (hu : b u≠0) (hy : reflectedClock A u≠0)
    (tail : ∀ j, u < j → b j=0 ∨ reflectedClock A j=0 ∨ reflectedClock A j=V)
    (clean : ∀ v∈annih (treeSpace A 6), v u=0) : False := by
  have hg := reflectedStageRow_annih ho 7 2 (by decide)
  have h6 := annih_antitone (treeSpace_mono A (show 6≤7 by decide)) hg
  have ha6 := annih_map_transpose (mat_treeSpace A 6) (Submodule.mem_map_of_mem hg)
  exact one_clock_literal_cut ha d2 u V hV hu hy tail (clean _ h6) (clean _ ha6)

end RKResearch.Certified.Graded.OrderElevenLocalCore
