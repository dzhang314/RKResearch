module

public import RKCert.ReviewedNative.DIRKTerminalRank
public import RKCert.ReviewedNative.CharZeroStageTransport

public section

/-! # From actual forward grade-six growth to stage counts

The counting and boundary results in this file work over every field.
The only additional input is an inequality for the genuine native defect
spaces of the *given* tableau: dim F₃ + 4 ≤ dim F₆. It is an explicit
premise, not a postulate or a claim established by this module. For an
arbitrary characteristic-zero ring one must instead supply the field-side
inequality for every characteristic-zero field specialization.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Separated coefficients through q and defects through a possibly higher
grade j are counted inside the actual Tⱼ, before applying a reverse budget. -/
theorem coeff_defect_tree_rank {q j : ℕ} (le : q ≤ j)
    (sep : ∀ a, coeffEval A q a ∈ zeroSpace A j → a=0) :
    q+1+finrank K (zeroSpace A j) ≤ finrank K (treeSpace A j) := by
  let F := zeroSpace A j
  let T := treeSpace A j
  let L := (coeffEval A q).coprod F.subtype
  let I := L.codRestrict T (fun z => T.add_mem
    (treeSpace_mono A le (coeffEval_mem_treeSpace A q z.1))
    (zeroSpace_le_treeSpace A j z.2.property))
  have hin : Function.Injective I := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨a,z⟩ h
    have eq : coeffEval A q a + (z : Fin s → K) = 0 :=
      congrArg (fun w : T => (w : Fin s → K)) h
    have en := eq_neg_of_add_eq_zero_left eq
    have az := sep a (en ▸ F.neg_mem z.property)
    have zz : (z : Fin s → K) = 0 := by simpa only [az,map_zero,zero_add] using eq
    exact Prod.ext az (Subtype.ext zz)
  simpa only [Module.finrank_prod,Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_injective hin)

theorem dirk_exists_zero_row_of_C2 (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    (hp : 1 ≤ p) (hc : monomialStageDefect A 1 = 0) : ∃ o, ∀ j, A o j=0 := by
  cases s with
  | zero =>
    obtain ⟨t,_⟩ := exists_lastActive ho hp
    exact Fin.elim0 t
  | succ s =>
    exact ⟨0,dirk_first_row_of_zero_quadratic ha
      (show monomialStageDefect A 1 0=0 from congrFun hc 0)⟩

/-- Every genuine extra forward dimension beyond ordinary unit growth from
grade three contributes one physical stage at *even* order. At the unpaid
top coefficient either C(2) gives a real zero row, or F₃ pays for the loss. -/
theorem dirk_even_marked_count (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {m extra : ℕ} (hm : 3 ≤ m) (pay : 2*m ≤ p)
    (marked : finrank K (zeroSpace A 3)+(m-3)+extra ≤ finrank K (zeroSpace A m)) :
    3*m-4+extra ≤ s := by
  have f3 := dirk_forward_rank_three ha ho (by omega)
  have raw := dirk_reverse_rank_budget ha ho (q:=m) (n:=m-2) (by omega) (by omega)
  by_cases c2 : monomialStageDefect A 1=0
  · obtain ⟨o,hr⟩ := dirk_exists_zero_row_of_C2 ha ho (by omega) c2
    have mid := treeSpace_rank_eq_of_separation ho (q:=m) (by omega)
      (coeff_defect_separated_zero_row ho hr (q:=m) (j:=m) pay (by omega))
    omega
  · have more := f3.2 c2
    have mid := coeff_defect_tree_rank (A:=A) (q:=m-1) (j:=m) (by omega)
      (coeff_defect_separated_paid ho (by omega) (by omega))
    omega

/-- At odd order either a zero row earns the terminal dimension, or the
extra quadratic seed is already counted in the actual grade-three rank. -/
theorem dirk_odd_marked_count (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {m extra : ℕ} (hm : 3 ≤ m) (pay : 2*m+1 ≤ p)
    (marked : finrank K (zeroSpace A 3)+(m-3)+extra ≤ finrank K (zeroSpace A m)) :
    3*m-2+extra ≤ s := by
  have f3 := dirk_forward_rank_three ha ho (by omega)
  have mid := treeSpace_rank_eq_of_separation ho (q:=m) (by omega) (coeff_separated ho pay)
  by_cases c2 : monomialStageDefect A 1=0
  · obtain ⟨o,hr⟩ := dirk_exists_zero_row_of_C2 ha ho (by omega) c2
    have term := dirk_reverse_room_anchored ha ho (q:=m) (n:=m-1) (by omega) (by omega) pay hr
    omega
  · have more := f3.2 c2
    have raw := dirk_reverse_rank_budget ha ho (q:=m) (n:=m-1) (by omega) (by omega)
    omega

/-- Forward rank can be carried to any later paid grade without borrowing
an unproved no-plateau statement. -/
theorem dirk_later_of_grade_six (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {m : ℕ} (hm : 6 ≤ m) (pay : m ≤ p)
    (six : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) :
    finrank K (zeroSpace A 3)+(m-3)+1 ≤ finrank K (zeroSpace A m) := by
  have gain := RKCert.ReviewedNative.RankFlags.finrank_gain_of_steps (zeroSpace A) hm
    (fun j lo hi => dirk_forward_zeroSpace_lt_succ ha ho (by omega) (by omega))
  omega

/-- A single grade-six surplus increases the uniform floor by one at every
p ≥ 12, including the 15-stage and 17-stage endpoints at p=12 and 13. -/
theorem dirk_uniform_of_grade_six (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    (hp : 12 ≤ p) (six : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) :
    p+(p-1)/2-2 ≤ s := by
  let m := p/2
  have hm : 6 ≤ m := by dsimp [m]; omega
  have marked := dirk_later_of_grade_six ha ho hm (by dsimp [m]; omega) six
  by_cases e : p % 2 = 0
  · have eq : p=2*m := by dsimp [m]; omega
    have lo := dirk_even_marked_count ha ho (by omega) (by omega) marked
    omega
  · have eq : p=2*m+1 := by dsimp [m]; omega
    have lo := dirk_odd_marked_count ha ho (by omega) (by omega) marked
    omega

/-- At even orders ≥14 a nonzero quadratic defect can be used together
with the *unanchored* endpoint refund one grade earlier. -/
theorem dirk_even_nonC2_of_grade_six (ha : A.IsLowerTriangular) (ho : HasOrder p A b)
    {m : ℕ} (hm : 7 ≤ m) (pay : 2*m ≤ p) (nc : monomialStageDefect A 1 ≠ 0)
    (six : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 3*m-2 ≤ s := by
  have gain := dirk_later_of_grade_six ha ho (m:=m-1) (by omega) (by omega) six
  have more := (dirk_forward_rank_three ha ho (by omega)).2 nc
  have mid := treeSpace_rank_eq_of_separation ho (q:=m-1) (by omega)
    (coeff_separated ho (by omega))
  have term := dirk_reverse_room_unanchored ha ho (q:=m-1) (n:=m-1)
    (by omega) (by omega) (by omega)
  omega

theorem dirk_order_twelve_of_grade_six (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (six : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 15 ≤ s :=
  dirk_uniform_of_grade_six ha ho (by decide) six

theorem dirk_order_thirteen_of_grade_six (ha : A.IsLowerTriangular) (ho : HasOrder 13 A b)
    (six : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 17 ≤ s :=
  dirk_uniform_of_grade_six ha ho (by decide) six

theorem dirk_order_fifteen_of_grade_six (ha : A.IsLowerTriangular) (ho : HasOrder 15 A b)
    (six : finrank K (zeroSpace A 3)+4 ≤ finrank K (zeroSpace A 6)) : 20 ≤ s :=
  dirk_uniform_of_grade_six ha ho (by decide) six

end RKResearch.Certified.Graded.Reverse

namespace RKResearch
open Module Certified.Graded
universe u

/-- A stage count descends from characteristic-zero fields to arbitrary
characteristic-zero commutative rings. The forward surplus is explicitly
required on each field tableau, not assumed to be inherited under reduction. -/
theorem HasOrder.dirk_charZero_count_of_field_grade_six
    {R : Type u} [CommRing R] [CharZero R] {s p : ℕ} {A : Matrix (Fin s) (Fin s) R}
    {b : Fin s → R} (h : HasOrder p A b) (ha : A.IsLowerTriangular) (hp : 12 ≤ p)
    (six : ∀ (K : Type u) [Field K] [CharZero K] (T : Matrix (Fin s) (Fin s) K) (w : Fin s → K),
      T.IsLowerTriangular → HasOrder p T w →
        finrank K (zeroSpace T 3)+4 ≤ finrank K (zeroSpace T 6)) :
    p+(p-1)/2-2 ≤ s :=
  h.lower_triangular_of_charZero_fields ha
    (fun K _ _ T w ht ord => Reverse.dirk_uniform_of_grade_six ht ord hp (six K T w ht ord))

end RKResearch
