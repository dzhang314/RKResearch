module

public import RKCert.ReviewedNative.DIRKTerminalRank
public import RKCert.ReviewedNative.DIRKGradeSixJoin
public import RKCert.ReviewedNative.C2CubicFlag
public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # The native rank and endpoint saturation at ORDER TEN, eleven stages -/

namespace RKResearch.Certified.Graded.CrossedOrderTen

open Module RKResearch FiniteRootedTree Reverse
open scoped Matrix FiniteRootedTree BigOperators

variable {K : Type*} [Field K]

private theorem nonC2_stage_floor {s : Nat} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b)
    (nc : monomialStageDefect A 1 ≠ 0) : 12 ≤ s := by
  have x := (dirk_forward_zeroSpace_rank_floor ha ho (q:=4) (by decide) (by decide)).2 nc
  have eq := treeSpace_rank_eq_of_separation ho (q:=4) (by decide)
    (coeff_defect_separated_paid ho (by decide) (by decide))
  have rev := dirk_reverse_room_unanchored ha ho (q:=4) (n:=4) (by decide) (by decide) (by decide)
  omega

/-- At the even midpoint, an actual origin makes the 6th clock
coefficient independent, buying the 11th stage at order ten. -/
theorem stage_floor {s : Nat} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) : 11 ≤ s := by
  by_cases c2 : monomialStageDefect A 1=0
  · obtain ⟨o,hr⟩ := dirk_exists_zero_row_of_C2 ha ho (by decide) c2
    have x := (dirk_forward_zeroSpace_rank_floor ha ho (q:=5) (by decide) (by decide)).1
    have eq := treeSpace_rank_eq_of_separation ho (q:=5) (by decide)
      (coeff_defect_separated_zero_row ho hr (by decide) (by decide))
    have rev := dirk_reverse_rank_budget ha ho (q:=5) (n:=3) (by decide) (by decide)
    omega
  · exact le_trans (by decide) (nonC2_stage_floor ha ho c2)

private def removeLast {s : Nat} (A : Matrix (Fin (s+1)) (Fin (s+1)) K) :
    Matrix (Fin s) (Fin s) K :=
  A.submatrix Fin.castSucc Fin.castSucc

private theorem removeLast_lower {s : Nat} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : A.IsLowerTriangular) : (removeLast A).IsLowerTriangular := by
  intro i j lt
  exact ha (show Fin.castSucc i < Fin.castSucc j from lt)

private theorem root_no_last_extra {s : Nat} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : A.IsLowerTriangular) (t : FiniteRootedTree) (i : Fin s) :
    Φ t (removeLast A) i = Φ t A i.castSucc := by
  induction t generalizing i with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    simp only [Φ,Pi.mul_apply,ht i]
    congr 1
    have z : A i.castSucc (Fin.last s)=0 := ha (Fin.castSucc_lt_last i)
    rw [Matrix.mulVec_apply_eq_sum,Matrix.mulVec_apply_eq_sum,Fin.sum_univ_castSucc,
      z,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [hu j]
    rfl

private theorem trim_inactive_last {p s : Nat}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (hb : b (Fin.last s)=0) :
    HasOrder p (removeLast A) (fun i => b i.castSucc) := by
  intro t h
  have e := ho t h
  rw [dotProduct,Fin.sum_univ_castSucc,hb,zero_mul,add_zero] at e
  simpa only [dotProduct,root_no_last_extra ha] using e

/-- No assumptions on the other weights, clock collisions, or realness. -/
structure Saturated (A : Matrix (Fin 11) (Fin 11) K) (b : Fin 11 → K) : Prop where
  c2 : monomialStageDefect A 1=0
  physical_origin : ∀ j, A 0 j=0
  e3 : finrank K (treeSpace A 3)=5
  e4 : finrank K (treeSpace A 4)=7
  e5 : finrank K (treeSpace A 5)=9
  f5 : finrank K (zeroSpace A 5)=3
  d1 : reflectedStageRow A b 0=0
  d2 : reflectedStageRow A b 1=0
  last_live : b (Fin.last 10)≠0
  last_node : nodes A (Fin.last 10)=1
  last_column : ∀ i, A i (Fin.last 10)=0

/-- Literal order-ten equality saturation, over any compatible field. -/
theorem saturated {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) : Saturated A b := by
  have c2 : monomialStageDefect A 1=0 := by
    by_contra nc
    have z := nonC2_stage_floor ha ho nc
    omega
  have h0 : ∀ j, A 0 j=0 :=
    dirk_first_row_of_zero_quadratic ha (show monomialStageDefect A 1 0=0 from congrFun c2 0)
  have f3 := (dirk_grade_three_of_C2 ha ho (by decide) c2).2
  have r3 := treeSpace_rank_eq_of_separation ho (q:=3) (by decide)
    (coeff_defect_separated_paid ho (by decide) (by decide))
  have r4 := treeSpace_rank_eq_of_separation ho (q:=4) (by decide)
    (coeff_defect_separated_paid ho (by decide) (by decide))
  have r5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide)
    (coeff_defect_separated_zero_row ho h0 (by decide) (by decide))
  have l4 := (dirk_forward_zeroSpace_rank_floor ha ho (q:=4) (by decide) (by decide)).1
  have l5 := (dirk_forward_zeroSpace_rank_floor ha ho (q:=5) (by decide) (by decide)).1
  have u4 := dirk_reverse_room_anchored ha ho (q:=4) (n:=4) (by decide) (by decide) (by decide) h0
  have u5 := dirk_reverse_rank_budget ha ho (q:=5) (n:=3) (by decide) (by decide)
  obtain ⟨d1,d2⟩ := dirk_primitiveBack_one_zero (show finrank K (primitiveBack A b 1)=0 by omega)
  have hl : b (Fin.last 10)≠0 := by
    intro dead
    have n := stage_floor (removeLast_lower ha) (trim_inactive_last ha ho dead)
    omega
  have H : LastActive b (Fin.last 10) := ⟨hl,fun j hj => False.elim ((not_lt_of_ge (Fin.le_last j)) hj)⟩
  have yn := H.dirk_reflected_zero ha d1 d2
  have one : nodes A (Fin.last 10)=1 := (sub_eq_zero.mp yn).symm
  have m := H.dirk_seed_value ha 0
  rw [d1] at m
  simp only [Pi.zero_apply,Nat.reduceAdd,Nat.cast_one,pow_zero,pow_one,mul_one,one_mul,yn, mul_zero,
    sub_zero] at m
  have last_diag : A (Fin.last 10) (Fin.last 10)=0 :=
    (mul_eq_zero.mp m.symm).resolve_right hl
  have hcol (i : Fin 11) : A i (Fin.last 10)=0 := by
    rcases lt_or_eq_of_le (Fin.le_last i) with hi | hi
    · exact ha hi
    · rwa [hi]
  exact ⟨c2,h0,by omega,by omega,by omega,by omega,d1,d2,hl,one,hcol⟩

end RKResearch.Certified.Graded.CrossedOrderTen
