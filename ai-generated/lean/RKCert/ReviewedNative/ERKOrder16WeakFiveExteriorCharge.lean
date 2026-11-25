module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import RKCert.ReviewedNative.PaidMarkedFactorAlternations
import RKCert.ReviewedNative.LegendreEnergyRatio
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.LegendreEnergy
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Count the exterior among the four original non-origin clock labels,
with no numerical ordering of the marked stages. -/
def exteriorMarkedClocks (c : Fin 5 → K) : Finset (Fin 5) :=
  (Finset.univ.erase 0).filter (fun i => c i < 0 ∨ 1 < c i)

/-- Every displayed exterior knot buys one additional unit-window
alternation of the actual fitting polynomial. The square absorbs all
other marked factors using the same six paid global moments. -/
theorem Moments.unit_alternations_of_exterior_count {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) :
    HasAlternationsOn q (Set.Ioo (0 : K) 1) ((exteriorMarkedClocks c).card + 2) := by
  classical
  let S : Finset (Fin 5) := Finset.univ.erase 0
  let p (i : Fin 5) := c i < 0 ∨ 1 < c i
  let Eset := exteriorMarkedClocks c
  let Dset := S.filter (fun i => ¬ p i)
  have S4 : S.card = 4 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
  have charge : Eset.card + Dset.card = 4 := by
    have h := Finset.card_filter_add_card_filter_not (s := S) p
    change Eset.card + Dset.card = S.card at h
    exact h.trans S4
  let sg (i : Fin 5) : K := if c i < 0 then 1 else -1
  let σ : K := ∏ i ∈ Eset, sg i
  let E : K[X] := ∏ i ∈ Eset, C (sg i) * (X - C (c i))
  let D : K[X] := ∏ i ∈ Dset, (X - C (c i))
  let W : K[X] := (X * (1 - X)) * E
  have hull : (∏ i ∈ S, (X - C (c i))) = nodalTail c Z := by
    have setEq : S = {1, 2, 3, 4} := by
      change (Finset.univ : Finset (Fin 5)).erase 0 = {1, 2, 3, 4}
      decide
    have n1 : (1 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5)) := by decide
    have n2 : (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5)) := by decide
    have n3 : (3 : Fin 5) ∉ ({4} : Finset (Fin 5)) := by decide
    rw [setEq, Finset.prod_insert n1, Finset.prod_insert n2, Finset.prod_insert n3,
      Finset.prod_singleton, nodalTail, M.middleFactor]
    ring
  have rawPartition :
      (∏ i ∈ Eset, (X - C (c i))) * D = ∏ i ∈ S, (X - C (c i)) :=
    Finset.prod_filter_mul_prod_filter_not S p (fun i => X - C (c i))
  have orient : E = C σ * (∏ i ∈ Eset, (X - C (c i))) := by
    dsimp only [E, σ]
    rw [Finset.prod_mul_distrib, map_prod]
  have factor : E * D = C σ * nodalTail c Z := by
    rw [orient, mul_assoc, rawPartition, hull]
  have dd : D.natDegree = Dset.card := natDegree_finsetProd_X_sub_C_eq_card _ _
  have dn : D ≠ 0 := (monic_prod_X_sub_C c Dset).ne_zero
  have ed : E.natDegree ≤ Eset.card := by
    have h := natDegree_prod_le (s := Eset) (f := fun i => C (sg i) * (X - C (c i)))
    change E.natDegree ≤ ∑ i ∈ Eset, (C (sg i) * (X - C (c i))).natDegree at h
    apply h.trans
    calc
      _ ≤ ∑ _i ∈ Eset, 1 := by
        exact Finset.sum_le_sum fun i _ => (natDegree_C_mul_le _ _).trans
          (natDegree_X_sub_C (c i)).le
      _ = Eset.card := by simp
  have oneSub : (1 - X : K[X]).natDegree ≤ 1 := by
    have e : (1 - X : K[X]) = -(X - C (1 : K)) := by simp [neg_sub]
    rw [e, natDegree_neg, natDegree_X_sub_C]
  have wd : W.natDegree ≤ 2 + Eset.card :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le oneSub) ed
  have wpos (x : K) (hx : x ∈ Set.Ioo (0 : K) 1) : 0 < W.eval x := by
    simp only [W, eval_mul, eval_sub, eval_X, eval_one]
    apply mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2))
    dsimp only [E]
    rw [eval_prod]
    apply Finset.prod_pos
    intro i hi
    have ex : c i < 0 ∨ 1 < c i := (Finset.mem_filter.mp hi).2
    simp only [eval_mul, eval_C, eval_sub, eval_X, sg]
    rcases ex with h | h
    · simpa [h] using (sub_pos.mpr (h.trans hx.1) : 0 < x - c i)
    · have nonleft : ¬ c i < 0 := not_lt_of_ge ((zero_lt_one.trans h).le)
      rw [if_neg nonleft]
      exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr zero_lt_one) (sub_neg.mpr (hx.2.trans h))
  have paid (R : K[X]) (rd : R.natDegree ≤ D.natDegree + (Eset.card + 2 - 1)) :
      integral 0 1 (W * (q * D) * R) = 0 := by
    have degree : R.natDegree ≤ 5 := by
      rw [dd] at rd
      omega
    have eq : W * (q * D) * R =
        C σ * ((X * (1 - X)) * (q * nodalTail c Z) * R) := calc
      _ = (X * (1 - X)) * (q * (E * D)) * R := by dsimp only [W]; ring
      _ = _ := by rw [factor]; ring
    rw [eq, integral_C_mul, M.weightedMoments R degree, mul_zero]
  have qd := M.qDegree
  exact alternations_of_paid_marked_factor (m := Eset.card + 2) zero_lt_one M.qNonzero dn
    (by omega) (by omega) wpos paid

theorem Moments.exterior_count_add_two_le_degree {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : (exteriorMarkedClocks c).card + 2 ≤ q.natDegree :=
  M.unit_alternations_of_exterior_count.le_natDegree

end
end RKCert.ReviewedNative.WeakFive16
