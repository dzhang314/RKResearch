module

public import RKCert.ReviewedNative.OrderedAlternationDegree
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exterior signs and drift from a saturated alternating witness

Only finite interpolation is used. In particular no split, derivative
root, real closure, or topology is needed. -/
namespace RKCert.ReviewedNative.EvenExteriorBarycentric

open Polynomial RKCert.ReviewedNative.FiniteOrderedSigns
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def base {d : ℕ} (x : Fin (d+1) → K) (i : Fin (d+1)) : K[X] :=
  ∏ j ∈ (Finset.univ : Finset (Fin (d+1))).erase i, (X-C (x j))

private def denom {d : ℕ} (x : Fin (d+1) → K) (i : Fin (d+1)) : K :=
  ∏ j ∈ (Finset.univ : Finset (Fin (d+1))).erase i, (x i-x j)

private theorem base_eval {d : ℕ} (x : Fin (d+1) → K) (i : Fin (d+1)) (y : K) :
    (base x i).eval y = ∏ j ∈ (Finset.univ : Finset (Fin (d+1))).erase i, (y-x j) := by
  simp only [base, eval_prod, eval_sub, eval_X, eval_C]

private theorem base_degree {d : ℕ} (x : Fin (d+1) → K) (i : Fin (d+1)) :
    (base x i).natDegree = d := by
  rw [base, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] <;> omega

private theorem denom_ne_zero {d : ℕ} {x : Fin (d+1) → K}
    (inj : Function.Injective x) (i : Fin (d+1)) : denom x i ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr (fun e => (Finset.mem_erase.mp hj).1 (inj e.symm))

/-- Adjacent barycentric denominators have opposite signs. All other
factors pair with the same sign because there is no index between them. -/
private theorem adjacent_denom_neg {d : ℕ} {x : Fin (d+1) → K}
    (mono : StrictMono x) (i : Fin d) :
    denom x i.castSucc * denom x i.succ < 0 := by
  classical
  let I : Finset (Fin (d+1)) := Finset.univ
  let a := i.castSucc
  let b := i.succ
  let J := (I.erase a).erase b
  have ab : a < b := Fin.castSucc_lt_succ
  have an : a ≠ b := ne_of_lt ab
  have hj : b ∈ I.erase a := Finset.mem_erase.mpr ⟨an.symm, Finset.mem_univ _⟩
  have hi : a ∈ I.erase b := Finset.mem_erase.mpr ⟨an, Finset.mem_univ _⟩
  have swap : (I.erase b).erase a = J := by
    ext j
    simp only [J, Finset.mem_erase]
    constructor <;> rintro ⟨h₁,h₂,h₃⟩ <;> exact ⟨h₂,h₁,h₃⟩
  have da : denom x a = (x a-x b)*∏ j ∈ J, (x a-x j) :=
    (Finset.mul_prod_erase (I.erase a) (fun j => x a-x j) hj).symm
  have db : denom x b = (x b-x a)*∏ j ∈ J, (x b-x j) := by
    rw [← swap]
    exact (Finset.mul_prod_erase (I.erase b) (fun j => x b-x j) hi).symm
  have jp : 0 < ∏ j ∈ J, (x a-x j)*(x b-x j) := by
    apply Finset.prod_pos
    intro j jm
    have jb : j ≠ b := (Finset.mem_erase.mp jm).1
    have ja : j ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp jm).2).1
    have side : j < a ∨ b < j := by
      have jav : j.val ≠ a.val := fun e => ja (Fin.ext e)
      have jbv : j.val ≠ b.val := fun e => jb (Fin.ext e)
      change j.val < a.val ∨ b.val < j.val
      simp only [a, b, Fin.val_castSucc, Fin.val_succ] at jav jbv ⊢
      omega
    rcases side with h | h
    · exact mul_pos (sub_pos.mpr (mono h)) (sub_pos.mpr (mono (h.trans ab)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (mono (ab.trans h))) (sub_neg.mpr (mono h))
  rw [show denom x i.castSucc = denom x a from rfl,
      show denom x i.succ = denom x b from rfl, da, db]
  have e :
      ((x a-x b)*∏ j ∈ J, (x a-x j))*((x b-x a)*∏ j ∈ J, (x b-x j)) =
      (x a-x b)*(x b-x a)*(∏ j ∈ J, (x a-x j)*(x b-x j)) := by
    rw [Finset.prod_mul_distrib]
    ring
  rw [e]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (sub_neg.mpr (mono ab)) (sub_pos.mpr (mono ab))) jp

private theorem degree_lt_nodes {P : K[X]} {d : ℕ} (pd : P.natDegree ≤ d) :
    P.degree < ((Finset.univ : Finset (Fin (d+1))).card : WithBot ℕ) := by
  rw [Finset.card_univ, Fintype.card_fin]
  exact P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le pd)

private theorem positive_barycentric {T : K[X]} {d : ℕ} {x : Fin (d+1) → K}
    (Tmon : T.Monic) (td : T.natDegree = d) (mono : StrictMono x)
    (live : ∀ i, T.eval (x i) ≠ 0)
    (opp : ∀ i : Fin d, T.eval (x i.castSucc)*T.eval (x i.succ) < 0) :
    ∀ i, 0 < T.eval (x i) / denom x i := by
  classical
  let b : Fin (d+1) → K := fun i => T.eval (x i) / denom x i
  have bne (i : Fin (d+1)) : b i ≠ 0 := div_ne_zero (live i) (denom_ne_zero mono.injective i)
  have step (i : Fin d) : 0 < b i.castSucc * b i.succ := by
    simp only [b, div_mul_div_comm]
    exact div_pos_of_neg_of_neg (opp i) (adjacent_denom_neg mono i)
  have top := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (d+1)))) (v := x)
    mono.injective.injOn (degree_lt_nodes td.le)
  rw [Finset.card_univ, Fintype.card_fin, show (d+1)-1=d by omega] at top
  have coeff : T.coeff d = 1 := by rw [← td, coeff_natDegree, Tmon.leadingCoeff]
  have sum : (∑ i, b i) = 1 := by
    rw [coeff] at top
    simpa only [b, denom] using top.symm
  have first : 0 < b 0 := by
    apply lt_of_not_ge
    intro h
    have n₀ : b 0 < 0 := lt_of_le_of_ne h (bne 0)
    have negAll (i : Fin (d+1)) : b i < 0 := by
      induction i using Fin.induction with
      | zero => exact n₀
      | succ j ih =>
          rcases mul_pos_iff.mp (step j) with p | n
          · exact (not_lt_of_ge p.1.le ih).elim
          · exact n.2
    have bad : (∑ i, b i) ≤ 0 := Finset.sum_nonpos (fun i _ => (negAll i).le)
    rw [sum] at bad
    exact (not_lt_of_ge bad) zero_lt_one
  intro i
  change 0 < b i
  induction i using Fin.induction with
  | zero => exact first
  | succ j ih =>
      rcases mul_pos_iff.mp (step j) with p | n
      · exact p.2
      · exact (not_lt_of_ge ih.le n.1).elim

private theorem expansion {T : K[X]} {d : ℕ} {x : Fin (d+1) → K}
    (td : T.natDegree = d) (inj : Function.Injective x) :
    T = ∑ i, C (T.eval (x i) / denom x i) * base x i := by
  classical
  let S : K[X] := ∑ i, C (T.eval (x i)/denom x i)*base x i
  have sd : S.natDegree ≤ d := natDegree_sum_le_of_forall_le _ _
    (fun i _ => (natDegree_C_mul_le _ _).trans (base_degree x i).le)
  change T = S
  apply eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset (Fin (d+1))) inj.injOn
  · exact degree_lt_nodes td.le
  · exact degree_lt_nodes sd
  · intro i _
    simp only [S, eval_finsetSum, eval_mul, eval_C]
    have es :
        (∑ j, (T.eval (x j)/denom x j)*(base x j).eval (x i)) =
          (T.eval (x i)/denom x i)*(base x i).eval (x i) := by
      apply Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      intro j _ ji
      have zm : i ∈ (Finset.univ : Finset (Fin (d+1))).erase j :=
        Finset.mem_erase.mpr ⟨ji.symm, Finset.mem_univ i⟩
      have zero : (base x j).eval (x i) = 0 := by
        rw [base_eval, ← Finset.mul_prod_erase _ (fun k => x i-x k) zm,
          sub_self, zero_mul]
      rw [zero, mul_zero]
    rw [es, base_eval]
    change T.eval (x i) = (T.eval (x i)/denom x i)*denom x i
    rw [div_mul_cancel₀ _ (denom_ne_zero inj i)]

private theorem prod_strict {ι : Type*} {I : Finset ι} {f g : ι → K}
    (ne : I.Nonempty) (fp : ∀ i ∈ I, 0 < f i)
    (lt : ∀ i ∈ I, f i < g i) : (∏ i ∈ I, f i) < ∏ i ∈ I, g i :=
  Finset.prod_lt_prod_of_nonempty₀ fp lt ne

private theorem left_product {ι : Type*} {I : Finset ι} {x : ι → K} {n : ℕ}
    (card : I.card = 2*n) (y : K) :
    (∏ i ∈ I, (y-x i)) = ∏ i ∈ I, (x i-y) := by
  calc
    _ = ∏ i ∈ I, ((-1 : K)*(x i-y)) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, card, pow_mul] <;> norm_num

/-- Positive even monic exterior values, strict on each exterior
interval, directly from the saturated alternating samples. -/
theorem exterior_of_even_alternations {T : K[X]} {n : ℕ}
    (n0 : 0 < n) (tm : T.Monic) (td : T.natDegree = 2*n)
    (alt : HasAlternationsOn T (Set.Ioo (0 : K) 1) (2*n)) :
    (∀ y : K, y ≤ 0 → 0 < T.eval y) ∧
    (∀ y : K, 1 ≤ y → 0 < T.eval y) ∧
    (∀ y z : K, y < z → z ≤ 0 → T.eval z < T.eval y) ∧
    (∀ y z : K, 1 ≤ y → y < z → T.eval y < T.eval z) := by
  classical
  obtain ⟨xs, inc, inside, run, count⟩ := alt.alternating_samples
  have len : 2*n+1 ≤ xs.length := by omega
  let x (i : Fin (2*n+1)) : K := xs[i.val]'(i.isLt.trans_le len)
  have mono : StrictMono x := by
    intro i j ij
    exact (List.pairwise_iff_getElem.mp inc) i.val j.val
      (i.isLt.trans_le len) (j.isLt.trans_le len) ij
  have live (i : Fin (2*n+1)) : T.eval (x i) ≠ 0 :=
    run.nonzero _ (List.getElem_mem (i.isLt.trans_le len))
  have xin (i : Fin (2*n+1)) : x i ∈ Set.Ioo (0 : K) 1 :=
    inside _ (List.getElem_mem (i.isLt.trans_le len))
  have opp (i : Fin (2*n)) : T.eval (x i.castSucc)*T.eval (x i.succ) < 0 := by
    have h := (List.isChain_iff_getElem.mp run.jumps) i.val (by have hi := i.isLt; omega)
    simpa only [x, Fin.val_castSucc, Fin.val_succ] using h
  let b (i : Fin (2*n+1)) : K := T.eval (x i) / denom x i
  have bpos (i : Fin (2*n+1)) : 0 < b i := positive_barycentric tm td mono live opp i
  have ex (y : K) : T.eval y = ∑ i, b i*(base x i).eval y := by
    have h := congrArg (fun P : K[X] => P.eval y) (expansion td mono.injective)
    simpa only [b, eval_finsetSum, eval_mul, eval_C] using h
  have ec (i : Fin (2*n+1)) :
      ((Finset.univ : Finset (Fin (2*n+1))).erase i).card = 2*n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] <;> omega
  have en (i : Fin (2*n+1)) : ((Finset.univ : Finset (Fin (2*n+1))).erase i).Nonempty :=
    Finset.card_pos.mp (by rw [ec]; omega)
  have bl (i : Fin (2*n+1)) (y : K) :
      (base x i).eval y = ∏ j ∈ (Finset.univ : Finset (Fin (2*n+1))).erase i, (x j-y) :=
    (base_eval x i y).trans (left_product (ec i) y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [ex]
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    rw [bl]
    exact mul_pos (bpos i) (Finset.prod_pos (fun j _ => sub_pos.mpr (hy.trans_lt (xin j).1)))
  · intro y hy
    rw [ex]
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    rw [base_eval]
    exact mul_pos (bpos i) (Finset.prod_pos (fun j _ => sub_pos.mpr ((xin j).2.trans_le hy)))
  · intro y z yz z0
    rw [ex y, ex z]
    apply sub_pos.mp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    simp only [bl]
    exact sub_pos.mpr (mul_lt_mul_of_pos_left (prod_strict (en i)
      (fun j _ => sub_pos.mpr (z0.trans_lt (xin j).1))
      (fun j _ => sub_lt_sub_left yz _)) (bpos i))
  · intro y z y1 yz
    rw [ex y, ex z]
    apply sub_pos.mp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    simp only [base_eval]
    exact sub_pos.mpr (mul_lt_mul_of_pos_left (prod_strict (en i)
      (fun j _ => sub_pos.mpr ((xin j).2.trans_le y1))
      (fun j _ => sub_lt_sub_right yz _)) (bpos i))

end
end RKCert.ReviewedNative.EvenExteriorBarycentric
