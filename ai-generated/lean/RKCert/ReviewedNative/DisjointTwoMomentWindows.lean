module

public import RKCert.ReviewedNative.OneWeightOrderedSigns
public import RKCert.ReviewedNative.OrderedAlternationDegree
import RKCert.ReviewedNative.LegendreEnergyRatio
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The terminal endpoint is appended only to the sign samples. The
polynomial comparison is integrated on the original affine grid. -/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.LegendreEnergy

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem three_samples {q : K[X]} {S : Set K} (h : HasAlternationsOn q S 2) :
    ∃ a b c : K, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧
      q.eval a * q.eval b < 0 ∧ q.eval b * q.eval c < 0 := by
  obtain ⟨xs, inc, inside, alt, count⟩ := h.alternating_samples
  have i0 : 0 < xs.length := by omega
  have i1 : 1 < xs.length := by omega
  have i2 : 2 < xs.length := by omega
  let a := xs[0]'i0
  let b := xs[1]'i1
  let c := xs[2]'i2
  refine ⟨a, b, c, inside _ (List.getElem_mem i0), inside _ (List.getElem_mem i1),
    inside _ (List.getElem_mem i2), ?_, ?_, ?_, ?_⟩
  · exact (List.pairwise_iff_getElem.mp inc) 0 1 i0 i1 (by decide)
  · exact (List.pairwise_iff_getElem.mp inc) 1 2 i1 i2 (by decide)
  · exact (List.isChain_iff_getElem.mp alt.jumps) 0 i1
  · exact (List.isChain_iff_getElem.mp alt.jumps) 1 i2

private theorem four_changes {q : K[X]} {S : Set K} {a b c d : K}
    (as : a ∈ S) (bs : b ∈ S) (cs : c ∈ S) (ds : d ∈ S)
    (ab : a < b) (bc : b < c) (cd : c < d)
    (abn : q.eval a * q.eval b < 0) (bcn : q.eval b * q.eval c < 0)
    (cdn : q.eval c * q.eval d < 0) : HasAlternationsOn q S 3 := by
  have ai := (mul_ne_zero_iff.mp (ne_of_lt abn)).1
  have bi := (mul_ne_zero_iff.mp (ne_of_lt abn)).2
  have ci := (mul_ne_zero_iff.mp (ne_of_lt cdn)).1
  have di := (mul_ne_zero_iff.mp (ne_of_lt cdn)).2
  have inc : ([a, b, c, d] : List K).Pairwise (· < ·) := by
    simp [List.pairwise_cons, ab, bc, cd, ab.trans bc, bc.trans cd, ab.trans (bc.trans cd)]
  have on (x : K) (hx : x ∈ [a, b, c, d]) : x ∈ S := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact as
    · exact bs
    · exact cs
    · exact ds
  have nz (x : K) (hx : x ∈ [a, b, c, d]) : q.eval x ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ai
    · exact bi
    · exact ci
    · exact di
  have jumps : ([a, b, c, d] : List K).IsChain (fun x y => q.eval x * q.eval y < 0) := by
    simp [List.isChain_cons_cons, List.isChain_pair, abn, bcn, cdn]
  exact HasAlternationsOn.of_alternating_samples inc on ⟨nz, jumps⟩ (by simp)

private theorem one_sub_X_degree : (1 - X : K[X]).natDegree ≤ 1 := by
  have e : (1 - X : K[X]) = -(X - C (1 : K)) := by simp [neg_sub]
  rw [e, natDegree_neg, natDegree_X_sub_C]

private theorem exists_quadratic_at_one (T : K[X]) (td : T.natDegree ≤ 2) :
    ∃ a b : K, T = C (T.eval 1) + C a * (1 - X) + C b * (1 - X)^2 := by
  let S := T.comp (1 - X)
  have sd : S.natDegree ≤ 2 := by
    have e : S.natDegree ≤ 2 * 1 := natDegree_comp_le.trans (Nat.mul_le_mul td one_sub_X_degree)
    exact e
  have expansion : S = C (S.coeff 0) + C (S.coeff 1) * X + C (S.coeff 2) * X^2 := by
    have h := S.as_sum_range_C_mul_X_pow' (n := 3) (by omega)
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
      pow_one] using h
  have back : S.comp (1 - X) = T := by
    dsimp only [S]
    rw [comp_assoc, show ((1 - X : K[X]).comp (1 - X)) = X by simp, comp_X]
  have eval0 : S.coeff 0 = T.eval 1 := by
    dsimp only [S]
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_sub, eval_one, eval_X, sub_zero]
  have e := congrArg (fun P : K[X] => P.comp (1 - X)) expansion
  refine ⟨S.coeff 1, S.coeff 2, ?_⟩
  simpa only [back, add_comp, mul_comp, C_comp, X_comp, pow_comp, eval0] using e

private theorem positive_right_mean {q : K[X]} (qd : q.natDegree ≤ 4) (qn : q ≠ 0)
    {u z : K} (uz : u < z) (z1 : z < 1) (atOne : 0 < q.eval 1)
    (left : HasAlternationsOn q (Set.Ioo (0 : K) u) 2)
    (r1 : integral z 1 ((1 - X) * q) = 0)
    (r2 : integral z 1 ((1 - X)^2 * q) = 0) :
    0 < integral z 1 q := by
  let xs := gridSamples z 1 ++ [1]
  have inc : xs.Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨gridSamples_increasing z1, by simp, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton.mp hy]
    exact (gridSamples_inside z1 x hx).2
  have inside (x : K) (hx : x ∈ xs) : x ∈ Set.Ioc z 1 := by
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨a, b⟩ := gridSamples_inside z1 x h
      exact ⟨a, b.le⟩
    · rw [List.mem_singleton.mp h]
      exact ⟨z1, le_rfl⟩
  have right : HasAlternationsOn q (Set.Ioc z 1) (variation q xs) :=
    ⟨xs, inc, inside, le_rfl⟩
  have bound := (left.add_separated right (fun _ hx _ hy => hx.2.trans (uz.trans hy.1))).le_natDegree
  have count : variation q xs ≤ 2 := by omega
  let x (i : Fin xs.length) := xs[i.val]
  have mono : StrictMono x := fun i j ij =>
    (List.pairwise_iff_getElem.mp inc) i.val j.val i.isLt j.isLt ij
  have repr (y : K) (hy : y ∈ xs) : ∃ i : Fin xs.length, x i = y := by
    obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hy
    exact ⟨⟨n, hn⟩, he⟩
  obtain ⟨i₁, eqOne⟩ := repr 1 (by simp [xs])
  have live : ∃ i : Fin xs.length, q.eval (x i) ≠ 0 := by
    refine ⟨i₁, ?_⟩
    rw [eqOne]
    exact atOne.ne'
  obtain ⟨T, deg, fit⟩ := exists_grid_separator (x := x) (a := fun i => q.eval (x i)) mono live
  have varEq : (List.ofFn (fun i : Fin xs.length => q.eval (x i))).signVariations =
      variation q xs := by
    unfold variation
    dsimp only [x]
    exact congrArg List.signVariations (List.ofFn_getElem_eq_map xs (fun y => q.eval y))
  have td : T.natDegree ≤ 2 := deg.trans (varEq.trans_le count)
  have tOne : 0 < T.eval 1 := by
    have liveOne : q.eval (x i₁) ≠ 0 := by rw [eqOne]; exact atOne.ne'
    have h := fit i₁ liveOne
    rw [eqOne] at h
    exact pos_of_mul_pos_right h atOne.le
  have gridFit (i : Fin 19) (hi : q.eval (intervalPoint z 1 i) ≠ 0) :
      0 < q.eval (intervalPoint z 1 i) * T.eval (intervalPoint z 1 i) := by
    have mem : intervalPoint z 1 i ∈ xs :=
      List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩))
    obtain ⟨j, ej⟩ := repr _ mem
    rw [← ej] at hi ⊢
    exact fit j hi
  have degree : (q * T).natDegree ≤ 6 := natDegree_mul_le_of_le qd td
  obtain ⟨i, hi⟩ := exists_nonzero_grid_sample z1 qn (qd.trans_lt (by decide : 4 < 19))
  have pos : 0 < integral z 1 (q * T) := by
    refine integral_pos_of_grid_samples z1 (degree.trans (by decide : 6 ≤ 19)) ?_ ?_
    · intro j
      rw [eval_mul]
      by_cases zero : q.eval (intervalPoint z 1 j) = 0
      · rw [zero, zero_mul]
      · exact (gridFit j zero).le
    · exact ⟨i, by rw [eval_mul]; exact gridFit i hi⟩
  obtain ⟨a, b, rep⟩ := exists_quadratic_at_one T td
  have eq : q * T = C (T.eval 1) * q + C a * ((1 - X) * q) +
      C b * ((1 - X)^2 * q) := calc
    _ = q * (C (T.eval 1) + C a * (1 - X) + C b * (1 - X)^2) :=
      congrArg (fun P : K[X] => q * P) rep
    _ = _ := by ring
  rw [eq] at pos
  simp only [map_add, integral_C_mul, r1, r2, mul_zero, add_zero] at pos
  exact pos_of_mul_pos_right pos tOne.le

/-- The two end pairs of a quartic across disjoint windows exhaust its
variation. There is no negative value in the gap and the unweighted
right mean is strictly positive. The endpoint signs are explicit. -/
theorem gap_nonneg_and_right_mean_pos {q : K[X]} (qd : q.natDegree ≤ 4)
    {u z : K} (u0 : 0 < u) (uz : u < z) (z1 : z < 1)
    (atZero : 0 < q.eval 0) (atOne : 0 < q.eval 1)
    (l1 : integral 0 u (X * q) = 0) (l2 : integral 0 u (X^2 * q) = 0)
    (r1 : integral z 1 ((1 - X) * q) = 0) (r2 : integral z 1 ((1 - X)^2 * q) = 0) :
    (∀ x ∈ Set.Icc u z, 0 ≤ q.eval x) ∧ 0 < integral z 1 q := by
  have qn : q ≠ 0 := by intro h; rw [h, eval_zero] at atZero; exact lt_irrefl _ atZero
  have sd : q.natDegree < 19 := qd.trans_lt (by decide : 4 < 19)
  have ld : (X : K[X]).natDegree ≤ 1 := natDegree_X.le
  have lPay (i : Fin 2) : integral 0 u ((X : K[X]) * q * X^i.val) = 0 := by
    fin_cases i
    · change integral 0 u (X * q * X^0) = 0
      rw [pow_zero, mul_one, l1]
    · change integral 0 u (X * q * X^1) = 0
      rw [pow_one, show X * q * X = X^2 * q by ring, l2]
  have rPay (i : Fin 2) : integral z 1 ((1 - X) * q * X^i.val) = 0 := by
    fin_cases i
    · change integral z 1 ((1 - X) * q * X^0) = 0
      rw [pow_zero, mul_one, r1]
    · change integral z 1 ((1 - X) * q * X^1) = 0
      rw [pow_one, show (1 - X) * q * X = (1 - X) * q - (1 - X)^2 * q by ring,
        map_sub, r1, r2, sub_zero]
  have left : HasAlternationsOn q (Set.Ioo (0 : K) u) 2 :=
    HasAlternationsOn.of_grid u0 (grid_variation_of_positive_moments (U := X) (m := 2)
      u0 qn sd (by omega) (fun x hx => by simpa only [eval_X] using hx.1) lPay)
  have rd : (1 - X : K[X]).natDegree ≤ 1 := one_sub_X_degree
  have right : HasAlternationsOn q (Set.Ioo z (1 : K)) 2 :=
    HasAlternationsOn.of_grid z1 (grid_variation_of_positive_moments (U := 1 - X) (m := 2)
      z1 qn sd (by omega)
      (fun x hx => by simpa only [eval_sub, eval_one, eval_X] using sub_pos.mpr hx.2) rPay)
  refine ⟨?_, positive_right_mean qd qn uz z1 atOne left r1 r2⟩
  obtain ⟨a, b, c, ha, hb, hc, ab, bc, abn, bcn⟩ := three_samples left
  have ap : 0 < q.eval a := by
    rcases lt_trichotomy (q.eval a) 0 with h | h | h
    · have extra : HasAlternationsOn q (Set.Ico (0 : K) u) 3 :=
        four_changes ⟨le_rfl, u0⟩ ⟨ha.1.le, ha.2⟩ ⟨hb.1.le, hb.2⟩ ⟨hc.1.le, hc.2⟩
          ha.1 ab bc (mul_neg_of_pos_of_neg atZero h) abn bcn
      have cap := (extra.add_separated right (fun _ hx _ hy => hx.2.trans (uz.trans hy.1))).le_natDegree
      omega
    · rw [h, zero_mul] at abn
      exact (lt_irrefl _ abn).elim
    · exact h
  have bn : q.eval b < 0 := by
    rcases mul_neg_iff.mp abn with h | h
    · exact h.2
    · exact (not_lt_of_ge ap.le h.1).elim
  have cp : 0 < q.eval c := by
    rcases mul_neg_iff.mp bcn with h | h
    · exact (not_lt_of_ge h.1.le bn).elim
    · exact h.2
  intro x hx
  by_contra! negative
  have widen (y : K) (hy : y ∈ Set.Ioo (0 : K) u) : y ∈ Set.Icc (0 : K) z :=
    ⟨hy.1.le, (hy.2.trans uz).le⟩
  have extra : HasAlternationsOn q (Set.Icc (0 : K) z) 3 :=
    four_changes (widen _ ha) (widen _ hb) (widen _ hc) ⟨u0.le.trans hx.1, hx.2⟩
      ab bc (hc.2.trans_le hx.1) abn bcn (mul_neg_of_pos_of_neg cp negative)
  have cap := (extra.add_separated right (fun _ hx _ hy => hx.2.trans_lt hy.1)).le_natDegree
  omega

end
end RKCert.ReviewedNative.FiniteOrderedSigns
