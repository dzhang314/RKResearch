module

public import RKCert.ReviewedNative.ERK19ZeroScalarInput
public import RKCert.ReviewedNative.OneWeightOrderedSigns
public import RKCert.ReviewedNative.OrderedAlternationDegree

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace RKCert.ReviewedNative.ERK19ZeroScalar

open Polynomial SignType
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- These are chronological labels, not sorted locations. Endpoints are
included in the definition, but the supplied windows rule them out. -/
def exteriorClockIndices (z : Fin 4 → K) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => z i ≤ 0 ∨ 1 ≤ z i)

private def interiorClockIndices (z : Fin 4 → K) : Finset (Fin 4) :=
  Finset.univ \ exteriorClockIndices z

omit [IsStrictOrderedRing K] in
private theorem mem_exterior_iff {z : Fin 4 → K} {i : Fin 4} :
    i ∈ exteriorClockIndices z ↔ z i ≤ 0 ∨ 1 ≤ z i := by
  simp [exteriorClockIndices]

omit [IsStrictOrderedRing K] in
private theorem mem_interior_iff {z : Fin 4 → K} {i : Fin 4} :
    i ∈ interiorClockIndices z ↔ z i ∈ Set.Ioo (0 : K) 1 := by
  simp [interiorClockIndices, mem_exterior_iff, not_or, Set.mem_Ioo]

omit [IsStrictOrderedRing K] in
private theorem interior_exterior_card (z : Fin 4 → K) :
    (interiorClockIndices z).card + (exteriorClockIndices z).card = 4 := by
  simpa [interiorClockIndices] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (exteriorClockIndices z))

private def clockFactors (z : Fin 4 → K) (S : Finset (Fin 4)) : K[X] :=
  ∏ i ∈ S, (X - C (z i))

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem clockFactors_degree (z : Fin 4 → K) (S : Finset (Fin 4)) :
    (clockFactors z S).natDegree = S.card :=
  natDegree_finsetProd_X_sub_C_eq_card S z

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem clockFactors_ne_zero (z : Fin 4 → K) (S : Finset (Fin 4)) :
    clockFactors z S ≠ 0 :=
  (monic_prod_X_sub_C z S).ne_zero

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem clockFactors_eval (z : Fin 4 → K) (S : Finset (Fin 4)) (x : K) :
    (clockFactors z S).eval x = ∏ i ∈ S, (x - z i) := by
  simp only [clockFactors, eval_prod, eval_sub, eval_X, eval_C]

omit [IsStrictOrderedRing K] in
private theorem clockFactors_split (z : Fin 4 → K) :
    clockFactors z (interiorClockIndices z) * clockFactors z (exteriorClockIndices z) =
      opposedNodalProduct z := by
  unfold clockFactors interiorClockIndices opposedNodalProduct
  rw [Finset.prod_sdiff (Finset.subset_univ (exteriorClockIndices z)), Fin.prod_univ_four]

private def interiorProduct (P : K[X]) (z : Fin 4 → K) : K[X] :=
  P * clockFactors z (interiorClockIndices z)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem quintic_ne_zero {P : K[X]} (d : P.natDegree = 5) : P ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 0) (by omega)

omit [IsStrictOrderedRing K] in
private theorem interior_product_degree {P : K[X]} {z : Fin 4 → K}
    (d : P.natDegree = 5) :
    (interiorProduct P z).natDegree = 5 + (interiorClockIndices z).card := by
  rw [interiorProduct, natDegree_mul (quintic_ne_zero d) (clockFactors_ne_zero _ _),
    d, clockFactors_degree]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem one_sub_X_degree : (1 - (X : K[X])).natDegree ≤ 1 :=
  (natDegree_sub_le 1 X).trans (by simp)

private def exteriorOrientation (z : Fin 4 → K) (i : Fin 4) : K :=
  if z i ≤ 0 then 1 else -1

/-- Factor out all exterior clocks into the positive weight. The global
moment pay remains exactly degree 18 and the sampled polynomial drops
one degree per exterior label. This avoids local simple-root reasoning. -/
private theorem interior_alternations {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) :
    HasAlternationsOn (interiorProduct P z) (Set.Ioo (0 : K) 1) (9 - e) := by
  let E := exteriorClockIndices z
  let σ : K := ∏ i ∈ E, exteriorOrientation z i
  let U : K[X] := C σ * ((1-X)*X^e*clockFactors z E)
  let F : K[X] := interiorProduct P z
  have count := interior_exterior_card z
  have bit := H.originBit
  have fd : F.natDegree = 5 + (interiorClockIndices z).card :=
    interior_product_degree H.degree
  have fn : F ≠ 0 :=
    mul_ne_zero (quintic_ne_zero H.degree) (clockFactors_ne_zero _ _)
  have ud : U.natDegree ≤ 1 + e + (exteriorClockIndices z).card := by
    have d₁ := natDegree_mul_le (p := (1-X : K[X])) (q := (X : K[X])^e)
    have d₂ := natDegree_mul_le (p := ((1-X)*X^e : K[X])) (q := clockFactors z E)
    have d₃ := natDegree_mul_le (p := C σ) (q := ((1-X)*X^e*clockFactors z E))
    have d₀ := one_sub_X_degree (K := K)
    rw [natDegree_X_pow] at d₁
    rw [clockFactors_degree] at d₂
    rw [natDegree_C, zero_add] at d₃
    change (C σ * ((1-X)*X^e*clockFactors z E)).natDegree ≤ 1 + e + E.card
    omega
  have orient (x : K) (hx : x ∈ Set.Ioo (0 : K) 1) :
      0 < σ*(clockFactors z E).eval x := by
    rw [clockFactors_eval]
    dsimp only [σ]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro i hi
    have h := (mem_exterior_iff (z := z)).mp hi
    by_cases low : z i ≤ 0
    · simpa [exteriorOrientation, low] using (sub_pos.mpr (low.trans_lt hx.1))
    · have high := h.resolve_left low
      simp only [exteriorOrientation, ite_eq_right low]
      exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr zero_lt_one)
        (sub_neg.mpr (hx.2.trans_le high))
  have up (x : K) (hx : x ∈ Set.Ioo (0 : K) 1) : 0 < U.eval x := by
    simp only [U, eval_mul, eval_C, eval_sub, eval_one, eval_X, eval_pow]
    rw [show σ*((1-x)*x^e*(clockFactors z E).eval x) =
      ((1-x)*x^e)*(σ*(clockFactors z E).eval x) by ring]
    exact mul_pos (mul_pos (sub_pos.mpr hx.2) (pow_pos hx.1 _)) (orient x hx)
  have paid (k : Fin (9-e)) : integral 0 1 (U*F*X^k.val) = 0 := by
    have rearrange : U*F*X^k.val =
        C σ * ((1-X)*X^e*(P*opposedNodalProduct z)*X^k.val) := by
      dsimp only [U, F, interiorProduct, E]
      rw [← clockFactors_split z]
      ring
    rw [rearrange, ← smul_eq_C_mul, map_smul, H.global k, smul_zero]
  have fsmall : F.natDegree < 19 := by omega
  have pay18 : U.natDegree + F.natDegree + ((9-e)-1) ≤ 18 := by omega
  have pay19 : U.natDegree + F.natDegree + ((9-e)-1) ≤ 19 := pay18.trans (by decide)
  exact HasAlternationsOn.of_grid (zero_lt_one : (0 : K) < 1)
    (grid_variation_of_positive_moments zero_lt_one fn fsmall pay19 up paid)

theorem opposed_quintic_exterior_budget {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) : (exteriorClockIndices z).card ≤ e := by
  have d := (interior_alternations H).le_natDegree
  have count := interior_exterior_card z
  have bit := H.originBit
  rw [interior_product_degree H.degree] at d
  omega

private theorem unique_exterior {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) {i : Fin 4} (hi : i ∈ exteriorClockIndices z) :
    (interiorClockIndices z).card = 3 ∧ e = 1 ∧
      ∀ j, j ≠ i → z j ∈ Set.Ioo (0 : K) 1 := by
  have h := opposed_quintic_exterior_budget H
  have bit := H.originBit
  have cap := h.trans bit
  have pos := Finset.card_pos.mpr ⟨i, hi⟩
  have count := interior_exterior_card z
  refine ⟨by omega, by omega, ?_⟩
  intro j ne
  apply mem_interior_iff.mp
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hj =>
    ne (Finset.card_le_one_iff.mp cap hj hi)⟩

private theorem flip_integral_zero {l r : K} {G : K[X]}
    (h : integral l r G = 0) : integral r l G = 0 := by
  simp only [integral_apply, sub_eq_zero] at h ⊢
  exact h.symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem add_clock_degree (U : K[X]) (a : K) :
    (U*(X-C a)).natDegree ≤ U.natDegree+1 :=
  natDegree_mul_le.trans (by simp only [natDegree_X_sub_C, le_refl])

/-- The zeroth test at the forbidden low clock already suffices. All
earlier mask roots lie to the right of this whole interval. -/
private theorem lower_paid_one {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) {i : Fin 4} (notLast : i ≠ 3)
    (other : ∀ j, j ≠ i → z j ∈ Set.Ioo (0 : K) 1) :
    ∃ U : K[X], U.natDegree ≤ 3 ∧
      (∀ x ∈ Set.Ioo (z i) 0, 0 < U.eval x) ∧ integral (z i) 0 (U*P) = 0 := by
  fin_cases i
  · have h : integral 0 (z 0) (X*P) = 0 := by
      simpa only [Fin.val_zero, pow_zero, mul_one] using H.leftFirst (0 : Fin 3)
    refine ⟨-X, by simp, ?_, ?_⟩
    · intro x hx
      simpa only [eval_neg, eval_X] using neg_pos.mpr hx.2
    · rw [neg_mul, map_neg]
      exact neg_eq_zero.mpr (flip_integral_zero h)
  · have a := (other (0 : Fin 4) (by decide)).1
    have h : integral 0 (z 1) (X*(X-C (z 0))*P) = 0 := by
      simpa only [Fin.val_zero, pow_zero, mul_one] using H.leftSecond (0 : Fin 2)
    refine ⟨X*(X-C (z 0)), (add_clock_degree X (z 0)).trans (by norm_num), ?_,
      flip_integral_zero h⟩
    intro x hx
    simpa only [eval_mul, eval_X, eval_sub, eval_C] using
      mul_pos_of_neg_of_neg hx.2 (sub_neg.mpr (hx.2.trans a))
  · have a := (other (0 : Fin 4) (by decide)).1
    have b := (other (1 : Fin 4) (by decide)).1
    have d₁ := add_clock_degree (X : K[X]) (z 0)
    have d₂ := add_clock_degree (X*(X-C (z 0))) (z 1)
    refine ⟨-(X*(X-C (z 0))*(X-C (z 1))), ?_, ?_, ?_⟩
    · rw [natDegree_neg]
      rw [natDegree_X] at d₁
      omega
    · intro x hx
      simp only [eval_neg, eval_mul, eval_X, eval_sub, eval_C]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg
        (mul_pos_of_neg_of_neg hx.2 (sub_neg.mpr (hx.2.trans a)))
        (sub_neg.mpr (hx.2.trans b)))
    · rw [neg_mul, map_neg]
      exact neg_eq_zero.mpr (flip_integral_zero H.leftThird)
  · exact (notLast rfl).elim

/-- The reversed interval starts at 1. All later mask roots lie to the
left; a single minus sign makes the native reverse weight positive. -/
private theorem upper_paid_one {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) {i : Fin 4} (notFirst : i ≠ 0)
    (other : ∀ j, j ≠ i → z j ∈ Set.Ioo (0 : K) 1) :
    ∃ U : K[X], U.natDegree ≤ 3 ∧
      (∀ x ∈ Set.Ioo 1 (z i), 0 < U.eval x) ∧ integral 1 (z i) (U*P) = 0 := by
  fin_cases i
  · exact (notFirst rfl).elim
  · have d := (other (3 : Fin 4) (by decide)).2
    have c := (other (2 : Fin 4) (by decide)).2
    have d₀ := one_sub_X_degree (K := K)
    have d₁ := add_clock_degree (1-X : K[X]) (z 3)
    have d₂ := add_clock_degree ((1-X)*(X-C (z 3))) (z 2)
    refine ⟨-((1-X)*(X-C (z 3))*(X-C (z 2))), ?_, ?_, ?_⟩
    · rw [natDegree_neg]
      omega
    · intro x hx
      simp only [eval_neg, eval_mul, eval_one, eval_X, eval_sub, eval_C]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (sub_neg.mpr hx.1) (sub_pos.mpr (d.trans hx.1)))
        (sub_pos.mpr (c.trans hx.1)))
    · rw [neg_mul, map_neg]
      exact neg_eq_zero.mpr (flip_integral_zero H.rightThird)
  · have d := (other (3 : Fin 4) (by decide)).2
    have d₀ := one_sub_X_degree (K := K)
    have d₁ := add_clock_degree (1-X : K[X]) (z 3)
    have h : integral (z 2) 1 ((1-X)*(X-C (z 3))*P) = 0 := by
      simpa only [Fin.val_zero, pow_zero, mul_one] using H.rightSecond (0 : Fin 2)
    refine ⟨-((1-X)*(X-C (z 3))), ?_, ?_, ?_⟩
    · rw [natDegree_neg]
      omega
    · intro x hx
      simp only [eval_neg, eval_mul, eval_one, eval_X, eval_sub, eval_C]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hx.1)
        (sub_pos.mpr (d.trans hx.1)))
    · rw [neg_mul, map_neg]
      exact neg_eq_zero.mpr (flip_integral_zero h)
  · have h : integral (z 3) 1 ((1-X)*P) = 0 := by
      simpa only [Fin.val_zero, pow_zero, mul_one] using H.rightFirst (0 : Fin 3)
    refine ⟨-(1-X), ?_, ?_, ?_⟩
    · rw [natDegree_neg]
      exact (one_sub_X_degree (K := K)).trans (by decide)
    · intro x hx
      simpa only [eval_neg, eval_sub, eval_X, eval_one] using
        neg_pos.mpr (sub_neg.mpr hx.1)
    · rw [neg_mul, map_neg]
      exact neg_eq_zero.mpr (flip_integral_zero h)

private theorem single_paid_alternation {P U : K[X]} {l r : K}
    (d : P.natDegree = 5) (lr : l < r) (ud : U.natDegree ≤ 3)
    (uPos : ∀ x ∈ Set.Ioo l r, 0 < U.eval x)
    (zero : integral l r (U*P) = 0) : HasAlternationsOn P (Set.Ioo l r) 1 := by
  apply HasAlternationsOn.of_grid lr
  refine grid_variation_of_positive_moments (U := U) lr (quintic_ne_zero d)
    (by omega) (by omega) uPos ?_
  intro k
  have hk := k.isLt
  have k0 : k.val = 0 := by omega
  simpa only [k0, pow_zero, mul_one] using zero

private theorem clockFactors_positive_after (z : Fin 4 → K) (S : Finset (Fin 4))
    {x : K} (after : ∀ i ∈ S, z i < x) : 0 < (clockFactors z S).eval x := by
  rw [clockFactors_eval]
  exact Finset.prod_pos (fun i hi => sub_pos.mpr (after i hi))

private theorem clockFactors_negative_before (z : Fin 4 → K) (S : Finset (Fin 4))
    (card : S.card = 3) {x : K} (before : ∀ i ∈ S, x < z i) :
    (clockFactors z S).eval x < 0 := by
  have pos : 0 < ∏ i ∈ S, ((-1 : K)*(x-z i)) :=
    Finset.prod_pos (fun i hi =>
      mul_pos_of_neg_of_neg (neg_lt_zero.mpr zero_lt_one) (sub_neg.mpr (before i hi)))
  rw [Finset.prod_mul_distrib, Finset.prod_const, card,
    show (-1 : K)^3 = (-1 : K) by ring, neg_one_mul] at pos
  rw [clockFactors_eval]
  exact neg_pos.mp pos

private theorem variation_neg_same (P : K[X]) (xs : List K) :
    variation (-P) xs = variation P xs := by
  unfold variation
  simpa only [List.map_map, Function.comp_def, eval_neg] using
    (List.signVariations_map_of_sign_eq_neg
      (f := fun x : K => -x) (fun x => Left.sign_neg x) (xs.map P.eval))

private theorem alternations_mul_positive {P B : K[X]} {S : Set K} {m : ℕ}
    (h : HasAlternationsOn P S m) (bPos : ∀ x ∈ S, 0 < B.eval x) :
    HasAlternationsOn (P*B) S m := by
  obtain ⟨xs, inc, inside, lower⟩ := h
  refine ⟨xs, inc, inside, ?_⟩
  have same : variation (P*B) xs = variation P xs := by
    unfold variation
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left (fun x hx => by
      simp only [Function.comp_apply, eval_mul, sign_mul,
        sign_pos (bPos x (inside x hx)), mul_one])
  exact same.symm ▸ lower

private theorem alternations_mul_negative {P B : K[X]} {S : Set K} {m : ℕ}
    (h : HasAlternationsOn P S m) (bNeg : ∀ x ∈ S, B.eval x < 0) :
    HasAlternationsOn (P*B) S m := by
  have positive (x : K) (hx : x ∈ S) : 0 < (-B).eval x := by
    rw [eval_neg]
    exact neg_pos.mpr (bNeg x hx)
  obtain ⟨xs, inc, inside, lower⟩ := alternations_mul_positive h positive
  rw [mul_neg, variation_neg_same] at lower
  exact ⟨xs, inc, inside, lower⟩

private theorem forbidden_low {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e)
    {i : Fin 4} (notLast : i ≠ 3) (lo : z i < 0) : False := by
  obtain ⟨ic, bit, other⟩ := unique_exterior H (mem_exterior_iff.mpr (Or.inl lo.le))
  obtain ⟨U, ud, uPos, uzero⟩ := lower_paid_one H notLast other
  have before (x : K) (hx : x ∈ Set.Ioo (z i) 0) :
      (clockFactors z (interiorClockIndices z)).eval x < 0 :=
    clockFactors_negative_before z _ ic (fun j hj =>
      hx.2.trans ((mem_interior_iff.mp hj).1))
  have outside : HasAlternationsOn (interiorProduct P z) (Set.Ioo (z i) 0) 1 :=
    alternations_mul_negative (single_paid_alternation H.degree lo ud uPos uzero) before
  have tooMany :=
    (outside.add_open (interior_alternations H) lo.le le_rfl zero_le_one).le_natDegree
  rw [interior_product_degree H.degree, ic, bit] at tooMany
  omega

private theorem forbidden_high {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e)
    {i : Fin 4} (notFirst : i ≠ 0) (hi : 1 < z i) : False := by
  obtain ⟨ic, bit, other⟩ := unique_exterior H (mem_exterior_iff.mpr (Or.inr hi.le))
  obtain ⟨U, ud, uPos, uzero⟩ := upper_paid_one H notFirst other
  have after (x : K) (hx : x ∈ Set.Ioo 1 (z i)) :
      0 < (clockFactors z (interiorClockIndices z)).eval x :=
    clockFactors_positive_after z _ (fun j hj =>
      (mem_interior_iff.mp hj).2.trans hx.1)
  have outside : HasAlternationsOn (interiorProduct P z) (Set.Ioo 1 (z i)) 1 :=
    alternations_mul_positive (single_paid_alternation H.degree hi ud uPos uzero) after
  have tooMany :=
    ((interior_alternations H).add_open outside zero_le_one le_rfl hi.le).le_natDegree
  rw [interior_product_degree H.degree, ic, bit] at tooMany
  omega

theorem opposed_quintic_clock_location {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (H : OpposedQuinticWindows P z e) :
    0 < z 0 ∧ z 3 < 1 ∧ z 1 ∈ Set.Ioo (0 : K) 1 ∧ z 2 ∈ Set.Ioo (0 : K) 1 := by
  have pos (i : Fin 4) (notLast : i ≠ 3) : 0 < z i := by
    by_contra no
    exact forbidden_low H notLast (lt_of_le_of_ne (le_of_not_gt no) (H.active i).1)
  have ltOne (i : Fin 4) (notFirst : i ≠ 0) : z i < 1 := by
    by_contra no
    exact forbidden_high H notFirst
      (lt_of_le_of_ne (le_of_not_gt no) (H.active i).2.1.symm)
  exact ⟨pos 0 (by decide), ltOne 3 (by decide),
    ⟨pos 1 (by decide), ltOne 1 (by decide)⟩,
    ⟨pos 2 (by decide), ltOne 2 (by decide)⟩⟩


end
end RKCert.ReviewedNative.ERK19ZeroScalar
