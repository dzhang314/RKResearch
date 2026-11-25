module

public import RKCert.ReviewedNative.UnitAffineSquareMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Set.Defs
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.FormalSignedQuadrature

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.UnitBetaSquareMass RKCert.ReviewedNative.UnitAffineSquareMass
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K]

/-- A literal grouped exact-moment law for normalized formal unit mass. -/
def UnitLaw [CharZero K] (T : Finset K) (mu : K → K) (b : ℕ) : Prop :=
  ∀ H : K[X], H.natDegree ≤ b → mass H = ∑ x ∈ T, mu x * H.eval x

variable [LinearOrder K] [IsStrictOrderedRing K]

def effectivePositive (A : K[X]) (T : Finset K) (mu : K → K) : Finset K :=
  T.filter fun x => 0 < mu x * A.eval x

/-- The only positivity input is strict mass on the actual nonzero squares
multiplied by A, not pointwise positivity of arbitrary polynomials. -/
theorem UnitLaw.positive_localizer_budget {T : Finset K} {mu : K → K} {b : ℕ}
    (law : UnitLaw T mu b) (A : K[X])
    (squares : ∀ G : K[X], G ≠ 0 → 0 < mass (A * G^2)) :
    b+1 ≤ A.natDegree + 2*(effectivePositive A T mu).card := by
  by_contra no
  let S := effectivePositive A T mu
  let G := nodalHull S
  let H := A * G^2
  have gd : G.natDegree = S.card := natDegree_nodalHull S
  have G0 : G ≠ 0 := (monic_nodalHull S).ne_zero
  have power : (G^2).natDegree ≤ 2*G.natDegree := natDegree_pow_le
  have degree : H.natDegree ≤ A.natDegree + 2*G.natDegree :=
    natDegree_mul_le_of_le le_rfl power
  have hd : H.natDegree ≤ b := by
    change ¬ (b+1 ≤ A.natDegree+2*S.card) at no
    omega
  have yes : 0 < mass H := squares G G0
  have terms (x : K) (hx : x ∈ T) : mu x * H.eval x ≤ 0 := by
    by_cases pos : 0 < mu x * A.eval x
    · have hin : x ∈ S := Finset.mem_filter.mpr ⟨hx, pos⟩
      have root : G.eval x = 0 := nodalHull_eval_of_mem hin
      simp [H, eval_mul, eval_pow, root]
    · simp only [H, eval_mul, eval_pow, ← mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt pos) (sq_nonneg _)
  have bad : mass H ≤ 0 := by
    rw [law H hd]
    exact Finset.sum_nonpos terms
  exact (not_lt_of_ge bad) yes

theorem UnitLaw.positive_budget {T : Finset K} {mu : K → K} {b : ℕ}
    (law : UnitLaw T mu b) :
    b+1 ≤ 2*(T.filter fun x => 0 < mu x).card := by
  have sq : ∀ G : K[X], G ≠ 0 → 0 < mass (1 * G^2) := by
    intro G hG
    simpa only [betaWeight, pow_zero, one_mul] using mass_beta_square_pos 0 0 hG
  simpa only [effectivePositive, natDegree_one, eval_one, mul_one, zero_add] using
    law.positive_localizer_budget 1 sq

/-- Same oriented factor as the general interval mask, positive on the
corresponding open interval for an exterior or boundary root. -/
def exteriorLinear (l t : K) : K[X] :=
  if t≤l then X-C t else C t-X

def exteriorMask (l : K) (E : Finset K) : K[X] :=
  ∏ t ∈ E, exteriorLinear l t

theorem exteriorLinear_degree (l t : K) : (exteriorLinear l t).natDegree ≤ 1 := by
  by_cases side : t≤l
  · simpa only [exteriorLinear, if_pos side] using (natDegree_X_sub_C t).le
  · rw [exteriorLinear, if_neg side]
    simpa only [natDegree_C, natDegree_X, max_eq_right (Nat.zero_le 1)] using
      (natDegree_sub_le (C t) (X : K[X]))

theorem exteriorMask_degree (l : K) (E : Finset K) :
    (exteriorMask l E).natDegree ≤ E.card := by
  classical
  unfold exteriorMask
  induction E using Finset.induction_on with
  | empty => simp
  | @insert t E off ih =>
      rw [Finset.prod_insert off, Finset.card_insert_of_notMem off]
      exact (natDegree_mul_le_of_le (exteriorLinear_degree l t) ih).trans (by omega)

theorem exteriorMask_zero (l : K) {E : Finset K} {t : K} (ht : t ∈ E) :
    (exteriorMask l E).eval t = 0 := by
  rw [exteriorMask, eval_prod]
  apply Finset.prod_eq_zero ht
  by_cases side : t≤l <;> simp [exteriorLinear, side]

theorem exteriorMask_pos {l r : K} {E : Finset K}
    (outside : ∀ t ∈ E, t≤l ∨ r≤t) {x : K} (hx : x ∈ Set.Ioo l r) :
    0 < (exteriorMask l E).eval x := by
  rw [exteriorMask, eval_prod]
  apply Finset.prod_pos
  intro t ht
  by_cases side : t≤l
  · simp only [exteriorLinear, if_pos side, eval_sub, eval_X, eval_C]
    exact sub_pos.mpr (side.trans_lt hx.1)
  · simp only [exteriorLinear, if_neg side, eval_sub, eval_X, eval_C]
    exact sub_pos.mpr (hx.2.trans_le ((outside t ht).resolve_left side))

theorem exteriorLinear_endpointAffine {t : K} (ex : t≤0 ∨ 1≤t) :
    EndpointAffine (exteriorLinear 0 t) := by
  by_cases side : t≤0
  · refine ⟨exteriorLinear_degree 0 t, ?_, ?_, Or.inr ?_⟩
    · simp only [exteriorLinear, if_pos side, eval_sub, eval_X, eval_C]
      exact sub_nonneg.mpr side
    · simp only [exteriorLinear, if_pos side, eval_sub, eval_X, eval_C]
      exact sub_nonneg.mpr (side.trans zero_le_one)
    · simp only [exteriorLinear, if_pos side, eval_sub, eval_X, eval_C]
      exact sub_pos.mpr (side.trans_lt zero_lt_one)
  · have right : 1≤t := ex.resolve_left side
    refine ⟨exteriorLinear_degree 0 t, ?_, ?_, Or.inl ?_⟩
    · simp only [exteriorLinear, if_neg side, eval_sub, eval_X, eval_C]
      exact sub_nonneg.mpr (zero_le_one.trans right)
    · simp only [exteriorLinear, if_neg side, eval_sub, eval_X, eval_C]
      exact sub_nonneg.mpr right
    · simp only [exteriorLinear, if_neg side, eval_sub, eval_X, eval_C]
      exact sub_pos.mpr (zero_lt_one.trans_le right)

theorem mass_exteriorMask_sq_pos {E : Finset K}
    (outside : ∀ t ∈ E, t≤0 ∨ 1≤t) {Q : K[X]} (Q0 : Q ≠ 0) :
    0 < mass (exteriorMask 0 E * Q^2) := by
  simpa only [betaWeight, pow_zero, one_mul, exteriorMask] using
    mass_beta_finset_prod_sq_pos E (exteriorLinear 0) Q0 0 0
      (fun t ht => exteriorLinear_endpointAffine (outside t ht))

def exteriorSites (T : Finset K) : Finset K :=
  T.filter (fun x => x≤0 ∨ 1≤x)

def negativeInteriorSites (T : Finset K) (mu : K → K) : Finset K :=
  (T \ exteriorSites T).filter (fun x => mu x < 0)

/-- The arithmetic case needed when no order-one condition is available. -/
theorem exterior_negative_le_twice_card (T : Finset K) (mu : K → K) :
    (exteriorSites T).card+2*(negativeInteriorSites T mu).card ≤ 2*T.card := by
  have sub : exteriorSites T ⊆ T := Finset.filter_subset _ _
  have split := Finset.card_sdiff_add_card_eq_card sub
  have bound : (negativeInteriorSites T mu).card ≤ (T \ exteriorSites T).card :=
    Finset.card_filter_le _ _
  omega

/-- One charge per exterior/boundary clock, two per negative interior
mass. No universal upper bound on b, and no nonzero masses, are required. -/
theorem UnitLaw.exterior_and_negative_budget {T : Finset K} {mu : K → K} {b : ℕ}
    (law : UnitLaw T mu b) :
    b+1+(exteriorSites T).card+2*(negativeInteriorSites T mu).card ≤ 2*T.card := by
  let E := exteriorSites T
  let A := exteriorMask 0 E
  let I := T \ E
  let Y := I.filter (fun x => 0 < mu x)
  let Z := I.filter (fun x => ¬ 0 < mu x)
  have sub : E ⊆ T := Finset.filter_subset _ _
  have outside : ∀ x ∈ E, x≤0 ∨ 1≤x := fun _ hx => (Finset.mem_filter.mp hx).2
  have inside {x : K} (hx : x∈T) (he : x∉E) : x∈Set.Ioo (0 : K) 1 := by
    refine ⟨lt_of_not_ge (fun h => he (Finset.mem_filter.mpr ⟨hx, Or.inl h⟩)), ?_⟩
    exact lt_of_not_ge (fun h => he (Finset.mem_filter.mpr ⟨hx, Or.inr h⟩))
  have identify : effectivePositive A T mu = Y := by
    ext x
    simp only [effectivePositive, Y, I, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hx, hp⟩
      have he : x∉E := by
        intro mem
        have az : A.eval x = 0 := exteriorMask_zero 0 mem
        rw [az, mul_zero] at hp
        exact (lt_irrefl (0 : K)) hp
      have pos : 0 < A.eval x := exteriorMask_pos outside (inside hx he)
      exact ⟨⟨hx, he⟩, (mul_pos_iff_of_pos_right pos).mp hp⟩
    · rintro ⟨⟨hx, he⟩, hp⟩
      have pos : 0 < A.eval x := exteriorMask_pos outside (inside hx he)
      exact ⟨hx, mul_pos hp pos⟩
  have ad : A.natDegree ≤ E.card := exteriorMask_degree 0 E
  have raw := law.positive_localizer_budget A (fun Q hQ => mass_exteriorMask_sq_pos outside hQ)
  rw [identify] at raw
  have parts : I.card+E.card=T.card := Finset.card_sdiff_add_card_eq_card sub
  have split : Y.card+Z.card=I.card :=
    Finset.card_filter_add_card_filter_not (s:=I) (fun x => 0 < mu x)
  have negative_part : negativeInteriorSites T mu ⊆ Z := by
    intro x hx
    have data : x ∈ I ∧ mu x < 0 := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨data.1, not_lt_of_ge data.2.le⟩
  have neg_le : (negativeInteriorSites T mu).card ≤ Z.card :=
    Finset.card_le_card negative_part
  change b+1+E.card+2*(negativeInteriorSites T mu).card≤2*T.card
  omega

end
end RKCert.ReviewedNative.FormalSignedQuadrature
