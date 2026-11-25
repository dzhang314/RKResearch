module

public import RKCert.ReviewedNative.FormalSignedQuadrature
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.FormalSignedQuadrature

open Polynomial RKCert.ReviewedNative.UnitBetaSquareMass
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace ExteriorSwitch

/-- True for a strictly positive grouped mass. -/
def massFlag (mu : K → K) (x : K) : Bool := decide (0 < mu x)

/-- Previous mass flag is initialized to false on each exterior side. -/
def switchCost (mu : K → K) : Bool → List K → ℕ
  | _, [] => 0
  | prev, x::xs =>
      switchCost mu (massFlag mu x) xs + (if massFlag mu x = prev then 0 else 1)

/-- The actual root is the clock where a change occurs. -/
def switchRoots (mu : K → K) : Bool → List K → Finset K
  | _, [] => ∅
  | prev, x::xs =>
      if massFlag mu x = prev then switchRoots mu (massFlag mu x) xs
      else insert x (switchRoots mu (massFlag mu x) xs)

theorem switchCost_first_cons (mu : K → K) (x : K) (xs : List K) :
    switchCost mu false (x::xs) =
      switchCost mu (massFlag mu x) xs + (if 0 < mu x then 1 else 0) := by
  by_cases h : 0 < mu x <;> simp [switchCost, massFlag, h]

theorem switchRoots_mem (mu : K → K) (prev : Bool) (xs : List K) :
    ∀ x ∈ switchRoots mu prev xs, x ∈ xs := by
  induction xs generalizing prev with
  | nil =>
      intro x hx
      simp [switchRoots] at hx
  | cons t ts ih =>
      intro x hx
      by_cases same : massFlag mu t=prev
      · have h : x ∈ switchRoots mu (massFlag mu t) ts := by
          simpa only [switchRoots, if_pos same] using hx
        exact List.mem_cons.mpr (Or.inr (ih _ x h))
      · have h : x ∈ insert t (switchRoots mu (massFlag mu t) ts) := by
          simpa only [switchRoots, if_neg same] using hx
        rcases Finset.mem_insert.mp h with eq | h
        · exact List.mem_cons.mpr (Or.inl eq)
        · exact List.mem_cons.mpr (Or.inr (ih _ x h))

theorem switchRoots_card (mu : K → K) (prev : Bool) (xs : List K) (nd : xs.Nodup) :
    (switchRoots mu prev xs).card = switchCost mu prev xs := by
  revert prev nd
  induction xs with
  | nil =>
      intro prev _
      simp [switchRoots, switchCost]
  | cons t ts ih =>
      intro prev nd
      have tail := (List.nodup_cons.mp nd).2
      have ihCard := ih (massFlag mu t) tail
      have off : t ∉ switchRoots mu (massFlag mu t) ts :=
        fun h => (List.nodup_cons.mp nd).1 (switchRoots_mem mu _ ts t h)
      by_cases same : massFlag mu t=prev
      · simp only [switchRoots, switchCost, if_pos same, add_zero, ihCard]
      · simp only [switchRoots, switchCost, if_neg same, Finset.card_insert_of_notMem off, ihCard]

private def incoming : Bool → K
  | false => 1
  | true => -1

private theorem incoming_flip {a b : Bool} (h : a≠b) :
    (incoming a : K) = -incoming b := by
  cases a <;> cases b <;> simp_all [incoming]

private theorem mass_incoming_nonpos (mu : K → K) (x : K) (prev : Bool)
    (same : massFlag mu x=prev) : mu x*incoming prev≤0 := by
  rw [← same]
  by_cases h : 0 < mu x
  · have flag : massFlag mu x=true := by simp [massFlag,h]
    rw [flag]
    simp only [incoming, mul_neg, mul_one]
    exact neg_nonpos.mpr h.le
  · have flag : massFlag mu x=false := by simp [massFlag,h]
    rw [flag]
    simp only [incoming, mul_one]
    exact le_of_not_gt h

private theorem mask_pos_from_factors {S : Finset K} {x : K}
    (h : ∀ t∈S, 0 < (exteriorLinear 0 t).eval x) :
    0 < (exteriorMask 0 S).eval x := by
  rw [exteriorMask, eval_prod]
  exact Finset.prod_pos h

private def Outward (a b : K) : Prop :=
  0 < (exteriorLinear 0 b).eval a ∧ (exteriorLinear 0 a).eval b < 0

/-- The normalized tail invariant on one side, for either outward order. -/
private theorem switched_side_nonpos (mu : K → K) (prev : Bool) (xs : List K)
    (nd : xs.Nodup) (out : xs.Pairwise Outward) :
    ∀ x∈xs, mu x*incoming prev*(exteriorMask 0 (switchRoots mu prev xs)).eval x≤0 := by
  revert prev nd out
  induction xs with
  | nil =>
      intro prev _ _ x hx
      simp at hx
  | cons t ts ih =>
      intro prev nd out
      let b := massFlag mu t
      let S := switchRoots mu b ts
      have td := (List.nodup_cons.mp nd).2
      have tail := (List.pairwise_cons.mp out).2
      have pair (y : K) (hy : y∈ts) : Outward t y := (List.pairwise_cons.mp out).1 y hy
      have off : t∉S := fun h => (List.nodup_cons.mp nd).1 (switchRoots_mem mu b ts t h)
      intro x hx
      rcases List.mem_cons.mp hx with eq | hx
      · subst x
        by_cases same : massFlag mu t=prev
        · have later : 0 < (exteriorMask 0 S).eval t := by
            apply mask_pos_from_factors
            intro y hy
            exact (pair y (switchRoots_mem mu b ts y hy)).1
          rw [switchRoots, if_pos same]
          exact mul_nonpos_of_nonpos_of_nonneg (mass_incoming_nonpos mu t prev same) later.le
        · have z : (exteriorMask 0 (insert t S)).eval t=0 :=
            exteriorMask_zero 0 (Finset.mem_insert_self _ _)
          rw [switchRoots, if_neg same, z, mul_zero]
      · by_cases same : massFlag mu t=prev
        · rw [switchRoots, if_pos same]
          simpa only [same] using ih (massFlag mu t) td tail x hx
        · have flip : (incoming prev : K) = -incoming b :=
            incoming_flip (Ne.symm same)
          have evalInsert : (exteriorMask 0 (insert t S)).eval x =
              (exteriorLinear 0 t).eval x * (exteriorMask 0 S).eval x := by
            simp only [exteriorMask, Finset.prod_insert off, eval_mul]
          calc
            _ = (mu x*incoming b*(exteriorMask 0 S).eval x) * (-( (exteriorLinear 0 t).eval x )) := by
              rw [switchRoots, if_neg same, evalInsert, flip]
              ring
            _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
              (ih b td tail x hx) (neg_nonneg.mpr (pair x hx).2.le)

/-- The endpoints are exterior if they occur in the input support. -/
def leftSites (T : Finset K) : Finset K :=
  T.filter fun x => x≤0

def rightSites (T : Finset K) : Finset K :=
  T.filter fun x => 1≤x

def leftOutward (T : Finset K) : List K := (leftSites T).sort (· ≥ ·)
def rightOutward (T : Finset K) : List K := (rightSites T).sort (· ≤ ·)

theorem mem_leftOutward {T : Finset K} {x : K} :
    x∈leftOutward T ↔ x∈T ∧ x≤0 := by
  simp only [leftOutward, leftSites, Finset.mem_sort, Finset.mem_filter]

theorem mem_rightOutward {T : Finset K} {x : K} :
    x∈rightOutward T ↔ x∈T ∧ 1≤x := by
  simp only [rightOutward, rightSites, Finset.mem_sort, Finset.mem_filter]

private theorem left_order (T : Finset K) : (leftOutward T).Pairwise Outward := by
  have sorted : (leftOutward T).SortedGT := (leftSites T).sortedGT_sort
  refine List.Pairwise.imp_of_mem ?_ sorted.pairwise
  intro a b ha hb gt
  have a0 := (mem_leftOutward.mp ha).2
  have b0 := (mem_leftOutward.mp hb).2
  simp only [Outward, exteriorLinear, if_pos a0, if_pos b0, eval_sub, eval_X, eval_C]
  exact ⟨sub_pos.mpr gt, sub_neg.mpr gt⟩

private theorem right_order (T : Finset K) : (rightOutward T).Pairwise Outward := by
  have sorted : (rightOutward T).SortedLT := (rightSites T).sortedLT_sort
  refine List.Pairwise.imp_of_mem ?_ sorted.pairwise
  intro a b ha hb lt
  have a0 : ¬ a≤0 := not_le_of_gt (zero_lt_one.trans_le (mem_rightOutward.mp ha).2)
  have b0 : ¬ b≤0 := not_le_of_gt (zero_lt_one.trans_le (mem_rightOutward.mp hb).2)
  simp only [Outward, exteriorLinear, if_neg a0, if_neg b0, eval_sub, eval_X, eval_C]
  exact ⟨sub_pos.mpr lt, sub_neg.mpr lt⟩

def leftChosen (T : Finset K) (mu : K → K) : Finset K :=
  switchRoots mu false (leftOutward T)

def rightChosen (T : Finset K) (mu : K → K) : Finset K :=
  switchRoots mu false (rightOutward T)

private theorem left_data {T : Finset K} {mu : K → K} {x : K} (h : x∈leftChosen T mu) :
    x∈T ∧ x≤0 := mem_leftOutward.mp (switchRoots_mem mu false _ x h)

private theorem right_data {T : Finset K} {mu : K → K} {x : K} (h : x∈rightChosen T mu) :
    x∈T ∧ 1≤x := mem_rightOutward.mp (switchRoots_mem mu false _ x h)

private theorem chosen_disjoint (T : Finset K) (mu : K → K) :
    Disjoint (leftChosen T mu) (rightChosen T mu) := by
  apply Finset.disjoint_left.mpr
  intro x l r
  exact (not_le_of_gt (zero_lt_one : (0:K)<1)) ((right_data r).2.trans (left_data l).2)

def selectedExterior (T : Finset K) (mu : K → K) : Finset K :=
  leftChosen T mu ∪ rightChosen T mu

def exteriorSignSwitchCost (T : Finset K) (mu : K → K) : ℕ :=
  switchCost mu false (leftOutward T) + switchCost mu false (rightOutward T)

theorem selectedExterior_subset (T : Finset K) (mu : K → K) :
    selectedExterior T mu ⊆ exteriorSites T := by
  intro x hx
  rcases Finset.mem_union.mp hx with hl | hr
  · exact Finset.mem_filter.mpr ⟨(left_data hl).1, Or.inl (left_data hl).2⟩
  · exact Finset.mem_filter.mpr ⟨(right_data hr).1, Or.inr (right_data hr).2⟩

theorem selectedExterior_card (T : Finset K) (mu : K → K) :
    (selectedExterior T mu).card = exteriorSignSwitchCost T mu := by
  rw [selectedExterior, Finset.card_union_of_disjoint (chosen_disjoint T mu)]
  unfold leftChosen rightChosen exteriorSignSwitchCost leftOutward rightOutward
  rw [switchRoots_card mu false _ ((leftSites T).sort_nodup (· ≥ ·)),
    switchRoots_card mu false _ ((rightSites T).sort_nodup (· ≤ ·))]

theorem exteriorSignSwitchCost_le (T : Finset K) (mu : K → K) :
    exteriorSignSwitchCost T mu ≤ (exteriorSites T).card := by
  rw [← selectedExterior_card T mu]
  exact Finset.card_le_card (selectedExterior_subset T mu)

def switchMask (T : Finset K) (mu : K → K) : K[X] :=
  exteriorMask 0 (selectedExterior T mu)

private theorem factor_degree (l t : K) : (exteriorLinear l t).natDegree=1 := by
  by_cases side : t≤l
  · rw [exteriorLinear, if_pos side, natDegree_X_sub_C]
  · have flip : C t-(X:K[X]) = -(X-C t) := by ring
    rw [exteriorLinear, if_neg side, flip, natDegree_neg, natDegree_X_sub_C]

private theorem factor_ne_zero (l t : K) : exteriorLinear l t≠0 := by
  intro z
  have d := factor_degree l t
  rw [z, natDegree_zero] at d
  omega

theorem switchMask_degree (T : Finset K) (mu : K → K) :
    (switchMask T mu).natDegree = exteriorSignSwitchCost T mu := by
  rw [switchMask, exteriorMask,
    Polynomial.natDegree_prod (selectedExterior T mu) (exteriorLinear 0)
      (fun t _ => factor_ne_zero 0 t)]
  simp only [factor_degree, Finset.sum_const, Nat.nsmul_eq_mul, mul_one, selectedExterior_card]

theorem selected_outside (T : Finset K) (mu : K → K) :
    ∀ t∈selectedExterior T mu, t≤0 ∨ 1≤t := by
  intro t ht
  have got : t∈exteriorSites T := selectedExterior_subset T mu ht
  exact (Finset.mem_filter.mp got).2

theorem switchMask_exterior_nonpos {T : Finset K} {mu : K → K} {x : K}
    (hx : x∈exteriorSites T) : mu x*(switchMask T mu).eval x≤0 := by
  let L := exteriorMask 0 (leftChosen T mu)
  let R := exteriorMask 0 (rightChosen T mu)
  have split : switchMask T mu=L*R := by
    simp only [switchMask, selectedExterior, L, R, exteriorMask,
      Finset.prod_union (chosen_disjoint T mu)]
  obtain ⟨ht, hl | hr⟩ := (show x∈T ∧ (x≤0 ∨ 1≤x) from Finset.mem_filter.mp hx)
  · have left : mu x*L.eval x≤0 := by
      simpa only [incoming, mul_one, L, leftChosen] using
        switched_side_nonpos mu false (leftOutward T)
          ((leftSites T).sort_nodup (· ≥ ·)) (left_order T) x (mem_leftOutward.mpr ⟨ht,hl⟩)
    have right : 0<R.eval x := by
      apply mask_pos_from_factors
      intro y hy
      have y1 := (right_data hy).2
      have y0 : ¬ y≤0 := not_le_of_gt (zero_lt_one.trans_le y1)
      rw [exteriorLinear, if_neg y0, eval_sub, eval_C, eval_X]
      exact sub_pos.mpr (hl.trans_lt (zero_lt_one.trans_le y1))
    rw [split, eval_mul, ← mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg left right.le
  · have right : mu x*R.eval x≤0 := by
      simpa only [incoming, mul_one, R, rightChosen] using
        switched_side_nonpos mu false (rightOutward T)
          ((rightSites T).sort_nodup (· ≤ ·)) (right_order T) x (mem_rightOutward.mpr ⟨ht,hr⟩)
    have left : 0<L.eval x := by
      apply mask_pos_from_factors
      intro y hy
      have y0 := (left_data hy).2
      rw [exteriorLinear, if_pos y0, eval_sub, eval_X, eval_C]
      exact sub_pos.mpr (y0.trans_lt (zero_lt_one.trans_le hr))
    rw [split, eval_mul, mul_comm (L.eval x) (R.eval x), ← mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg right left.le

theorem effectivePositive_switchMask (T : Finset K) (mu : K → K) :
    effectivePositive (switchMask T mu) T mu =
      (T \ exteriorSites T).filter (fun x => 0 < mu x) := by
  have inside {x : K} (hx : x∈T) (off : x∉exteriorSites T) :
      x∈Set.Ioo (0:K) 1 :=
    ⟨lt_of_not_ge (fun h => off (Finset.mem_filter.mpr ⟨hx,Or.inl h⟩)),
      lt_of_not_ge (fun h => off (Finset.mem_filter.mpr ⟨hx,Or.inr h⟩))⟩
  have pos {x : K} (hx : x∈T) (off : x∉exteriorSites T) :
      0 < (switchMask T mu).eval x := exteriorMask_pos (selected_outside T mu) (inside hx off)
  ext x
  simp only [effectivePositive, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hx, hp⟩
    have off : x∉exteriorSites T :=
      fun he => (not_lt_of_ge (switchMask_exterior_nonpos (mu:=mu) he)) hp
    exact ⟨⟨hx,off⟩, (mul_pos_iff_of_pos_right (pos hx off)).mp hp⟩
  · rintro ⟨⟨hx,off⟩,hp⟩
    exact ⟨hx, mul_pos hp (pos hx off)⟩

end ExteriorSwitch

open ExteriorSwitch

/-- All-order diagnostic on the actual signed measure, with one charge per
outward sign switch (plus a positive initial sign), not per exterior atom. -/
theorem UnitLaw.exterior_sign_switch_budget {T : Finset K} {mu : K → K} {b : ℕ}
    (law : UnitLaw T mu b) :
    b+1 ≤ 2*((T \ exteriorSites T).filter (fun x => 0 < mu x)).card+
      exteriorSignSwitchCost T mu := by
  have positive : ∀ P : K[X], P≠0 → 0 < mass (switchMask T mu * P^2) := by
    intro P pn
    exact mass_exteriorMask_sq_pos (ExteriorSwitch.selected_outside T mu) pn
  have bound := law.positive_localizer_budget (switchMask T mu) positive
  rw [switchMask_degree, effectivePositive_switchMask] at bound
  exact bound.trans_eq (Nat.add_comm _ _)

end
end RKCert.ReviewedNative.FormalSignedQuadrature
