module

public import RKResearch.OrderConditions
public import RKCert.ReviewedNative.RationalThreeSiteDiscriminant
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Cast.CharZero

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Four active sites for order-five quadrature with rational active abscissae

Repeated raw nodes are grouped before discarding a zero aggregate weight.
The input is the reviewed bushy-moment law, or any quadrature rule with those
same moments. There is no triangularity, distinctness of raw stages, order
on the coefficient field, or positivity assumption. Noncontributing
abscissae are not required to be rational. -/

namespace RKResearch

open scoped BigOperators Matrix Classical

noncomputable section

section Grouping

variable {ι X K : Type*} [Fintype ι] [AddCommMonoid K]

/-- The weight carried by the whole fiber of a site, with cancellation. -/
def quadratureSiteWeight (b : ι → K) (c : ι → X) (x : X) : K :=
  ∑ i ∈ Finset.univ.filter (fun i => c i = x), b i

/-- The distinct sites whose aggregate weight is not zero. -/
def activeQuadratureSites (b : ι → K) (c : ι → X) : Finset X :=
  (Finset.univ.image c).filter (fun x => quadratureSiteWeight b c x ≠ 0)

theorem mem_activeQuadratureSites_iff {b : ι → K} {c : ι → X} {x : X} :
    x ∈ activeQuadratureSites b c ↔
      (∃ i, c i = x) ∧ quadratureSiteWeight b c x ≠ 0 := by
  simp only [activeQuadratureSites, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]

end Grouping

/-- Every weighted test can be grouped at the exact active sites.
The lemma does not require an additive, polynomial, or injective test. -/
theorem weighted_sum_eq_activeQuadratureSites {ι X K : Type*} [Fintype ι] [Semiring K]
    (b : ι → K) (c : ι → X) (f : X → K) :
    (∑ i, b i * f (c i)) =
      ∑ x ∈ activeQuadratureSites b c, quadratureSiteWeight b c x * f x := by
  let T : Finset X := Finset.univ.image c
  have hr (i : ι) (hi : i ∈ (Finset.univ : Finset ι)) : c i ∈ T :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  calc
    (∑ i, b i * f (c i)) =
        ∑ x ∈ T, ∑ i ∈ Finset.univ.filter (fun i => c i = x), b i * f (c i) :=
      (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T) (g := c)
        hr (fun i => b i * f (c i))).symm
    _ = ∑ x ∈ T, quadratureSiteWeight b c x * f x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [quadratureSiteWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by
      symm
      apply Finset.sum_subset (show activeQuadratureSites b c ⊆ T from Finset.filter_subset _ _)
      intro x hx hnot
      have hz : quadratureSiteWeight b c x = 0 := by
        by_contra hn
        apply hnot
        change x ∈ T.filter (fun y => quadratureSiteWeight b c y ≠ 0)
        exact Finset.mem_filter.mpr ⟨hx, hn⟩
      rw [hz, zero_mul]

section MomentLaw

open Certified.RationalQuadratureFive

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- A small finite set of rational sites is covered by a possibly repeated
rational triple; zero may be chosen when the set is empty. -/
private theorem rat_triple_cover {T : Finset K} (hcard : T.card ≤ 3)
    (hrat : ∀ x ∈ T, ∃ r : ℚ, x = (r : K)) :
    ∃ r u v : ℚ, ∀ x ∈ T, x = (r : K) ∨ x = (u : K) ∨ x = (v : K) := by
  have h : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases h with h | h | h | h
  · have hT := Finset.card_eq_zero.mp h
    exact ⟨0, 0, 0, by simp [hT]⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨r, hr⟩ := hrat a (Finset.mem_singleton_self a)
    refine ⟨r, r, r, ?_⟩
    intro x hx
    exact Or.inl ((Finset.mem_singleton.mp hx).trans hr)
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    obtain ⟨r, hr⟩ := hrat a (by simp)
    obtain ⟨u, hu⟩ := hrat b (by simp)
    refine ⟨r, u, u, ?_⟩
    intro x hx
    have h' : x = a ∨ x = b := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    exact h'.elim (fun e => Or.inl (e.trans hr)) (fun e => Or.inr (Or.inl (e.trans hu)))
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h
    obtain ⟨r, hr⟩ := hrat a (by simp)
    obtain ⟨u, hu⟩ := hrat b (by simp)
    obtain ⟨v, hv⟩ := hrat c (by simp)
    refine ⟨r, u, v, ?_⟩
    intro x hx
    have h' : x = a ∨ x = b ∨ x = c := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases h' with e | e | e
    · exact Or.inl (e.trans hr)
    · exact Or.inr (Or.inl (e.trans hu))
    · exact Or.inr (Or.inr (e.trans hv))

omit [CharZero K] in
private def siteMass (T : Finset K) (μ : K → K) : (K → K) →ₗ[K] K where
  toFun f := ∑ x ∈ T, μ x * f x
  map_add' f g := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- An exact grouped unit rule through degree four with rational sites has
at least four sites. The weights may be arbitrary in a char-zero field. -/
theorem four_le_of_rational_grouped_unit_moments_five (T : Finset K) (μ : K → K)
    (hrat : ∀ x ∈ T, ∃ q : ℚ, x = (q : K))
    (law : ∀ k : ℕ, k ≤ 4 →
      (∑ x ∈ T, μ x * x^k) = 1 / ((k+1 : ℕ) : K)) : 4 ≤ T.card := by
  by_contra h
  obtain ⟨r, u, v, cover⟩ := rat_triple_cover (by omega : T.card ≤ 3) hrat
  let F := siteMass T μ
  let mon (k : ℕ) : K → K := fun x => x^k
  let P : K → K := fun x => (x - (r : K)) * (x - (u : K)) * (x - (v : K))
  let a : K := (r : K) + (u : K) + (v : K)
  let b : K := (r : K)*(u : K) + (r : K)*(v : K) + (u : K)*(v : K)
  let c : K := (r : K)*(u : K)*(v : K)
  have vanish (f : K → K) : F (fun x => f x * P x) = 0 := by
    change (∑ x ∈ T, μ x * (f x * P x)) = 0
    apply Finset.sum_eq_zero
    intro x hx
    rcases cover x hx with hx | hx | hx <;> simp [P, hx]
  have hA := vanish (fun _ => 1)
  simp only [one_mul] at hA
  have hB := vanish (mon 1)
  have hP : P = mon 3 - a • mon 2 + b • mon 1 - c • mon 0 := by
    funext x
    simp only [P, mon, a, b, c, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hXP : (fun x => mon 1 x * P x) = mon 4 - a • mon 3 + b • mon 2 - c • mon 1 := by
    funext x
    simp only [P, mon, a, b, c, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have moment (k : ℕ) (hk : k ≤ 4) : F (mon k) = 1 / ((k+1 : ℕ) : K) := law k hk
  have m0 : F (mon 0) = 1 := by simpa using moment 0 (by decide)
  have m1 : F (mon 1) = 1 / 2 := by simpa using moment 1 (by decide)
  have m2 : F (mon 2) = 1 / 3 := by simpa using moment 2 (by decide)
  have m3 : F (mon 3) = 1 / 4 := by simpa using moment 3 (by decide)
  have m4 : F (mon 4) = 1 / 5 := by simpa using moment 4 (by decide)
  rw [hP] at hA
  rw [hXP] at hB
  have h0K : threeNodeUnitMean (r : K) (u : K) (v : K) = 0 := by
    simpa only [map_add, map_sub, map_smul, smul_eq_mul, m0, m1, m2, m3, mul_one,
      threeNodeUnitMean, a, b, c] using hA
  have h1K : threeNodeUnitXMean (r : K) (u : K) (v : K) = 0 := by
    simpa only [map_add, map_sub, map_smul, smul_eq_mul, m1, m2, m3, m4,
      threeNodeUnitXMean, a, b, c] using hB
  have h0 : threeNodeUnitMean r u v = 0 := by
    apply Rat.cast_injective (α := K)
    change Rat.castHom K (threeNodeUnitMean r u v) = Rat.castHom K 0
    simp only [threeNodeUnitMean, map_zero, map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat]
    simpa only [Rat.coe_castHom, threeNodeUnitMean] using h0K
  have h1 : threeNodeUnitXMean r u v = 0 := by
    apply Rat.cast_injective (α := K)
    change Rat.castHom K (threeNodeUnitXMean r u v) = Rat.castHom K 0
    simp only [threeNodeUnitXMean, map_zero, map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat]
    simpa only [Rat.coe_castHom, threeNodeUnitXMean] using h1K
  exact no_rational_unit_three_roots r u v h0 h1

end MomentLaw

section Native

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K] {p : ℕ}

/-- Direct quadrature interface. Only the contributing sites must be
rational, and every repeated node is counted at its aggregate weight. -/
theorem HasQuadratureOrder.four_le_activeQuadratureSites_of_rat
    {b c : ι → K} (ho : HasQuadratureOrder p b c) (hp : 5 ≤ p)
    (hrat : ∀ x ∈ activeQuadratureSites b c, ∃ q : ℚ, x = (q : K)) :
    4 ≤ (activeQuadratureSites b c).card := by
  apply four_le_of_rational_grouped_unit_moments_five _ _ hrat
  intro k hk
  rw [← weighted_sum_eq_activeQuadratureSites b c (fun x => x^k)]
  have hPay : k + 1 ≤ p := by omega
  have he : ((k+1 : ℕ) : K) * (∑ i, b i * (c i)^k) = 1 := by
    simpa only [dotProduct, Pi.pow_apply] using ho k hPay
  exact (eq_div_iff (ho.isUnit (Nat.succ_pos k) hPay).ne_zero).mpr
    (by simpa only [mul_comm] using he)

/-- The native RK specialization uses only the reviewed bushy trees at the
physical abscissae `A *ᵥ 1`. All other tree and tableau assumptions are
unnecessary in this argument. -/
theorem HasOrder.four_le_activeQuadratureSites_of_rat
    {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder p A b) (hp : 5 ≤ p)
    (hrat : ∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ q : ℚ, x = (q : K)) :
    4 ≤ (activeQuadratureSites b (A *ᵥ 1)).card :=
  ho.hasQuadratureOrder.four_le_activeQuadratureSites_of_rat hp hrat

/-- Convenience form when the whole stage-node vector consists of rational
casts, including sites whose aggregate weight vanishes. -/
theorem HasOrder.four_le_activeQuadratureSites_of_rat_nodes
    {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder p A b) (hp : 5 ≤ p)
    (hrat : ∀ i, ∃ q : ℚ, (A *ᵥ 1) i = (q : K)) :
    4 ≤ (activeQuadratureSites b (A *ᵥ 1)).card := by
  apply ho.four_le_activeQuadratureSites_of_rat hp
  intro x hx
  obtain ⟨⟨i, hi⟩, _⟩ := mem_activeQuadratureSites_iff.mp hx
  obtain ⟨q, hq⟩ := hrat i
  exact ⟨q, hi.symm.trans hq⟩

end Native

/-- For matrices and weights over the rationals no separate abscissa
hypothesis is required. -/
theorem HasOrder.four_le_activeQuadratureSites_rat
    {ι : Type*} [Fintype ι] {p : ℕ} {A : Matrix ι ι ℚ} {b : ι → ℚ}
    (ho : HasOrder p A b) (hp : 5 ≤ p) :
    4 ≤ (activeQuadratureSites b (A *ᵥ 1)).card :=
  ho.four_le_activeQuadratureSites_of_rat hp (fun x _ => ⟨x, rfl⟩)

end

end RKResearch
