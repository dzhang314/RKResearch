module

public import RKCert.ReviewedNative.PrimeNodalFactorDegree
public import RKCert.ReviewedNative.ReducedHilbertMomentPrimeCut
public import RKCert.ReviewedNative.RationalQuadratureFiveSupport

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Strict prime obstruction for the actual rational support of a dense RK rule

The tree input is just the reviewed bush interface. Equal abscissae
are aggregated before any arithmetic. Rationality is required only
at contributing sites, not for weights or inactive abscissae. -/

namespace RKResearch.Certified.RationalPrimeCut

open Polynomial
open scoped Polynomial BigOperators Classical

/-- A rational finite cover of the active abscissae gives the paid
orthogonality of its actual integral nodal product. The weights
need not descend to the rationals. -/
theorem uniformIntRows_of_grouped_rat_roots {K : Type*} [Field K] [CharZero K]
    (S : Finset K) (μ : K → K) (T : Finset ℚ) {p t : ℕ}
    (cover : ∀ x ∈ S, ∃ r ∈ T, x = (r : K))
    (law : ∀ k : ℕ, k+1 ≤ p → (∑ x ∈ S, μ x * x^k) = 1 / ((k+1 : ℕ) : K))
    (paid : T.card+t ≤ p) :
    ∀ k : ℕ, k < t → UniformIntRowZero (integralRationalNodalHull T).coeff T.card k := by
  intro k hk
  let P := integralRationalNodalHull T
  let I := Finset.range (T.card+1)
  have nd : P.natDegree < T.card+1 :=
    (integralRationalNodalHull_natDegree T).trans_lt (Nat.lt_succ_self _)
  have vanish : (∑ x ∈ S, μ x * x^k * P.eval₂ (Int.castRingHom K) x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨r, hr, e⟩ := cover x hx
    have z : P.eval₂ (Int.castRingHom K) (r : K) = 0 := integralRationalNodalHull_eval₂_zero hr
    rw [e, z, mul_zero]
  have expans :
      (∑ x ∈ S, μ x * x^k * P.eval₂ (Int.castRingHom K) x) =
        ∑ j ∈ I, (P.coeff j : K) * ∑ x ∈ S, μ x * x^(j+k) := by
    calc
      _ = ∑ x ∈ S, ∑ j ∈ I, (P.coeff j : K) * (μ x * x^(j+k)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [eval₂_eq_sum_range' (Int.castRingHom K) nd x, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Int.coe_castRingHom, pow_add]
        ring
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have hK : (∑ j ∈ I, (P.coeff j : K) / ((j+k+1 : ℕ) : K)) = 0 := by
    refine Eq.trans ?_ (expans.symm.trans vanish)
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [law (j+k) (by omega), div_eq_mul_inv, one_mul]
  change (∑ j ∈ I, (P.coeff j : ℚ) / ((j+k+1 : ℕ) : ℚ)) = 0
  apply Rat.cast_injective (α := K)
  change Rat.castHom K (∑ j ∈ I, (P.coeff j : ℚ) / ((j+k+1 : ℕ) : ℚ)) = Rat.castHom K 0
  simpa only [map_sum, map_div₀, map_intCast, map_natCast, map_zero] using hK

theorem exists_split_reducedHilbert_of_integralRationalNodal
    {q t : ℕ} [Fact q.Prime] (T : Finset ℚ) (hnq : T.card < q)
    (hpaid : T.card+t < 2*q)
    (law : ∀ k : ℕ, k < t → UniformIntRowZero (integralRationalNodalHull T).coeff T.card k) :
    ∃ R : (ZMod q)[X], R ≠ 0 ∧ R.Splits ∧ R.natDegree+t < q ∧
      ∀ k : ℕ, k < t → R.natDegree+k+2 < q → UniformZModRowZero q R.coeff R.natDegree k := by
  let P := integralRationalNodalHull T
  let R := P.map (Int.castRingHom (ZMod q))
  obtain ⟨hn, hs, _, budget⟩ := integralRationalNodalHull_mod_profile q T
  have h := reduced_Hilbert_projection P hnq hpaid (integralRationalNodalHull_natDegree T).le
    hn budget law
  refine ⟨R, hn, hs, h.1, ?_⟩
  intro k hk hsafe
  simpa only [UniformZModRowZero, R, coeff_map, Int.coe_castRingHom] using h.2 k hk hsafe

end RKResearch.Certified.RationalPrimeCut

namespace RKResearch

open Certified.RationalPrimeCut
open scoped BigOperators Polynomial Matrix Classical

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K] {p : ℕ}

/-- Reusable projection on the actual active support, allowing one
unpaid reduced row precisely at the degree boundary. -/
theorem HasQuadratureOrder.exists_split_reducedHilbert_of_rat
    {b c : ι → K} (ho : HasQuadratureOrder p b c) {q t : ℕ} [Fact q.Prime]
    (hnq : (activeQuadratureSites b c).card < q)
    (hbound : (activeQuadratureSites b c).card+t < 2*q)
    (hpaid : (activeQuadratureSites b c).card+t ≤ p)
    (hrat : ∀ x ∈ activeQuadratureSites b c, ∃ r : ℚ, x = (r : K)) :
    ∃ R : (ZMod q)[X], R ≠ 0 ∧ R.Splits ∧ R.natDegree+t < q ∧
      ∀ k : ℕ, k < t → R.natDegree+k+2 < q → UniformZModRowZero q R.coeff R.natDegree k := by
  let S := activeQuadratureSites b c
  let ρ (x : S) : ℚ := Classical.choose (hrat x.val x.property)
  have hρ (x : S) : x.val = (ρ x : K) := Classical.choose_spec (hrat x.val x.property)
  have injρ : Function.Injective ρ := by
    intro x y exy
    apply Subtype.ext
    exact (hρ x).trans ((congrArg (fun r : ℚ => (r : K)) exy).trans (hρ y).symm)
  let T := (Finset.univ : Finset S).image ρ
  have hT : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ injρ, Finset.card_univ, Fintype.card_coe]
  have cover (x : K) (hx : x ∈ S) : ∃ r ∈ T, x = (r : K) := by
    let y : S := ⟨x,hx⟩
    exact ⟨ρ y, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩, hρ y⟩
  have legal (k : ℕ) (hk : k+1 ≤ p) :
      (∑ x ∈ S, quadratureSiteWeight b c x * x^k) = 1 / ((k+1 : ℕ) : K) := by
    change (∑ x ∈ activeQuadratureSites b c, quadratureSiteWeight b c x * x^k) = _
    rw [← weighted_sum_eq_activeQuadratureSites b c (fun x => x^k)]
    have raw : ((k+1 : ℕ) : K) * (∑ i, b i * (c i)^k) = 1 := by
      simpa only [dotProduct, Pi.pow_apply] using ho k hk
    exact (eq_div_iff (ho.isUnit (Nat.succ_pos k) hk).ne_zero).mpr
      (by simpa only [mul_comm] using raw)
  exact exists_split_reducedHilbert_of_integralRationalNodal T
    (by rw [hT]; exact hnq) (by rw [hT]; exact hbound)
    (uniformIntRows_of_grouped_rat_roots S (quadratureSiteWeight b c) T cover legal
      (by rw [hT]; exact hpaid))

/-- For rational active sites, the width cannot lie below a prime
that is strictly less than twice the order surplus. To isolate
one denominator pole the proof discards unneeded high tests. -/
theorem HasQuadratureOrder.no_strict_prime_support_gap_of_rat
    {b c : ι → K} (ho : HasQuadratureOrder p b c) {q : ℕ} (hPrime : q.Prime)
    (hrat : ∀ x ∈ activeQuadratureSites b c, ∃ r : ℚ, x = (r : K))
    (hnq : (activeQuadratureSites b c).card < q)
    (hgap : q < 2*(p-(activeQuadratureSites b c).card)) : False := by
  let : Fact q.Prime := ⟨hPrime⟩
  let n := (activeQuadratureSites b c).card
  let t := min (p-n) q
  have hnq' : n < q := hnq
  have hgap' : q < 2*(p-n) := hgap
  have hpos := hPrime.pos
  have hbound : n+t < 2*q := by
    have ht : t ≤ q := Nat.min_le_right _ _
    omega
  have hpay : n+t ≤ p := by
    have ht : t ≤ p-n := Nat.min_le_left _ _
    omega
  have hG : q < 2*t := by
    rcases le_total (p-n) q with h | h
    · simpa only [t, Nat.min_eq_left h] using hgap'
    · simp only [t, Nat.min_eq_right h]
      omega
  obtain ⟨R, hn, _, hc, law⟩ :=
    ho.exists_split_reducedHilbert_of_rat (q := q) (t := t) hnq hbound hpay hrat
  exact strict_prime_Hilbert_of_projection R hn hc hG law

/-- The strict floor contributed by any prime. It concerns the
distinct contributing sites, not the full stage count. -/
theorem HasOrder.prime_floor_activeQuadratureSites_of_rat
    {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder p A b) (q : ℕ) (hPrime : q.Prime)
    (hrat : ∀ x ∈ activeQuadratureSites b (A *ᵥ 1), ∃ r : ℚ, x = (r : K)) :
    min q (p-q/2) ≤ (activeQuadratureSites b (A *ᵥ 1)).card := by
  by_contra h
  have h1 := min_le_left q (p-q/2)
  have h2 := min_le_right q (p-q/2)
  exact ho.hasQuadratureOrder.no_strict_prime_support_gap_of_rat hPrime hrat
    (by omega) (by omega)

/-- Rational coefficient specialization; the abscissa premise is automatic. -/
theorem HasOrder.prime_floor_activeQuadratureSites_rat
    {ι : Type*} [Fintype ι] {p : ℕ} {A : Matrix ι ι ℚ} {b : ι → ℚ}
    (ho : HasOrder p A b) (q : ℕ) (hPrime : q.Prime) :
    min q (p-q/2) ≤ (activeQuadratureSites b (A *ᵥ 1)).card :=
  ho.prime_floor_activeQuadratureSites_of_rat q hPrime (fun x _ => ⟨x, rfl⟩)

end
end RKResearch
