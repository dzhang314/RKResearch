module

public import RKCert.ReviewedNative.SDIRKSixPaidPhysical
public import RKCert.ReviewedNative.CommonDiagonalGoodScalar
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

public section

/-! # Two small-characteristic obstructions at six stages

Characteristic 7 is excluded over all nontrivial commutative rings.
In characteristic 3533, six stages require a square root of 2077, so
the prime field is excluded. The argument uses the actual chart and
five of its physical clocks, not a search over abstract tableaux.
-/

namespace RKResearch.Certified.Graded.SDIRKSix

open RKCert.ReviewedNative.SDIRKSixReceipts
open scoped Matrix

variable {K : Type*} [Field K]

private theorem cancel_paid_here (h30 : IsUnit (30 : K))
    {n : ℕ} (hn : n ∣ 30 ^ 13) {x : K} (hx : (n : K) * x = 0) : x = 0 :=
  (isUnit_of_dvd_paid_power h30 hn).mul_left_cancel (by simpa only [mul_zero] using hx)

private theorem coefficient_ne (p n : ℕ) [CharP K p] (h : ¬ p ∣ n) : (n : K) ≠ 0 :=
  fun h₀ => h ((CharP.cast_eq_zero_iff K p n).mp h₀)

/-- If only the second multiplier may vanish, the original receipts
still discard the zero-tap, kappa, and degree-twelve alternatives. -/
private theorem restrict_cubic_terminal {A : Matrix (Fin 6) (Fin 6) K} {γ z u v : K}
    (h : SixStageChart A γ z u v)
    (d₁ : (3846112 : K) ≠ 0) (d₃ : (122267206287360000 : K) ≠ 0)
    (d₄ : (6214370355160790146744320000 : K) ≠ 0) :
    factorThree z u v = 0 ∧ hThree z u v = 0 ∧
      vThree z u v = 0 ∧ terminal z u v = 0 := by
  by_cases h₃ : factorThree z u v = 0
  · have hH := cancel_paid_here h.paid (n := 576) (by decide)
      (deriveHThree_mul z u v h.bridge1_zero h.front_zero h₃)
    have hV := cancel_paid_here h.paid (n := 960) (by decide)
      (deriveVThree_mul z u v h.bridge2_zero hH h₃)
    refine ⟨h₃, hH, hV, h.last_zero.resolve_left ?_⟩
    intro hk
    exact d₁ (by simpa only [mul_one] using noThreeKappa_mul z u v hk hV hH h₃)
  · have hguard := mul_ne_zero (pow_ne_zero 2 h.z_ne) h₃
    have hproject := cancel_paid_here h.paid (n := 360) (by decide)
      (project_mul z u v h.bridge1_zero h.front_zero)
    have h₁₂ := (mul_eq_zero.mp hproject).resolve_left hguard
    have hH := (mul_eq_zero.mp (hTwelve_guard_mul_eq_zero h.paid
      h.front_zero h.bridge1_zero)).resolve_left hguard
    have hV := cancel_paid_here h.paid (n := 5529600) (by decide)
      (deriveVTwelve_mul z u v h.bridge2_zero hH h₁₂)
    exfalso
    rcases h.last_zero with hk | ht
    · exact d₃ (by simpa only [mul_one] using noTwelveKappa_mul z u v hk hV hH h₁₂)
    · exact d₄ (by simpa only [mul_one] using noTwelveTerminal_mul z u v ht hV hH h₁₂)

private def terminalSym (z x y : K) : K :=
  y * ((-40 * z^3 + 480 * z^2 - 1600 * z + 1600) * y^2
    + (z^6 - 24 * z^5 + 254 * z^4 - 1420 * z^3 + 4200 * z^2 - 6400 * z + 4000) * x * y
    + (-2 * z^6 + 36 * z^5 - 244 * z^4 + 720 * z^3 - 720 * z^2 - 400 * z + 800) * (x^2 - 2*y)
    + (-z^7 + 22 * z^6 - 216 * z^5 + 1192 * z^4 - 4000 * z^3 + 8640 * z^2 - 11200 * z + 6400) * y
    + (2 * z^7 - 37 * z^6 + 288 * z^5 - 1214 * z^4 + 2860 * z^3 - 3240 * z^2 + 800 * z + 800) * x
    + (-4 * z^7 + 60 * z^6 - 312 * z^5 + 616 * z^4 - 120 * z^3 - 960 * z^2 + 800 * z))

private theorem terminal_as_symmetric (z u v : K) :
    terminal z u v = terminalSym z (u + v) (u*v) := by
  simp only [terminal, terminalSym]
  ring

set_option maxHeartbeats 20000000 in
private theorem terminal_reduction_7 [CharP K 7] {z u v : K}
    (h₃ : factorThree z u v = 0) (hH : hThree z u v = 0)
    (hV : vThree z u v = 0) (ht : terminal z u v = 0) : z = 1 := by
  have hchar : (7 : K) = 0 := CharP.cast_eq_zero K 7
  simp only [factorThree, hThree, vThree] at h₃ hH hV
  have hs : u + v = -2 * z^2 + z + 1 := by
    linear_combination (norm := ring) 1 * hV - (u + v - 5 * z^2 + 63 * z - 49) * hchar
  have hp : u * v = -1 := by
    linear_combination (norm := ring) (1 * u) * hV - 1 * hH -
      (u * v - 3 * z^2 + 40 * z - 31) * hchar
  rw [terminal_as_symmetric, hs, hp] at ht
  simp only [terminalSym] at ht
  have hr : 3 * z^2 + z + 3 = 0 := by
    linear_combination (norm := ring) ht - (z^7 + 3 * z^6 + 3 * z^5 - 3 * z^4 - z^3 - 3 * z^2 + 3 * z - 3) * h₃ -
      (z^10 - 19 * z^9 + 145 * z^8 - 456 * z^7 + 227 * z^6 + 1631 * z^5 - 3559 * z^4 + 2175 * z^3 + 1129 * z^2 - 2063 * z + 779) * hchar
  linear_combination (norm := ring) (2) * h₃ + (-3 * z - 1) * hr -
    (-z^3 - 6 * z^2 + 19 * z - 14) * hchar

set_option maxHeartbeats 20000000 in
private theorem terminal_reduction_3533 [CharP K 3533] {z u v : K}
    (h₃ : factorThree z u v = 0) (hH : hThree z u v = 0)
    (hV : vThree z u v = 0) (ht : terminal z u v = 0) : z = 1645 := by
  have hchar : (3533 : K) = 0 := CharP.cast_eq_zero K 3533
  simp only [factorThree, hThree, vThree] at h₃ hH hV
  have hs : u + v = 1329 * z^2 - 55 * z + 43 := by
    linear_combination (norm := ring) 1325 * hV - (3 * u + 3 * v - 12 * z^2 + 165 * z - 129) * hchar
  have hp : u * v = -439 * z^2 - 35 * z + 27 := by
    linear_combination (norm := ring) (1325 * u) * hV - 1325 * hH -
      (3 * u * v - 8 * z^2 + 105 * z - 81) * hchar
  rw [terminal_as_symmetric, hs, hp] at ht
  simp only [terminalSym] at ht
  have hr : -1632 * z^2 + 366 * z - 995 = 0 := by
    linear_combination (norm := ring) ht - (84 * z^9 - 383 * z^8 + 1756 * z^7 - 678 * z^6 + 1318 * z^5 - 1331 * z^4 + 362 * z^3 - 1656 * z^2 - 1018 * z - 251) * h₃ -
      (511431 * z^12 - 9633891 * z^11 + 71782763 * z^10 - 257879186 * z^9 + 438019493 * z^8 - 295986879 * z^7 + 3739828 * z^6 + 62843510 * z^5 - 20780666 * z^4 - 295085 * z^3 + 586914 * z^2 - 292126 * z + 56959) * hchar
  linear_combination (norm := ring) (-906) * h₃ + (1701 * z - 1414) * hr -
    (-786 * z^3 + 834 * z^2 - 644 * z + 411) * hchar

/-- In characteristic 7 the chart over any field, including any algebraic
extension, forces z=1 and v=-u with u=±1. -/
private theorem chart_char7 [CharP K 7] {A : Matrix (Fin 6) (Fin 6) K}
    {γ z u v : K} (h : SixStageChart A γ z u v) :
    z = 1 ∧ v = -u ∧ (u = 1 ∨ u = -1) := by
  obtain ⟨h₃, hH, hV, ht⟩ := restrict_cubic_terminal h
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 7 3846112 (by decide))
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 7 122267206287360000 (by decide))
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 7 6214370355160790146744320000 (by decide))
  have hz := terminal_reduction_7 h₃ hH hV ht
  have hchar : (7 : K) = 0 := CharP.cast_eq_zero K 7
  subst z
  simp only [hThree] at hH
  simp only [vThree] at hV
  have hv : v = -u := by linear_combination (norm := ring) hV - (u + v + 9) * hchar
  have hu : (u - 1) * (u + 1) = 0 := by
    linear_combination (norm := ring) hH - (u^2 + 9*u - 6) * hchar
  exact ⟨rfl, hv, (mul_eq_zero.mp hu).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left⟩

/-- Discriminant necessary for a six-stage tableau, over every field
of characteristic 3533, without enumerating field elements or using
a characteristic-zero or algebraic-closure assumption. -/
private theorem chart_char3533 [CharP K 3533] {A : Matrix (Fin 6) (Fin 6) K}
    {γ z u v : K} (h : SixStageChart A γ z u v) :
    ∃ x : K, x^2 = 2077 := by
  obtain ⟨h₃, hH, hV, ht⟩ := restrict_cubic_terminal h
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 3533 3846112 (by decide))
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 3533 122267206287360000 (by decide))
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 3533 6214370355160790146744320000 (by decide))
  have hz := terminal_reduction_3533 h₃ hH hV ht
  have hchar : (3533 : K) = 0 := CharP.cast_eq_zero K 3533
  subst z
  simp only [hThree] at hH
  refine ⟨2 * u - 824, ?_⟩
  linear_combination (norm := ring) 1767 * hH - (4 * u^2 - 44300219 * u + 28190856) * hchar

private def moment (b c : Fin 6 → K) (j : ℕ) : K := b ⬝ᵥ c ^ j

private theorem moment_values_char7 [CharP K 7] {b c : Fin 6 → K}
    (h : HasQuadratureOrder 6 b c) :
    moment b c 1 = 4 ∧ moment b c 2 = 5 ∧ moment b c 3 = 2 ∧
      moment b c 4 = 3 ∧ moment b c 5 = 6 := by
  have hchar : (7 : K) = 0 := CharP.cast_eq_zero K 7
  have t₁ : (2 : K) * moment b c 1 = 1 := h 1 (by decide)
  have t₂ : (3 : K) * moment b c 2 = 1 := h 2 (by decide)
  have t₃ : (4 : K) * moment b c 3 = 1 := h 3 (by decide)
  have t₄ : (5 : K) * moment b c 4 = 1 := h 4 (by decide)
  have t₅ : (6 : K) * moment b c 5 = 1 := h 5 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination 4*t₁ - moment b c 1 * hchar
  · linear_combination 5*t₂ - 2*moment b c 2 * hchar
  · linear_combination 2*t₃ - moment b c 3 * hchar
  · linear_combination 3*t₄ - 2*moment b c 4 * hchar
  · linear_combination 6*t₅ - 5*moment b c 5 * hchar

/-- Two moments of a polynomial vanishing at five prescribed clocks
rule out any choice of the sixth if its only possible value is
itself a root of the polynomial. -/
private theorem one_free_clock_excluded {b c : Fin 6 → K}
    (P : K → K) {r : K} (hne : r ≠ 0) (hp₁ : P 1 = 0)
    (hrest : ∀ i, i ≠ 3 → P (c i) = 0)
    (hPb : (∑ i, b i * P (c i)) = r)
    (hCPb : (∑ i, b i * (c i * P (c i))) = r) : False := by
  have weighted_eq (f : K → K) (hf : ∀ i, i ≠ 3 → f (c i) = 0) :
      (∑ i, b i * f (c i)) = b 3 * f (c 3) := by
    apply Finset.sum_eq_single
    · intro i _ hi
      rw [hf i hi, mul_zero]
    · simp
  have h0 : b 3 * P (c 3) = r := (weighted_eq P hrest).symm.trans hPb
  have h1 : b 3 * (c 3 * P (c 3)) = r :=
    (weighted_eq (fun x => x * P x) (fun i hi => by rw [hrest i hi, mul_zero])).symm.trans hCPb
  have hr : (c 3 - 1) * r = 0 := by linear_combination h1 - c 3 * h0
  have hc : c 3 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hne)
  rw [hc, hp₁, mul_zero] at h0
  exact hne h0.symm

private theorem no_quadrature_char7_plus [CharP K 7] {b c : Fin 6 → K}
    (h : HasQuadratureOrder 6 b c)
    (c₀ : c 0 = 1) (c₁ : c 1 = 2) (c₂ : c 2 = 3) (c₄ : c 4 = 1) (c₅ : c 5 = 0) :
    False := by
  obtain ⟨m₁,m₂,m₃,m₄,m₅⟩ := moment_values_char7 h
  have hchar : (7 : K) = 0 := CharP.cast_eq_zero K 7
  let P := fun x : K => x * (x-1) * (x-2) * (x-3)
  refine one_free_clock_excluded (b := b) (c := c) P (r := 1) one_ne_zero (by dsimp [P]; ring) ?_ ?_ ?_
  · intro i hi
    fin_cases i <;> simp [P,c₀,c₁,c₂,c₄,c₅] at *
  · simp only [P, moment, dotProduct, Pi.pow_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at *
    linear_combination (norm := ring) m₄ - 6*m₃ + 11*m₂ - 6*m₁ + 3*hchar
  · simp only [P, moment, dotProduct, Pi.pow_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at *
    linear_combination (norm := ring) m₅ - 6*m₄ + 11*m₃ - 6*m₂ - 3*hchar

private theorem no_quadrature_char7_minus [CharP K 7] {b c : Fin 6 → K}
    (h : HasQuadratureOrder 6 b c)
    (c₀ : c 0 = 1) (c₁ : c 1 = 0) (c₂ : c 2 = -1) (c₄ : c 4 = -1) (c₅ : c 5 = 0) :
    False := by
  obtain ⟨m₁,m₂,m₃,m₄,-⟩ := moment_values_char7 h
  have hchar : (7 : K) = 0 := CharP.cast_eq_zero K 7
  let P := fun x : K => x * (x-1) * (x+1)
  refine one_free_clock_excluded (b := b) (c := c) P (r := 5)
    (by simpa only [Nat.cast_ofNat] using coefficient_ne (K := K) 7 5 (by decide))
    (by dsimp [P]; ring) ?_ ?_ ?_
  · intro i hi
    fin_cases i <;> simp [P,c₀,c₁,c₂,c₄,c₅] at *
  · simp only [P, moment, dotProduct, Pi.pow_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at *
    linear_combination (norm := ring) m₃ - m₁ - hchar
  · simp only [P, moment, dotProduct, Pi.pow_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at *
    linear_combination (norm := ring) m₄ - m₂ - hchar

/-- No six-stage strict tableau over any characteristic-seven field. -/
theorem order_six_six_stages_impossible_char_seven [CharP K 7]
    {A : Matrix (Fin 6) (Fin 6) K} {b : Fin 6 → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (hγ : γ ≠ 0) : False := by
  obtain ⟨z,u,v,h⟩ := order_six_six_stage_chart ho ha he hγ
  obtain ⟨rfl,rfl,hu⟩ := chart_char7 h
  have hclock : nodes (scaleTable (1 : K) A) = A *ᵥ 1 := by
    rw [nodes_scaleTable, one_smul]
  have q := ho.hasQuadratureOrder
  rw [← hclock] at q
  rcases hu with rfl | rfl
  · exact no_quadrature_char7_plus q h.clock₀
      (by rw [h.clock₁]; ring) (by rw [h.clock₂]; ring)
      (by rw [h.clock₄]; ring) (by rw [h.clock₅]; ring)
  · exact no_quadrature_char7_minus q h.clock₀
      (by rw [h.clock₁]; ring) (by rw [h.clock₂]; ring)
      (by rw [h.clock₄]; ring) (by rw [h.clock₅]; ring)

theorem seven_le_of_strict_order_six_char_seven [CharP K 7] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (hγ : γ ≠ 0) : 7 ≤ s := by
  have h₆ := nonsingular_stageFloor_field ho ha (fun i => he i ▸ hγ) (by decide)
  change 6 ≤ s at h₆
  by_contra hsmall
  have hs : s = 6 := by omega
  subst s
  exact order_six_six_stages_impossible_char_seven ho ha he hγ

/-- Every characteristic-3533 field missing the indicated square root
has the stricter floor. In particular this is not a uniform
characteristic-3533 statement. -/
theorem seven_le_of_strict_order_six_char3533_of_nonsquare [CharP K 3533] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (hγ : γ ≠ 0) (hdisc : ¬ ∃ x : K, x^2 = 2077) : 7 ≤ s := by
  have h₆ := nonsingular_stageFloor_field ho ha (fun i => he i ▸ hγ) (by decide)
  change 6 ≤ s at h₆
  by_contra hsmall
  have hs : s = 6 := by omega
  subst s
  obtain ⟨z,u,v,h⟩ := order_six_six_stage_chart ho ha he hγ
  exact hdisc (chart_char3533 h)

end RKResearch.Certified.Graded.SDIRKSix

namespace RKResearch

open scoped Matrix
open Certified.Graded.SDIRKSix

private theorem erkFloorSix : erkUniformFloor 6 = 7 := by
  have h := congrArg (fun xs : List ℕ => xs[6]?) erkUniformFloor_through_twenty
  change some (erkUniformFloor 6) = some 7 at h
  exact Option.some.inj h

/-- Seven stages over every nontrivial commutative ring of
characteristic 7. Neither field structure nor a unit common diagonal
is required at the endpoint. -/
theorem HasOrder.common_diagonal_order_six_stages_char_seven
    {R : Type*} [CommRing R] [Nontrivial R] [CharP R 7] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) : 7 ≤ s := by
  have hn : ¬ IsNilpotent (1 : R) := by
    rintro ⟨n, hn⟩
    exact one_ne_zero (by simpa only [one_pow] using hn)
  have hs := ho.common_diagonal_stage_floor_at_scalar (d := (1 : R)) (k := 7) ha he
    (Or.inr hn) (fun K _ f _ ho' ha' he' hg' => by
      have hz : ((7 : ℕ) : K) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg f (CharP.cast_eq_zero R 7)
      let : CharP K 7 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 7)).mpr hz
      exact seven_le_of_strict_order_six_char_seven ho' ha' he' hg')
  simpa only [erkFloorSix, min_self] using hs

local instance : Fact (Nat.Prime 3533) := ⟨by norm_num⟩

private theorem disc_pow_1766 : (2077 : ZMod 3533)^1766 = 3532 := by
  have h1 : (2077 : ZMod 3533)^1 = 2077 := pow_one _
  have h3 : (2077 : ZMod 3533)^3 = 3365 := by
    change (2077 : ZMod 3533)^(1*2+1) = _
    rw [pow_succ, pow_mul, h1]
    decide +kernel
  have h6 : (2077 : ZMod 3533)^6 = 3493 := by
    change (2077 : ZMod 3533)^(3*2) = _
    rw [pow_mul, h3]
    decide +kernel
  have h13 : (2077 : ZMod 3533)^13 = 2180 := by
    change (2077 : ZMod 3533)^(6*2+1) = _
    rw [pow_succ, pow_mul, h6]
    decide +kernel
  have h27 : (2077 : ZMod 3533)^27 = 2689 := by
    change (2077 : ZMod 3533)^(13*2+1) = _
    rw [pow_succ, pow_mul, h13]
    decide +kernel
  have h55 : (2077 : ZMod 3533)^55 = 396 := by
    change (2077 : ZMod 3533)^(27*2+1) = _
    rw [pow_succ, pow_mul, h27]
    decide +kernel
  have h110 : (2077 : ZMod 3533)^110 = 1364 := by
    change (2077 : ZMod 3533)^(55*2) = _
    rw [pow_mul, h55]
    decide +kernel
  have h220 : (2077 : ZMod 3533)^220 = 2138 := by
    change (2077 : ZMod 3533)^(110*2) = _
    rw [pow_mul, h110]
    decide +kernel
  have h441 : (2077 : ZMod 3533)^441 = 605 := by
    change (2077 : ZMod 3533)^(220*2+1) = _
    rw [pow_succ, pow_mul, h220]
    decide +kernel
  have h883 : (2077 : ZMod 3533)^883 = 2985 := by
    change (2077 : ZMod 3533)^(441*2+1) = _
    rw [pow_succ, pow_mul, h441]
    decide +kernel
  have h1766 : (2077 : ZMod 3533)^1766 = 3532 := by
    change (2077 : ZMod 3533)^(883*2) = _
    rw [pow_mul, h883]
    decide +kernel
  exact h1766

private theorem nonsquare_3533 : ¬ ∃ x : ZMod 3533, x^2 = (2077 : ZMod 3533) := by
  rintro ⟨x, hx⟩
  have hn : x ≠ 0 := by
    rintro rfl
    exact (by decide +kernel : (0 : ZMod 3533)^2 ≠ 2077) hx
  have he := congrArg (fun a : ZMod 3533 => a^1766) hx
  change (x^2)^1766 = (2077 : ZMod 3533)^1766 at he
  rw [← pow_mul, disc_pow_1766] at he
  change x^(3533-1) = 3532 at he
  have hu := (pow_card_eq_one' (x := Units.mk0 x hn))
  rw [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card] at hu
  have hval : x^(3533-1) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using
      congrArg (fun a : (ZMod 3533)ˣ => (a : ZMod 3533)) hu
  exact (by decide +kernel : (1 : ZMod 3533) ≠ 3532) (hval.symm.trans he)

/-- Seven stages over the prime field of size 3533, including the
explicit-diagonal specialization if the common diagonal is zero. -/
theorem HasOrder.common_diagonal_order_six_stages_prime_3533 {s : ℕ}
    {A : Matrix (Fin s) (Fin s) (ZMod 3533)} {b : Fin s → ZMod 3533} {γ : ZMod 3533}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ) : 7 ≤ s := by
  by_cases hγ : γ = 0
  · have hu : ¬ IsUnit γ := by rw [hγ]; exact not_isUnit_zero
    simpa only [erkFloorSix] using ho.common_diagonal_erk_floor_of_not_isUnit ha he hu
  · exact seven_le_of_strict_order_six_char3533_of_nonsquare ho ha he hγ nonsquare_3533

/-- The prime-field exclusion transports to every commutative ring
with a unital specialization to that prime field, regardless of the
characteristic or the original common diagonal. -/
theorem HasOrder.common_diagonal_order_six_stages_maps_to_3533
    {R : Type*} [CommRing R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (he : ∀ i, A i i = γ)
    (f : R →+* ZMod 3533) : 7 ≤ s :=
  (ho.map f).common_diagonal_order_six_stages_prime_3533 (ha.map f)
    (fun i => congrArg f (he i))

end RKResearch
