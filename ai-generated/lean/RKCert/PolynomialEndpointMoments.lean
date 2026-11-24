module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Two noncoincident endpoints over a characteristic-zero field

These are formal polynomial moments, not integrals over an ordered interval.
A coefficient vector represents a polynomial of degree AT MOST the displayed
degree; no monic normalization is assumed. All eliminations are ring identities.
No stage-space or flat-band extraction is assumed by these scalar results.
-/
namespace RKCert.Endpoint
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K] [CharZero K]

/-- For coefficients in ascending order: the formal integral of x^k P(x)
from zero to u. Each denominator is a nonzero natural number in the field. -/
def moment {n : ℕ} (c : Fin n → K) (u : K) (k : ℕ) : K :=
  ∑ i : Fin n, c i * u ^ (i.val + k + 1) / (i.val+k+1 : ℕ)

/-- Unit-endpoint moment tests of x P(x) against the first d monomials,
and two tests at a against x(x-1) and x²(x-1). -/
def twoTests {n : ℕ} (c : Fin n → K) (a : K) (d : ℕ) : Prop :=
  (∀ k : Fin d, moment c 1 (k.val+1) = 0) ∧
  (moment c a 2 - moment c a 1 = 0) ∧
  (moment c a 3 - moment c a 2 = 0)


/-- Degree ≤ 3: 3 first-endpoint tests and just TWO second-endpoint tests force the zero polynomial. -/
theorem match3 (c : Fin 4 → K) (a : K) (ha : a ≠ 0) (h1a : a ≠ 1)
    (h : twoTests c a 3) : c = 0 := by
  have h1 : c 0 / 2 + c 1 / 3 + c 2 / 4 + c 3 / 5 = 0 := by
    have hh := h.1 (0 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h2 : c 0 / 3 + c 1 / 4 + c 2 / 5 + c 3 / 6 = 0 := by
    have hh := h.1 (1 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h3 : c 0 / 4 + c 1 / 5 + c 2 / 6 + c 3 / 7 = 0 := by
    have hh := h.1 (2 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have e1 : (c 0 * a ^ 3 / 3 + c 1 * a ^ 4 / 4 + c 2 * a ^ 5 / 5 + c 3 * a ^ 6 / 6) - (c 0 * a ^ 2 / 2 + c 1 * a ^ 3 / 3 + c 2 * a ^ 4 / 4 + c 3 * a ^ 5 / 5) = 0 := by
    have hh := h.2.1
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have e2 : (c 0 * a ^ 4 / 4 + c 1 * a ^ 5 / 5 + c 2 * a ^ 6 / 6 + c 3 * a ^ 7 / 7) - (c 0 * a ^ 3 / 3 + c 1 * a ^ 4 / 4 + c 2 * a ^ 5 / 5 + c 3 * a ^ 6 / 6) = 0 := by
    have hh := h.2.2
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have c0 : c 0 = (-4 / 35) * c 3 := by linear_combination 72 * h1 + (-240) * h2 + 180 * h3
  have c1 : c 1 = (6 / 7) * c 3 := by linear_combination (-240) * h1 + 900 * h2 + (-720) * h3
  have c2 : c 2 = (-12 / 7) * c 3 := by linear_combination 180 * h1 + (-720) * h2 + 600 * h3
  have hn : a - 1 ≠ 0 := sub_ne_zero.mpr h1a
  have z1 : (c 3 * ((35 * (a ^ 2)) + ((-1) * 44 * a) + 12)) * (a ^ 2 * (a - 1)^2) = 0 := by
    rw [c0, c1, c2] at e1
    linear_combination 210 * e1
  have p1 : c 3 * ((35 * (a ^ 2)) + ((-1) * 44 * a) + 12) = 0 := (mul_eq_zero.mp z1).resolve_right (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
  have z2 : (c 3 * ((30 * (a ^ 2)) + ((-1) * 35 * a) + 8)) * (a ^ 3 * (a - 1)^2) = 0 := by
    rw [c0, c1, c2] at e2
    linear_combination 210 * e2
  have p2 : c 3 * ((30 * (a ^ 2)) + ((-1) * 35 * a) + 8) = 0 := (mul_eq_zero.mp z2).resolve_right (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
  have z : c 3 = 0 := by linear_combination ((185 / 12) + ((-1) * (95 / 2) * a)) * p1 + (((665 / 12) * a) + (-23)) * p2
  funext i; fin_cases i <;> simp_all

/-- Degree ≤ 4: 4 first-endpoint tests and just TWO second-endpoint tests force the zero polynomial. -/
theorem match4 (c : Fin 5 → K) (a : K) (ha : a ≠ 0) (h1a : a ≠ 1)
    (h : twoTests c a 4) : c = 0 := by
  have h1 : c 0 / 2 + c 1 / 3 + c 2 / 4 + c 3 / 5 + c 4 / 6 = 0 := by
    have hh := h.1 (0 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h2 : c 0 / 3 + c 1 / 4 + c 2 / 5 + c 3 / 6 + c 4 / 7 = 0 := by
    have hh := h.1 (1 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h3 : c 0 / 4 + c 1 / 5 + c 2 / 6 + c 3 / 7 + c 4 / 8 = 0 := by
    have hh := h.1 (2 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h4 : c 0 / 5 + c 1 / 6 + c 2 / 7 + c 3 / 8 + c 4 / 9 = 0 := by
    have hh := h.1 (3 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have e1 : (c 0 * a ^ 3 / 3 + c 1 * a ^ 4 / 4 + c 2 * a ^ 5 / 5 + c 3 * a ^ 6 / 6 + c 4 * a ^ 7 / 7) - (c 0 * a ^ 2 / 2 + c 1 * a ^ 3 / 3 + c 2 * a ^ 4 / 4 + c 3 * a ^ 5 / 5 + c 4 * a ^ 6 / 6) = 0 := by
    have hh := h.2.1
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have e2 : (c 0 * a ^ 4 / 4 + c 1 * a ^ 5 / 5 + c 2 * a ^ 6 / 6 + c 3 * a ^ 7 / 7 + c 4 * a ^ 8 / 8) - (c 0 * a ^ 3 / 3 + c 1 * a ^ 4 / 4 + c 2 * a ^ 5 / 5 + c 3 * a ^ 6 / 6 + c 4 * a ^ 7 / 7) = 0 := by
    have hh := h.2.2
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have c0 : c 0 = (5 / 126) * c 4 := by linear_combination 200 * h1 + (-1200) * h2 + 2100 * h3 + (-1120) * h4
  have c1 : c 1 = (-10 / 21) * c 4 := by linear_combination (-1200) * h1 + 8100 * h2 + (-15120) * h3 + 8400 * h4
  have c2 : c 2 = (5 / 3) * c 4 := by linear_combination 2100 * h1 + (-15120) * h2 + 29400 * h3 + (-16800) * h4
  have c3 : c 3 = (-20 / 9) * c 4 := by linear_combination (-1120) * h1 + 8400 * h2 + (-16800) * h3 + 9800 * h4
  have hn : a - 1 ≠ 0 := sub_ne_zero.mpr h1a
  have z1 : (c 4 * ((108 * (a ^ 3)) + ((-1) * 190 * (a ^ 2)) + (100 * a) + (-15))) * (a ^ 2 * (a - 1)^2) = 0 := by
    rw [c0, c1, c2, c3] at e1
    linear_combination 756 * e1
  have p1 : c 4 * ((108 * (a ^ 3)) + ((-1) * 190 * (a ^ 2)) + (100 * a) + (-15)) = 0 := (mul_eq_zero.mp z1).resolve_right (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
  have z2 : (c 4 * ((189 * (a ^ 3)) + ((-1) * 318 * (a ^ 2)) + (155 * a) + (-20))) * (a ^ 3 * (a - 1)^2) = 0 := by
    rw [c0, c1, c2, c3] at e2
    linear_combination 1512 * e2
  have p2 : c 4 * ((189 * (a ^ 3)) + ((-1) * 318 * (a ^ 2)) + (155 * a) + (-20)) = 0 := (mul_eq_zero.mp z2).resolve_right (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
  have z : c 4 = 0 := by linear_combination (((-1) * (6678 / 29) * (a ^ 2)) + ((27704 / 145) * a) + (-13069 / 435)) * p1 + (((3816 / 29) * (a ^ 2)) + ((-1) * (51884 / 435) * a) + (652 / 29)) * p2
  funext i; fin_cases i <;> simp_all

/-- With a free quartic and only three first-endpoint tests, the alternative
is exact and meaningful over NONordered fields.  We do not discard the
quadratic's two complex roots. -/
theorem quartic_three_two (c : Fin 5 → K) (a : K) (ha : a ≠ 0) (h1a : a ≠ 1)
    (h : twoTests c a 3) : c = 0 ∨ 15 * a^2 - 24 * a + 10 = 0 := by
  have h1 : c 0 / 2 + c 1 / 3 + c 2 / 4 + c 3 / 5 + c 4 / 6 = 0 := by
    have hh := h.1 (0 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h2 : c 0 / 3 + c 1 / 4 + c 2 / 5 + c 3 / 6 + c 4 / 7 = 0 := by
    have hh := h.1 (1 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have h3 : c 0 / 4 + c 1 / 5 + c 2 / 6 + c 3 / 7 + c 4 / 8 = 0 := by
    have hh := h.1 (2 : Fin _)
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have e1 : (c 0 * a ^ 3 / 3 + c 1 * a ^ 4 / 4 + c 2 * a ^ 5 / 5 + c 3 * a ^ 6 / 6 + c 4 * a ^ 7 / 7) - (c 0 * a ^ 2 / 2 + c 1 * a ^ 3 / 3 + c 2 * a ^ 4 / 4 + c 3 * a ^ 5 / 5 + c 4 * a ^ 6 / 6) = 0 := by
    have hh := h.2.1
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have e2 : (c 0 * a ^ 4 / 4 + c 1 * a ^ 5 / 5 + c 2 * a ^ 6 / 6 + c 3 * a ^ 7 / 7 + c 4 * a ^ 8 / 8) - (c 0 * a ^ 3 / 3 + c 1 * a ^ 4 / 4 + c 2 * a ^ 5 / 5 + c 3 * a ^ 6 / 6 + c 4 * a ^ 7 / 7) = 0 := by
    have hh := h.2.2
    norm_num [moment, Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  let t := c 3 - ((-20 / 9)) * c 4
  have c0 : c 0 = (-4 / 35) * t + (5 / 126) * c 4 := by
    dsimp [t]; linear_combination 72 * h1 + (-240) * h2 + 180 * h3
  have c1 : c 1 = (6 / 7) * t + (-10 / 21) * c 4 := by
    dsimp [t]; linear_combination (-240) * h1 + 900 * h2 + (-720) * h3
  have c2 : c 2 = (-12 / 7) * t + (5 / 3) * c 4 := by
    dsimp [t]; linear_combination 180 * h1 + (-720) * h2 + 600 * h3
  have c3 : c 3 = t + (-20 / 9) * c 4 := by dsimp [t]; ring
  have p1 : (t * ((630 * (a ^ 2)) + ((-1) * 792 * a) + 216) + c 4 * ((540 * (a ^ 3)) + ((-1) * 950 * (a ^ 2)) + (500 * a) + (-75))) * (a ^ 2 * (a - 1)^2) = 0 := by
    rw [c0,c1,c2,c3] at e1
    linear_combination 3780 * e1
  have q1 := (mul_eq_zero.mp p1).resolve_right (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ (sub_ne_zero.mpr h1a)))
  have p2 : (t * ((1080 * (a ^ 2)) + ((-1) * 1260 * a) + 288) + c 4 * ((945 * (a ^ 3)) + ((-1) * 1590 * (a ^ 2)) + (775 * a) + (-100))) * (a ^ 3 * (a - 1)^2) = 0 := by
    rw [c0,c1,c2,c3] at e2
    linear_combination 7560 * e2
  have q2 := (mul_eq_zero.mp p2).resolve_right (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ (sub_ne_zero.mpr h1a)))
  have v : c 4 * (a * (a - 1)^2 * (15 * a^2 - 24 * a + 10)) = 0 := by
    linear_combination (((-1) * (4 / 3) * (a ^ 2)) + ((14 / 9) * a) + (-16 / 45)) * q1 + (((7 / 9) * (a ^ 2)) + ((-1) * (44 / 45) * a) + (4 / 15)) * q2
  rcases mul_eq_zero.mp v with z | zz
  · left
    let p3 : Fin 4 → K := fun i => c i.castSucc
    have h3 : twoTests p3 a 3 := by
      have red (u : K) (k : ℕ) : moment p3 u k = moment c u k := by
        simp [moment, p3, Fin.sum_univ_succ, z]
      exact ⟨fun k => (red _ _).trans (h.1 k), by rw [red, red]; exact h.2.1,
        by rw [red, red]; exact h.2.2⟩
    have z3 := match3 p3 a ha h1a h3
    funext i
    have van (i : Fin 4) : c i.castSucc = 0 := congrFun z3 i
    fin_cases i
    · exact van 0
    · exact van 1
    · exact van 2
    · exact van 3
    · exact z
  · right
    exact (mul_eq_zero.mp zz).resolve_left (mul_ne_zero ha (pow_ne_zero _ (sub_ne_zero.mpr h1a)))
/-- Ordered fields have no exceptional quadratic ratio. -/
theorem ordered_quartic_three_two {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (c : Fin 5 → F) (a : F) (ha : a ≠ 0) (h1a : a ≠ 1)
    (h : twoTests c a 3) : c = 0 := by
  rcases quartic_three_two c a ha h1a h with h0 | hq
  · exact h0
  · nlinarith [sq_nonneg (5 * a - 4)]

end RKCert.Endpoint
