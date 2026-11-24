module

public import RKCert.ReviewedNative.BushyMoments
public import RKCert.ReviewedNative.ChangeCoefficients
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public section

/-! # Low-order DIRK stage obstructions natively from the reviewed HasOrder

The moment identities and all scalar residues derive directly from the
reviewed trees. A lower triangular matrix can have zero diagonal entries.
No signs, positivity, distinctness, or individual nonzero weights are taken
as hypotheses. Finite Hankel identities force the necessary distinctness. -/

namespace RKResearch

open scoped Matrix

section Field

variable {K : Type*} [Field K] {s : ℕ}

private theorem momentDetTwo (b c : Fin 2 → K) :
    b 0 * b 1 * (c 1-c 0)^2 = stageMass b c 0 * stageMass b c 2 - stageMass b c 1 ^ 2 := by
  simp only [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_two, pow_zero, pow_one, mul_one]
  ring

private theorem momentDetThree (b c : Fin 3 → K) :
    b 0*b 1*b 2 * (c 1-c 0)^2 * (c 2-c 0)^2 * (c 2-c 1)^2 =
      stageMass b c 0 * (stageMass b c 2 * stageMass b c 4 - stageMass b c 3 ^ 2) -
      stageMass b c 1 * (stageMass b c 1 * stageMass b c 4 - stageMass b c 3 * stageMass b c 2) +
      stageMass b c 2 * (stageMass b c 1 * stageMass b c 3 - stageMass b c 2 ^ 2) := by
  simp only [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_three, pow_zero, pow_one, mul_one]
  ring

private theorem firstNode_zero_of_vanishing_defect {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : A.IsLowerTriangular) (hg : monomialStageDefect A 1 0 = 0) :
    (A *ᵥ (1 : Fin (s+1) → K)) 0 = 0 := by
  let c : Fin (s+1) → K := A *ᵥ 1
  have hrow (v : Fin (s+1) → K) : (A *ᵥ v) 0 = A 0 0 * v 0 := by
    apply lowerTriangular_mulVec_pivot ha
    intro j hj
    exact False.elim ((Fin.not_lt_zero j) hj)
  have hc : c 0 = A 0 0 := by
    change (A *ᵥ (1 : Fin (s+1) → K)) 0 = _
    rw [hrow, Pi.one_apply, mul_one]
  change (2:K) * (A *ᵥ c^1) 0 - c 0 ^ 2 = 0 at hg
  rw [pow_one, hrow, ← hc] at hg
  have hz : c 0 ^ 2 = 0 := by linear_combination hg
  exact (sq_eq_zero_iff.mp hz)

/-- Order three already needs two stages, without a triangularity hypothesis. -/
theorem HasOrder.order_three_stages_field {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b 3) : 2 ≤ s := by
  by_contra hn
  have hs : s = 0 ∨ s = 1 := by omega
  rcases hs with rfl | rfl
  · have h0 := h.bushy_moment 0 (by decide)
    simp [stageMass, dotProduct] at h0
  · let c : Fin 1 → K := A *ᵥ 1
    have h0 := h.bushy_moment 0 (by decide)
    have h1 : (2:K) * stageMass b c 1 = 1 := h.bushy_moment 1 (by decide)
    have h2 : (3:K) * stageMass b c 2 = 1 := h.bushy_moment 2 (by decide)
    norm_num [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_one] at h0 h1 h2
    simp only [h0, one_mul] at h1 h2
    apply zero_ne_one (α := K)
    linear_combination 4*h2 - 3*(2*c 0+1)*h1

/-- A lower triangular tableau with order four has at least three stages. -/
theorem HasOrder.dirk_order_four_stages_field {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b 4) (ha : A.IsLowerTriangular) : 3 ≤ s := by
  have h3 : HasOrder A b 3 := fun t ht => h t (ht.trans (by decide))
  have hlo := h3.order_three_stages_field
  by_contra hsmall
  have hs : s = 2 := by omega
  subst s
  let c : Fin 2 → K := A *ᵥ 1
  let g := monomialStageDefect A 1
  have m0 : (1:K) * stageMass b c 0 = 1 :=
    by simpa only [Nat.zero_add, Nat.cast_one] using h.bushy_moment 0 (by decide)
  have m1 : (2:K) * stageMass b c 1 = 1 := h.bushy_moment 1 (by decide)
  have m2 : (3:K) * stageMass b c 2 = 1 := h.bushy_moment 2 (by decide)
  have m3 : (4:K) * stageMass b c 3 = 1 := h.bushy_moment 3 (by decide)
  have hcert : (12:K)*(b 0 * b 1 * (c 1-c 0)^2) = 1 := by
    rw [momentDetTwo]
    linear_combination (12*stageMass b c 2)*m0 + (-(6*stageMass b c 1)-3)*m1 + 4*m2
  have hv : b 0*b 1*(c 1-c 0)^2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcert
    exact zero_ne_one hcert
  have hb0 : b 0 ≠ 0 := by intro hz; apply hv; simp [hz]
  have h10 : c 1-c 0 ≠ 0 := by intro hz; apply hv; simp [hz]
  have t0 : stageMass (fun i => b i*g i) c 0 = 0 :=
    h.monomialStageDefect_moment 1 0 (by decide)
  have t1 : stageMass (fun i => b i*g i) c 1 = 0 :=
    h.monomialStageDefect_moment 1 1 (by decide)
  simp only [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_two, pow_zero, pow_one, mul_one] at t0 t1
  have hcut : b 0*(c 1-c 0)*g 0 = 0 := by linear_combination c 1*t0 - t1
  have hg0 := (mul_eq_zero.mp hcut).resolve_left (mul_ne_zero hb0 h10)
  have hc0 : c 0 = 0 := firstNode_zero_of_vanishing_defect ha hg0
  have hk : stageMass b c 1 * stageMass b c 3 - stageMass b c 2 ^ 2 = 0 := by
    simp only [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_two, hc0, pow_one,
      zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero, zero_add]
    ring
  have he : (72:K)*(stageMass b c 1 * stageMass b c 3 - stageMass b c 2 ^ 2) = 1 := by
    linear_combination (36*stageMass b c 3)*m1 - (24*stageMass b c 2+8)*m2 + 9*m3
  rw [hk, mul_zero] at he
  exact zero_ne_one he

/-- A lower triangular tableau with order five has at least four stages.
All three knot/weight nonvanishing facts are derived from paid moments. -/
theorem HasOrder.dirk_order_five_stages_field {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b 5) (ha : A.IsLowerTriangular) : 4 ≤ s := by
  have h4 : HasOrder A b 4 := fun t ht => h t (ht.trans (by decide))
  have hlo := h4.dirk_order_four_stages_field ha
  by_contra hsmall
  have hs : s = 3 := by omega
  subst s
  let c : Fin 3 → K := A *ᵥ 1
  let g := monomialStageDefect A 1
  let f := monomialStageDefect A 2
  have m0 : (1:K) * stageMass b c 0 = 1 :=
    by simpa only [Nat.zero_add, Nat.cast_one] using h.bushy_moment 0 (by decide)
  have m1 : (2:K) * stageMass b c 1 = 1 := h.bushy_moment 1 (by decide)
  have m2 : (3:K) * stageMass b c 2 = 1 := h.bushy_moment 2 (by decide)
  have m3 : (4:K) * stageMass b c 3 = 1 := h.bushy_moment 3 (by decide)
  have m4 : (5:K) * stageMass b c 4 = 1 := h.bushy_moment 4 (by decide)
  have hcert : (2160:K)*(b 0*b 1*b 2 * (c 1-c 0)^2 * (c 2-c 0)^2 * (c 2-c 1)^2) = 1 := by
    rw [momentDetThree]
    linear_combination (2160*stageMass b c 2*stageMass b c 4-2160*(stageMass b c 3)^2)*m0 +
      (-(1080*stageMass b c 1*stageMass b c 4)+2160*stageMass b c 2*stageMass b c 3-540*stageMass b c 4)*m1 +
      (-(720*(stageMass b c 2)^2)-240*stageMass b c 2+720*stageMass b c 3+720*stageMass b c 4-80)*m2 +
      (45-540*stageMass b c 3)*m3 + 36*m4
  have hv : b 0*b 1*b 2 * (c 1-c 0)^2 * (c 2-c 0)^2 * (c 2-c 1)^2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcert
    exact zero_ne_one hcert
  have hb0 : b 0 ≠ 0 := by intro hz; apply hv; simp [hz]
  have hb1 : b 1 ≠ 0 := by intro hz; apply hv; simp [hz]
  have h10 : c 1-c 0 ≠ 0 := by intro hz; apply hv; simp [hz]
  have h20 : c 2-c 0 ≠ 0 := by intro hz; apply hv; simp [hz]
  have h21 : c 2-c 1 ≠ 0 := by intro hz; apply hv; simp [hz]
  have t0 : stageMass (fun i => b i*g i) c 0 = 0 :=
    h.monomialStageDefect_moment 1 0 (by decide)
  have t1 : stageMass (fun i => b i*g i) c 1 = 0 :=
    h.monomialStageDefect_moment 1 1 (by decide)
  have t2 : stageMass (fun i => b i*g i) c 2 = 0 :=
    h.monomialStageDefect_moment 1 2 (by decide)
  simp only [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_three, pow_zero, pow_one, mul_one]
    at t0 t1 t2
  have e0 : b 0*(c 1-c 0)*(c 2-c 0)*g 0 = 0 := by
    linear_combination c 1*c 2*t0 - (c 1+c 2)*t1 + t2
  have e1 : b 1*(c 1-c 0)*(c 2-c 1)*g 1 = 0 := by
    linear_combination -(c 0*c 2)*t0 + (c 0+c 2)*t1 - t2
  have hg0 := (mul_eq_zero.mp e0).resolve_left (mul_ne_zero (mul_ne_zero hb0 h10) h20)
  have hg1 := (mul_eq_zero.mp e1).resolve_left (mul_ne_zero (mul_ne_zero hb1 h10) h21)
  have hc0 : c 0 = 0 := firstNode_zero_of_vanishing_defect ha hg0
  have hc1 : c 1 ≠ 0 := by simpa only [hc0, sub_zero] using h10
  have za : A 0 1 = 0 := ha (show (0 : Fin 3) < 1 by decide)
  have zb : A 0 2 = 0 := ha (show (0 : Fin 3) < 2 by decide)
  have zd : A 1 2 = 0 := ha (show (1 : Fin 3) < 2 by decide)
  have hdef (d : ℕ) (i : Fin 3) :
      monomialStageDefect A d i =
        ((d+1 : ℕ) : K) * (A i 0*c 0^d + A i 1*c 1^d + A i 2*c 2^d) - c i^(d+1) := by
    change ((d+1 : ℕ) : K) * (A *ᵥ c^d) i - c i^(d+1) = _
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three]
    rfl
  have hf0 : f 0 = 0 := by
    change monomialStageDefect A 2 0 = 0
    rw [hdef]
    norm_num [hc0, za, zb]
  have u0 : stageMass (fun i => b i*f i) c 0 = 0 :=
    h.monomialStageDefect_moment 2 0 (by decide)
  have u1 : stageMass (fun i => b i*f i) c 1 = 0 :=
    h.monomialStageDefect_moment 2 1 (by decide)
  simp only [stageMass, dotProduct, Pi.pow_apply, Fin.sum_univ_three, pow_zero, pow_one, mul_one,
    hf0, mul_zero, zero_mul, zero_add] at u0 u1
  have ec : b 1*(c 2-c 1)*f 1 = 0 := by linear_combination c 2*u0-u1
  have hf1 := (mul_eq_zero.mp ec).resolve_left (mul_ne_zero hb1 h21)
  change monomialStageDefect A 1 1 = 0 at hg1
  change monomialStageDefect A 2 1 = 0 at hf1
  rw [hdef] at hg1 hf1
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hg1 hf1
  simp only [hc0, zd, zero_pow (by decide : 1 ≠ 0), zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_mul, zero_add, add_zero, pow_one] at hg1 hf1
  have hz : c 1^3 = 0 := by linear_combination 2*hf1-3*c 1*hg1
  exact pow_ne_zero 3 hc1 hz

end Field

section Ring

variable {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}

/-- Order four needs three physical stages over every nontrivial commutative ring. -/
theorem HasOrder.dirk_order_four_stages (h : HasOrder A b 4) (ha : A.IsLowerTriangular) : 3 ≤ s :=
  h.lower_triangular_of_all_fields ha (fun _ _ _ _ ht h' => h'.dirk_order_four_stages_field ht)

/-- Order five needs four physical stages over every nontrivial commutative ring. -/
theorem HasOrder.dirk_order_five_stages (h : HasOrder A b 5) (ha : A.IsLowerTriangular) : 4 ≤ s :=
  h.lower_triangular_of_all_fields ha (fun _ _ _ _ ht h' => h'.dirk_order_five_stages_field ht)

end Ring

end RKResearch
