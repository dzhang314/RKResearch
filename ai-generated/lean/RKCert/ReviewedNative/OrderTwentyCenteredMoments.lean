module

public import RKCert.ReviewedNative.HankelCenteredAtom
public import RKCert.ReviewedNative.StagePolynomialMoment
public import RKCert.ReviewedNative.BushyMoments

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # From actual raw order tests to centered signed powers

No coefficient or localized positivity is used. There is no global
rational embedding in the coefficient field. Every division is by
a paid integer; all binomial cancellation takes place over ℤ. -/
namespace RKResearch.Certified.Graded.HankelCenteredAtom

open Polynomial Matrix HankelLegendreIntData
open scoped Polynomial Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

structure CenteredPower20 (I : K[X] →ₗ[K] K) : Prop where
  units : ∀ n : ℕ, 0 < n → n ≤ 20 → (n : K) ≠ 0
  powers : ∀ j < 20, (paidNat : K) * I (X^j) = (atom j : K)

theorem CenteredPower20.paidNat_ne_zero {I : K[X] →ₗ[K] K} (h : CenteredPower20 I) :
    (paidNat : K) ≠ 0 := by
  have f (n : ℕ) (hn : n≤20) : (n.factorial : K) ≠ 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      exact mul_ne_zero (h.units _ (Nat.succ_pos _) hn) (ih (Nat.le_of_succ_le hn))
  rw [paidNat_eq_factorial]
  exact f 20 (Nat.le_refl _)

private theorem centeredPrefix_sum (n k : ℕ) :
    centeredPrefix n k = ∑ j ∈ Finset.range k, centeredCoeff n j * rawAtom j := by
  induction k with
  | zero => simp [centeredPrefix]
  | succ k ih => simp only [centeredPrefix, Finset.sum_range_succ, ih]

private theorem centered_power_expansion (x : K) (n : ℕ) :
    ((2:K)*x-1)^n = ∑ j ∈ Finset.range (n+1), (centeredCoeff n j : K)*x^j := by
  rw [sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [centeredCoeff_eq]
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
    Int.cast_neg, Int.cast_one]
  rw [mul_pow]
  ring

/-- Reusable transfer from any weighted raw evaluations whose first
twenty cleared monomials agree. Signed and zero weights are allowed. -/
theorem centered_weighted_powers {ι : Type*} [Fintype ι] (x b : ι → K)
    (raw : ∀ j < 20, (paidNat : K) * (∑ t, b t * (x t)^j) = (rawAtom j : K))
    (n : ℕ) (hn : n<20) :
    (paidNat : K) * weightedStageMoment (fun t => 2*x t-1) b (X^n) = (atom n : K) := by
  let f (j : ℕ) (t : ι) : K := b t * (x t)^j
  let c (j : ℕ) : K := (centeredCoeff n j : K)
  have exchange :
      (∑ t, b t * ∑ j ∈ Finset.range (n+1), c j * (x t)^j) =
      ∑ j ∈ Finset.range (n+1), c j * ∑ t, f j t := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro t _
    unfold f
    ring
  calc
    _ = (paidNat : K) * (∑ t, b t * ∑ j ∈ Finset.range (n+1), c j * (x t)^j) := by
      simp only [weightedStageMoment_apply, Polynomial.eval_pow, Polynomial.eval_X,
        centered_power_expansion, c]
    _ = (paidNat : K) * ∑ j ∈ Finset.range (n+1), c j * ∑ t, f j t := by rw [exchange]
    _ = ∑ j ∈ Finset.range (n+1), c j * ((paidNat : K) * ∑ t, f j t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j ∈ Finset.range (n+1), c j * (rawAtom j : K) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h : j < 20 := by have e := Finset.mem_range.mp hj; omega
      rw [show (paidNat : K) * (∑ t, f j t)=(rawAtom j : K) from raw j h]
    _ = _ := by
      have z := centeredAtoms ⟨n,hn⟩
      change centeredPrefix n (n+1)=atom n at z
      rw [centeredPrefix_sum] at z
      have e := congrArg (fun z : ℤ => (z : K)) z
      simpa only [c, Int.cast_sum, Int.cast_mul] using e

theorem raw_hasOrder_atoms {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : RKResearch.HasOrder 20 A b) (j : ℕ) (hj : j<20) :
    (paidNat : K) * (∑ t, b t * ((A *ᵥ 1) t)^j) = (rawAtom j : K) := by
  have hpay : j+1≤20 := Nat.succ_le_of_lt hj
  have hdvd : j+1 ∣ paidNat := paid_atom_denominators ⟨j,hj⟩
  have hne : ((j+1:ℕ):K) ≠ 0 := (ho.natCast_isUnit (Nat.succ_pos j) hpay).ne_zero
  have e : (∑ t, b t * ((A *ᵥ 1) t)^j) = stageMass b (A *ᵥ 1) j := by
    simp only [stageMass, dotProduct, Pi.pow_apply]
  rw [e, ho.bushy_moment_div j hpay, rawAtom, Int.cast_natCast, Nat.cast_div hdvd hne]
  simp only [div_eq_mul_inv, one_mul]

/-- The actual order-20 signed centered evaluation has all and only
the required pure atom tests, degrees 0 through 19. -/
theorem centered_HasOrder_powers {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : RKResearch.HasOrder 20 A b) :
    CenteredPower20 (weightedStageMoment (fun t => 2*(A *ᵥ 1) t-1) b) where
  units n hn hp := (ho.natCast_isUnit hn hp).ne_zero
  powers n hn := centered_weighted_powers _ _ (raw_hasOrder_atoms ho) n hn

end
end RKResearch.Certified.Graded.HankelCenteredAtom
