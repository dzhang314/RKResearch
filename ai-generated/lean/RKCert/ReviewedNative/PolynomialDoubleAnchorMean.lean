module

public import RKCert.NodalPrimitive
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A formal double-anchor quotient with its independent mean -/

namespace RKCert.ReviewedNative.AnchorMean

open Polynomial RKCert.Endpoint

noncomputable section

variable {K : Type*} [Field K]

/-- The two literal stage-independent endpoint factors. -/
def anchorPair (u : K) : K[X] := X * (X - C u)

theorem anchorPair_monic (u : K) : (anchorPair u).Monic := by
  change (X * (X - C u)).Monic
  exact monic_X.mul (monic_X_sub_C u)

@[simp] theorem anchorPair_natDegree (u : K) : (anchorPair u).natDegree = 2 := by
  change (X * (X - C u)).natDegree = 2
  rw [natDegree_mul X_ne_zero (monic_X_sub_C u).ne_zero, natDegree_X, natDegree_X_sub_C]

variable [CharZero K]

private def fromZero (u : K) : K[X] →ₗ[K] K :=
  (Polynomial.leval u).comp formalPrimitiveLinear

/-- The raw quotient is available without a nonzero or degree hypothesis
on q, and its independent X² mean is also paid. -/
theorem exists_anchored_quotient_mean {q : K[X]} {u : K}
    (hu : u ≠ 0)
    (first : (formalPrimitive (X * q)).eval u = 0)
    (second : (formalPrimitive (X ^ 2 * q)).eval u = 0) :
    ∃ h : K[X], formalPrimitive (anchorPair u * q) = anchorPair u ^ 2 * h ∧
      (formalPrimitive (X ^ 2 * h)).eval u = 0 := by
  let F := formalPrimitive (anchorPair u * q)
  have derivativeF : F.derivative = anchorPair u * q := derivative_formalPrimitive _
  have first' : fromZero u (X * q) = 0 := first
  have second' : fromZero u (X ^ 2 * q) = 0 := second
  have atU : F.eval u = 0 := by
    change fromZero u (anchorPair u * q) = 0
    have split : anchorPair u * q = X ^ 2 * q - u • (X * q) := by
      rw [anchorPair, smul_eq_C_mul]
      ring
    rw [split]
    simp only [map_sub, map_smul, first', second', smul_zero, sub_zero]
  have div : anchorPair u ^ 2 ∣ F := by
    by_cases hF : F = 0
    · rw [hF]
      exact dvd_zero _
    have sq (x : K) (root : F.IsRoot x) (droot : F.derivative.IsRoot x) :
        (X - C x) ^ 2 ∣ F :=
      (le_rootMultiplicity_iff hF).mp
        ((one_lt_rootMultiplicity_iff_isRoot hF).mpr ⟨root, droot⟩)
    have zeroSq := sq (0 : K) (formalPrimitive_eval_zero _) (by
      change F.derivative.eval 0 = 0
      rw [derivativeF]
      simp [anchorPair])
    have uSq := sq u atU (by
      change F.derivative.eval u = 0
      rw [derivativeF]
      simp [anchorPair])
    have cop : IsCoprime (X - C (0 : K)) (X - C u) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hu.symm).isUnit
    have both : IsCoprime ((X - C (0 : K)) ^ 2) ((X - C u) ^ 2) := cop.pow
    simpa only [C_0, sub_zero, anchorPair, mul_pow] using both.mul_dvd zeroSq uSq
  obtain ⟨h, factor⟩ := div
  let T : K[X] := X ^ 2 * (X - C u) * h
  have viaT : F = (X - C u) * T := by
    rw [factor]
    dsimp [T, anchorPair]
    ring
  have quotientDeriv : T.derivative = X * q - X ^ 2 * h := by
    have e := congrArg Polynomial.derivative viaT
    have linear : (X - C u).derivative = 1 := by simp
    rw [derivativeF, derivative_mul, linear, one_mul] at e
    apply mul_left_cancel₀ (monic_X_sub_C u).ne_zero
    calc
      (X - C u) * T.derivative = anchorPair u * q - T := by rw [e]; ring
      _ = (X - C u) * (X * q - X ^ 2 * h) := by dsimp [T, anchorPair]; ring
  have T0 : T.eval 0 = 0 := by simp [T]
  have Tu : T.eval u = 0 := by simp [T]
  have primT : formalPrimitive T.derivative = T :=
    eq_of_derivative_and_eval_zero (derivative_formalPrimitive _)
      (by rw [formalPrimitive_eval_zero, T0])
  have paid : fromZero u T.derivative = 0 := by
    change (formalPrimitive T.derivative).eval u = 0
    rw [primT, Tu]
  have mean : fromZero u (X ^ 2 * h) = 0 := by
    simpa only [quotientDeriv, map_sub, first', zero_sub, neg_eq_zero] using paid
  exact ⟨h, factor, mean⟩

/-- Monic normalization, with the exact degree and constant, and with
the same literal mean. Works uniformly in the degree of q. -/
theorem exists_monic_anchored_quotient_mean {q : K[X]} {u : K}
    (mq : q.Monic) (hu : u ≠ 0)
    (first : (formalPrimitive (X * q)).eval u = 0)
    (second : (formalPrimitive (X ^ 2 * q)).eval u = 0) :
    ∃ H : K[X], H.Monic ∧ H.natDegree + 1 = q.natDegree ∧
      formalPrimitive (anchorPair u * q) =
        C (((q.natDegree + 3 : ℕ) : K)⁻¹) * (anchorPair u ^ 2 * H) ∧
      (formalPrimitive (X ^ 2 * H)).eval u = 0 := by
  obtain ⟨h, raw, rawMean⟩ := exists_anchored_quotient_mean hu first second
  let L := anchorPair u
  let F := formalPrimitive (L * q)
  let N : K := ((q.natDegree + 3 : ℕ) : K)
  have Ln : L.Monic := anchorPair_monic u
  have Ld : L.natDegree = 2 := anchorPair_natDegree u
  have fraw : F = L ^ 2 * h := raw
  have df : F.derivative = L * q := derivative_formalPrimitive _
  have Fn : F ≠ 0 := by
    intro hz
    rw [hz, derivative_zero] at df
    exact (mul_ne_zero Ln.ne_zero mq.ne_zero) df.symm
  have hn : h ≠ 0 := by
    intro hz
    apply Fn
    rw [fraw, hz, mul_zero]
  have d := natDegree_derivative F
  rw [df, natDegree_mul Ln.ne_zero mq.ne_zero, Ld] at d
  have Fd : F.natDegree = q.natDegree + 3 := by omega
  have hd := congrArg Polynomial.natDegree fraw
  rw [Fd, natDegree_mul (pow_ne_zero _ Ln.ne_zero) hn, natDegree_pow, Ld] at hd
  have lc := congrArg Polynomial.leadingCoeff df
  rw [leadingCoeff_derivative, leadingCoeff_mul, Ln.leadingCoeff, mq.leadingCoeff, mul_one, Fd] at lc
  have top : F.leadingCoeff * N = 1 := lc
  have rawLc := congrArg Polynomial.leadingCoeff fraw
  rw [leadingCoeff_mul, (Ln.pow 2).leadingCoeff, one_mul] at rawLc
  have htop : h.leadingCoeff * N = 1 := by
    rw [← rawLc]
    exact top
  have Nn : N ≠ 0 := Nat.cast_ne_zero.mpr (show q.natDegree + 3 ≠ 0 by omega)
  let H := h * C N
  have Hm : H.Monic := monic_mul_C_of_leadingCoeff_mul_eq_one htop
  have Hd : H.natDegree + 1 = q.natDegree := by
    change (h * C N).natDegree + 1 = q.natDegree
    rw [natDegree_mul_C Nn]
    omega
  have fit : F = C N⁻¹ * (L ^ 2 * H) := by
    calc
      F = L ^ 2 * h := fraw
      _ = (C N⁻¹ * C N) * (L ^ 2 * h) := by
        rw [← C_mul, inv_mul_cancel₀ Nn, C_1, one_mul]
      _ = C N⁻¹ * (L ^ 2 * H) := by dsimp [H]; ring
  have mean : (formalPrimitive (X ^ 2 * H)).eval u = 0 := by
    change fromZero u (X ^ 2 * H) = 0
    have scale : X ^ 2 * H = N • (X ^ 2 * h) := by
      rw [smul_eq_C_mul]
      dsimp [H]
      ring
    have paid : fromZero u (X ^ 2 * h) = 0 := rawMean
    rw [scale, map_smul, paid, smul_zero]
  exact ⟨H, Hm, Hd, fit, mean⟩

/-- The product rule recovers q from any factored normalized primitive,
with no additional endpoint, degree, or order assumptions. -/
theorem reconstruct_of_anchored_primitive {q H : K[X]} {u k : K}
    (factor : formalPrimitive (anchorPair u * q) = C k * (anchorPair u ^ 2 * H)) :
    q = C k * (2 * (anchorPair u).derivative * H + anchorPair u * H.derivative) := by
  let L := anchorPair u
  have f : formalPrimitive (L * q) = C k * (L ^ 2 * H) := factor
  have derivativeFactor : (C k * (L ^ 2 * H)).derivative =
      L * (C k * (2 * L.derivative * H + L * H.derivative)) := by
    simp only [pow_two, derivative_mul, derivative_C, zero_mul, zero_add]
    ring
  have step := congrArg Polynomial.derivative f
  rw [derivative_formalPrimitive, derivativeFactor] at step
  exact mul_left_cancel₀ (anchorPair_monic u).ne_zero step

end
end RKCert.ReviewedNative.AnchorMean
