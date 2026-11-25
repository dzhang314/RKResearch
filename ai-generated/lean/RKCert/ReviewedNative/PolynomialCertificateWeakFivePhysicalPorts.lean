module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePorts
public import RKCert.ReviewedNative.PositiveIntervalGrid19

import Mathlib.Tactic.Ring

@[expose] public section

/-! # The six actual stopped polynomial integrals

A left factor is X-r and a right factor is r-X. Four right factors equal
the same monic quartic. Appending the right mark therefore inserts z-X,
not X-z. The integral substitutions below are algebraic and allow
degenerate spans; a span is divided out only when explicitly nonzero. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def leftProduct (rs : List K) : K[X] := (rs.map (fun r => X - C r)).prod

noncomputable def rightProduct (rs : List K) : K[X] := (rs.map (fun r => C r - X)).prod

theorem rightProduct_eq_sign (rs : List K) :
    rightProduct rs = (-1 : K[X]) ^ rs.length * leftProduct rs := by
  induction rs with
  | nil => simp [rightProduct, leftProduct]
  | cons r rs ih =>
    change (C r - X) * rightProduct rs =
      (-1 : K[X]) ^ (rs.length + 1) * ((X - C r) * leftProduct rs)
    rw [ih, pow_succ]
    ring

theorem rightProduct_eq_leftProduct_of_even (rs : List K) (he : Even rs.length) :
    rightProduct rs = leftProduct rs := by rw [rightProduct_eq_sign, he.neg_one_pow, one_mul]

theorem rightProduct_append_mark (rs : List K) (he : Even rs.length) (z : K) :
    rightProduct (rs ++ [z]) = leftProduct rs * (C z - X) := by
  calc
    rightProduct (rs ++ [z]) = rightProduct rs * (C z - X) := by simp [rightProduct]
    _ = leftProduct rs * (C z - X) := by rw [rightProduct_eq_leftProduct_of_even rs he]

private theorem leftProduct_comp (rs : List K) (d : K) :
    (leftProduct rs).comp (C d * X) = (rs.map (portFactor d)).prod := by
  induction rs with
  | nil => simp [leftProduct]
  | cons r rs ih =>
    change ((X - C r) * leftProduct rs).comp _ = portFactor d r * (rs.map (portFactor d)).prod
    simp only [mul_comp, sub_comp, X_comp, C_comp, ih, portFactor]

private theorem rightProduct_comp (rs : List K) (d : K) :
    (rightProduct rs).comp (C (d - 1) * X + 1) =
      ((rs.map (fun r => 1 - r)).map (portFactor (1 - d))).prod := by
  induction rs with
  | nil => simp [rightProduct]
  | cons r rs ih =>
    change ((C r - X) * rightProduct rs).comp _ =
      portFactor (1 - d) (1 - r) * ((rs.map (fun r => 1 - r)).map (portFactor (1 - d))).prod
    rw [mul_comp, sub_comp, C_comp, X_comp, ih]
    have hf : C r - (C (d - 1) * X + 1) = portFactor (1 - d) (1 - r) := by
      simp only [portFactor, map_sub, map_one]
      ring
    rw [hf]

private theorem integral_unit_eq (P : K[X]) :
    RKCert.ReviewedNative.PositiveRule19.integral 0 1 P = unitFunctional P := by
  rw [RKCert.ReviewedNative.PositiveRule19.integral_zero_left]
  rfl

theorem left_window_exact (e : ℕ) (d : K) (rs : List K) :
    RKCert.ReviewedNative.PositiveRule19.integral 0 d (X ^ e * leftProduct rs) =
      d ^ (e + 1) * formalPort e d rs := by
  rw [RKCert.ReviewedNative.PositiveRule19.integral_affine]
  simp only [sub_zero, map_zero, add_zero, mul_comp, pow_comp, X_comp, leftProduct_comp]
  have alg : (C d * X) ^ e * (rs.map (portFactor d)).prod =
      (d ^ e) • (X ^ e * (rs.map (portFactor d)).prod) := by
    simp only [Polynomial.smul_eq_C_mul, map_pow, mul_pow, mul_assoc]
  rw [alg, map_smul]
  simp only [smul_eq_mul, integral_unit_eq, formalPort, pow_succ]
  ring

theorem right_window_exact (e : ℕ) (d : K) (rs : List K) :
    RKCert.ReviewedNative.PositiveRule19.integral d 1 ((1 - X) ^ e * rightProduct rs) =
      (1 - d) ^ (e + 1) * formalPort e (1 - d) (rs.map (fun r => 1 - r)) := by
  let P := (1 - X) ^ e * rightProduct rs
  have reverse : RKCert.ReviewedNative.PositiveRule19.integral d 1 P =
      -RKCert.ReviewedNative.PositiveRule19.integral 1 d P := by
    simp only [RKCert.ReviewedNative.PositiveRule19.integral_apply]
    ring
  change RKCert.ReviewedNative.PositiveRule19.integral d 1 P = _
  rw [reverse, RKCert.ReviewedNative.PositiveRule19.integral_affine]
  have flip : ((1 - X : K[X]).comp (C (d - 1) * X + 1)) = C (1 - d) * X := by
    simp only [sub_comp, one_comp, X_comp, map_sub, map_one]
    ring
  simp only [P, map_one, mul_comp, pow_comp, flip, rightProduct_comp]
  let Q := ((rs.map (fun r => 1 - r)).map (portFactor (1 - d))).prod
  have alg : (C (1 - d) * X) ^ e * Q = ((1 - d) ^ e) • (X ^ e * Q) := by
    simp only [Polynomial.smul_eq_C_mul, map_pow, mul_pow, mul_assoc]
  rw [alg, map_smul]
  simp only [smul_eq_mul, integral_unit_eq, formalPort, Q, pow_succ]
  ring

noncomputable def LocalPort.physicalValue (p : LocalPort) (β : Fin 8 → K) : K :=
  if p.reflected then
    RKCert.ReviewedNative.PositiveRule19.integral (β p.stop) 1
      ((1 - X) ^ p.e * rightProduct (p.factors.map β))
  else
    RKCert.ReviewedNative.PositiveRule19.integral 0 (β p.stop)
      (X ^ p.e * leftProduct (p.factors.map β))

theorem LocalPort.physicalValue_eq (p : LocalPort) (β : Fin 8 → K) :
    p.physicalValue β = (portSite p.reflected β p.stop) ^ (p.e + 1) * p.value β := by
  cases h : p.reflected
  · have hsite : portSite false β = β := rfl
    simpa only [LocalPort.physicalValue, LocalPort.value, h, hsite, Bool.false_eq_true,
      ite_false] using left_window_exact p.e (β p.stop) (p.factors.map β)
  · have hsite : portSite true β = (fun i => 1 - β i) := rfl
    simpa only [LocalPort.physicalValue, LocalPort.value, h, hsite, ite_true,
      List.map_map, Function.comp_def] using right_window_exact p.e (β p.stop) (p.factors.map β)

theorem no_six_physical_ports_on_chart {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    {σ : List (Fin 8)} (perm : σ.Perm (List.finRange 8)) (good : (decodeWord σ).permitted = true)
    (nonzero : ∀ p ∈ (decodeWord σ).six, portSite p.reflected β p.stop ≠ 0)
    (paid : ∀ p ∈ (decodeWord σ).six, p.physicalValue β = 0) : False := by
  apply no_six_paid_ports_on_chart hs ht order unit roots perm good
  intro p hp
  have h := paid p hp
  rw [LocalPort.physicalValue_eq] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (nonzero p hp))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
