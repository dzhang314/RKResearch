module

public import RKCert.ReviewedNative.SDIRKNineReplayData
public import RKCert.ReviewedNative.SDIRKNineParameter

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Specialization to the archived pair of real algebraic parameters

This is the exact link between the integer-normalized tableau and the
independently proved existence of the two small auxiliary real nodes. -/

namespace RKResearch.Certified.SDIRKNineReplay

open RKCert.ReviewedNative.IntegerHornerCertificate
open SDIRKNineParameter

set_option maxHeartbeats 2500000

private theorem inner_real (x : ℝ) :
    coeval innerMod x = -value pCoeffs x := by
  norm_num [innerMod, coeval, RKCert.ReviewedNative.IntegerHornerCertificate.horner, value,
    RKCert.ReviewedNative.PolynomialBracket.horner, pCoeffs]
  ring

private theorem outerU_real (x : ℝ) :
    outerU.val x = (shapeDen : ℝ) * U x := by
  norm_num [outerU, Expr.val, shapeDen, coeval, RKCert.ReviewedNative.IntegerHornerCertificate.horner, U, value,
    RKCert.ReviewedNative.PolynomialBracket.horner, uCoeffs]
  ring

private theorem outerV_real (x : ℝ) :
    outerV.val x = (shapeDen : ℝ)^2 * V x := by
  norm_num [outerV, Expr.val, shapeDen, coeval, RKCert.ReviewedNative.IntegerHornerCertificate.horner, V, value,
    RKCert.ReviewedNative.PolynomialBracket.horner, vCoeffs]
  ring

theorem realRootPair_of_parameters {x v w : ℝ} (hp : value pCoeffs x = 0)
    (hs : v + w = U x) (hm : v * w = V x) :
    RootPair x ((shapeDen : ℝ) * v) := by
  constructor
  · rw [inner_real, hp, neg_zero]
  · rw [outerU_real, outerV_real, ← hs, ← hm]
    ring

theorem exists_real_rootPair : ∃ x y : ℝ, x ≠ 0 ∧ RootPair x y := by
  obtain ⟨x, v, w, -, hx, hp, -, -, -, -, hs, hm⟩ := exists_real_parameters
  exact ⟨x, (shapeDen:ℝ)*v, hx.ne', realRootPair_of_parameters hp hs hm⟩

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem map_coeval (f : R →+* S) (x : R) (a : List ℤ) :
    f (coeval a x) = coeval a (f x) := by
  induction a with
  | nil => simp [coeval, RKCert.ReviewedNative.IntegerHornerCertificate.horner]
  | cons a as ih => simp only [coeval_cons, map_add, map_mul, map_intCast, ih]

private theorem map_expr (f : R →+* S) (x : R) (a : Expr) :
    f (a.val x) = a.val (f x) := by
  induction a with
  | atom as => exact map_coeval f x as
  | add a b ha hb => simp only [Expr.val, map_add, ha, hb]
  | neg a ha => simp only [Expr.val, map_neg, ha]
  | mul a b ha hb => simp only [Expr.val, map_mul, ha, hb]

/-- Injective coefficient maps both preserve and reflect the two local relations. -/
theorem rootPair_iff_map (f : R →+* S) (hf : Function.Injective f) {x y : R} :
    RootPair x y ↔ RootPair (f x) (f y) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [map_coeval, map_zero] using congrArg f h.inner
    · simpa only [map_pow, map_sub, map_mul, map_expr] using congrArg f h.outer
  · intro h
    refine ⟨hf ?_, hf ?_⟩
    · simpa only [map_coeval, map_zero] using h.inner
    · simpa only [map_pow, map_sub, map_mul, map_expr] using h.outer

end Map

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem exists_realAlgebraic_rootPair : ∃ x y : ℝₐ, x ≠ 0 ∧ RootPair x y := by
  obtain ⟨x, v, w, -, hx, hp, hax, hav, -, -, -, -, hs, hm⟩ :=
    exists_algebraic_parameters
  let xx : ℝₐ := ⟨x, mem_algebraicClosure_iff.mpr hax⟩
  let vv : ℝₐ := ⟨v, mem_algebraicClosure_iff.mpr hav⟩
  let f := algebraMap ℝₐ ℝ
  refine ⟨xx, (shapeDen : ℝₐ) * vv, ?_, (rootPair_iff_map f f.injective).mpr ?_⟩
  · intro h
    have heq : f xx = f 0 := congrArg f h
    rw [map_zero] at heq
    exact hx.ne' heq
  · rw [map_mul, map_intCast]
    exact realRootPair_of_parameters hp hs hm

end RKResearch.Certified.SDIRKNineReplay
