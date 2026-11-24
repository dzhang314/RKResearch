module

public import RKCert.ReviewedNative.LobattoDIRK109Algebra
public import RKCert.ReviewedNative.PolynomialBracket
public import RKCert.ReviewedNative.LaguerreGauss76Real

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Selecting the archived real algebraic parameters

The large positive quartic root and the positive square root of seven
are selected by exact signs. The two polynomial equations do not
require an irreducibility or degree assumption. -/

namespace RKResearch.Certified.LobattoDIRK109

open Polynomial
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

def lo : ℚ := 1102801182/100000000
def hi : ℚ := 1102801183/100000000
def pCoeffs : List ℚ := [3087,0,-147,0,1]

noncomputable def value (cs : List ℚ) (x : ℝ) : ℝ :=
  RKCert.ReviewedNative.PolynomialBracket.horner (cs.map (Rat.castHom ℝ)) x

private theorem inner_real (x : ℝ) :
    coeval innerMod x = value pCoeffs x := by
  norm_num [innerMod, coeval, horner, value, pCoeffs,
    RKCert.ReviewedNative.PolynomialBracket.horner]

theorem exists_real_x : ∃ x ∈ Set.Ioo (lo:ℝ) (hi:ℝ), coeval innerMod x = 0 := by
  obtain ⟨x, hx, hp⟩ := RKCert.ReviewedNative.PolynomialBracket.exists_real_horner_root (B:=12)
    (by norm_num [lo,hi] : (lo:ℝ) < (hi:ℝ)) (by norm_num [lo]) (by norm_num [hi])
    (pCoeffs.map (Rat.castHom ℝ))
    (by norm_num [lo,pCoeffs,RKCert.ReviewedNative.PolynomialBracket.horner])
    (by norm_num [hi,pCoeffs,RKCert.ReviewedNative.PolynomialBracket.horner])
  exact ⟨x, hx, (inner_real x).trans hp⟩

private theorem root_is_algebraic {x : ℝ} (hx : coeval innerMod x = 0) : IsAlgebraic ℚ x := by
  open RKCert.ReviewedNative.PolynomialBracket in
  refine ⟨ofCoeffs pCoeffs, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun p : ℚ[X] => p.coeff 4) h
    rw [RKCert.ReviewedNative.PolynomialBracket.coeff_ofCoeffs] at hh
    norm_num [pCoeffs] at hh
  · rw [aeval_def, RKCert.ReviewedNative.PolynomialBracket.eval₂_ofCoeffs]
    exact (inner_real x).symm.trans hx

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_coeval (f : R →+* S) (x : R) (a : List ℤ) :
    f (coeval a x) = coeval a (f x) := by
  induction a with
  | nil => simp [coeval, horner]
  | cons a as ih => simp only [coeval_cons, map_add, map_mul, map_intCast, ih]

theorem map_expr (f : R →+* S) (x : R) (a : Expr) :
    f (a.val x) = a.val (f x) := by
  induction a with
  | atom as => exact map_coeval f x as
  | add a b ha hb => simp only [Expr.val, map_add, ha, hb]
  | neg a ha => simp only [Expr.val, map_neg, ha]
  | mul a b ha hb => simp only [Expr.val, map_mul, ha, hb]

theorem map_qval (f : R →+* S) (x y : R) (a : QExpr) :
    f (a.val x y) = a.val (f x) (f y) := by
  simp only [QExpr.val, map_add, map_mul, map_expr]

end Map

theorem exists_realAlgebraic_parameters :
    ∃ x y : ℝₐ, (x:ℝ) ∈ Set.Ioo (lo:ℝ) (hi:ℝ) ∧ 0 < (y:ℝ) ∧
      coeval innerMod x = 0 ∧ y^2 = 7 := by
  obtain ⟨x, hI, hx⟩ := exists_real_x
  obtain ⟨y, hp, hy⟩ := LaguerreGauss76.positive_algebraic_root 7 (by decide)
  let xx : ℝₐ := ⟨x, mem_algebraicClosure_iff.mpr (root_is_algebraic hx)⟩
  let f := algebraMap ℝₐ ℝ
  refine ⟨xx, y, hI, hp, f.injective ?_, ?_⟩
  · rw [map_coeval, map_zero]
    exact hx
  · exact hy

theorem exists_real_parameters :
    ∃ x y : ℝ, x ∈ Set.Ioo (lo:ℝ) (hi:ℝ) ∧ 0 < y ∧
      coeval innerMod x = 0 ∧ y^2 = 7 := by
  obtain ⟨x, y, hI, hp, hx, hy⟩ := exists_realAlgebraic_parameters
  let f := algebraMap ℝₐ ℝ
  refine ⟨f x, f y, hI, hp, ?_, ?_⟩
  · simpa only [map_coeval, map_zero] using congrArg f hx
  · have hh := congrArg f hy
    rw [map_pow, map_ofNat] at hh
    exact hh

end RKResearch.Certified.LobattoDIRK109
