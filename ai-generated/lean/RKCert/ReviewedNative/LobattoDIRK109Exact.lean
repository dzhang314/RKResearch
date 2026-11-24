module

public import RKCert.ReviewedNative.LobattoDIRK109

import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # The archived ten-stage witness fails order ten

The output quadrature actually pays the order-ten bush. The tall
tree supplies a nonzero residual instead. Its stage value reuses
the cached derivative of the reviewed order-eight tall tree. -/

namespace RKResearch.Certified.LobattoDIRK109

open RKResearch FiniteRootedTree CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 3500000
set_option maxRecDepth 14000

private def resA : List ℤ := [464211741, 22418235, -14344015, 775070]
private def resB : List ℤ := [324991275, -20504925, -13138055, 1117630]
private def resMult : ℤ := 622580174731245406772838811618607730355731394151485593686932193280

private def residualCoeff : QExpr :=
  (QExpr.atom resA resB).scale (.atom [resMult])

private def tenthV : Vec := act (deriv (tag 199))

private theorem deriv_leaf {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    VecVal x y (deriv (tag 0)) = numA x y *ᵥ 1 := by
  have hk : keys (tag 0) = ⟨1,1,[]⟩ := by decide +kernel
  simpa only [hk, decode, List.map_nil, List.prod_nil] using
    deriv_correct hx hy (tag 0) (by decide +kernel)

private theorem deriv_one_child {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) {i j : Fin Count}
    (hi : (keys i).order < 9) (hk : (keys i).children = [j]) :
    VecVal x y (deriv i) = numA x y *ᵥ VecVal x y (deriv j) := by
  simpa only [decode, hk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    using deriv_correct hx hy i hi

private def chainKey : ℕ → Fin Count
  | 0 => tag 0
  | 1 => tag 1
  | 2 => tag 3
  | 3 => tag 7
  | 4 => tag 16
  | 5 => tag 36
  | 6 => tag 84
  | 7 => tag 199
  | _ => tag 0

private theorem chain_succ (k : ℕ) (hk : k < 7) :
    (keys (chainKey (k + 1))).order < 9 ∧
      (keys (chainKey (k + 1))).children = [chainKey k] := by
  interval_cases k <;> decide +kernel

private theorem chain_power {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) (k : ℕ) (hk : k < 8) :
    (numA x y) ^ (k + 1) *ᵥ (1 : Fin 10 → K) = VecVal x y (deriv (chainKey k)) := by
  induction k with
  | zero =>
    simpa only [Nat.zero_add, pow_one, chainKey] using (deriv_leaf hx hy).symm
  | succ k ih =>
    have hc := chain_succ k (by omega)
    rw [show k.succ + 1 = (k + 1) + 1 from rfl, pow_succ', ← Matrix.mulVec_mulVec,
      ih (by omega)]
    exact (deriv_one_child hx hy hc.1 hc.2).symm

private theorem tenthV_val {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    Φ (tallTree 10) (numA x y) = VecVal x y tenthV := by
  rw [Φ_tallTree, show ((10:ℕ+):ℕ)-1 = 9 from rfl, tenthV, act_val hy]
  rw [show (numA x y) ^ 9 = numA x y * (numA x y) ^ 8 from pow_succ' _ _,
    ← Matrix.mulVec_mulVec]
  exact congrArg (fun v : Fin 10 → K => numA x y *ᵥ v) (chain_power hx hy 7 (by decide))

private theorem tenth_numerator {K : Type*} [CommRing K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    (3628800:K) * (VecVal x y rawB ⬝ᵥ Φ (tallTree 10) (numA x y)) =
      (weightDen:K)*(stageDen:K)^9 + residualCoeff.val x y := by
  have hc : QExpr.eqMod innerMod 6 ((sumWord tenthV).scale (.atom [3628800]))
      ((QExpr.const (weightDen*stageDen^9)).add residualCoeff) = true := by decide +kernel
  have h := QExpr.eqMod_sound hc (y := y) hx
  rw [QExpr.val_scale, sumWord_val hy, QExpr.val_add, QExpr.val_const, ← tenthV_val hx hy] at h
  have hz : (Expr.atom [3628800]).val x = (3628800:K) := by norm_num [Expr.val, coeval, horner]
  simpa only [hz, Int.cast_mul, Int.cast_pow] using h

private theorem coeval_real_value (as : List ℤ) (x : ℝ) :
    coeval as x = value (as.map (Int.castRingHom ℚ)) x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [coeval_cons, ih]
    simp [value, RKCert.ReviewedNative.PolynomialBracket.horner]

private theorem coeval_pos {as : List ℤ} {x : ℝ}
    (hI : x ∈ Set.Ioo (lo:ℝ) (hi:ℝ))
    (hpos : 0 < (RKCert.ReviewedNative.PolynomialBracket.box lo hi
      (as.map (Int.castRingHom ℚ))).1) : 0 < coeval as x := by
  rw [coeval_real_value]
  exact RKCert.ReviewedNative.PolynomialBracket.horner_pos_of_box
    (by norm_num [lo]) hI.1.le hI.2.le _ hpos

private theorem residual_nonzero {x y : ℝ}
    (hI : x ∈ Set.Ioo (lo:ℝ) (hi:ℝ)) (hy : 0 < y) : residualCoeff.val x y ≠ 0 := by
  have ha : 0 < coeval resA x := coeval_pos hI (by decide +kernel)
  have hb : 0 < coeval resB x := coeval_pos hI (by decide +kernel)
  rw [residualCoeff, QExpr.val_scale]
  change coeval [resMult] x * (coeval resA x + y*coeval resB x) ≠ 0
  have hm : coeval [resMult] x = (resMult:ℝ) := by simp [coeval,horner]
  rw [hm]
  exact mul_ne_zero (Int.cast_ne_zero.mpr (by decide +kernel))
    (add_pos ha (mul_pos hy hb)).ne'

private theorem not_order_ten {K : Type*} [Field K] [CharZero K] {x y : K}
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) (hr : residualCoeff.val x y ≠ 0) :
    ¬ HasOrder 10 (A x y) (b x y) := by
  intro ho
  have ht := ho (tallTree 10) (by rw [order_tallTree]; decide)
  have hf : ((tallTree 10).factorial:ℕ) = 3628800 := calc
    _ = Nat.factorial 10 := factorial_tallTree (10 : ℕ+)
    _ = _ := by decide +kernel
  change (((tallTree 10).factorial:ℕ):K) * (b x y ⬝ᵥ Φ (tallTree 10) (A x y)) = 1 at ht
  rw [hf,Nat.cast_ofNat] at ht
  let d : K := stageDen
  let e : K := weightDen
  have hm :
      (3628800:K) * (VecVal x y rawB ⬝ᵥ Φ (tallTree 10) (numA x y)) = e*d^9 := by
    rw [← scale_A x y, ← scale_b x y, Φ_matrix_smul, order_tallTree, smul_dotProduct, dotProduct_smul]
    change 3628800 * (e * (d^9 * (b x y ⬝ᵥ Φ (tallTree 10) (A x y)))) = e*d^9
    calc
      _ = e*d^9 * (3628800 * (b x y ⬝ᵥ Φ (tallTree 10) (A x y))) := by ac_rfl
      _ = _ := by rw [ht, mul_one]
  have hz : e*d^9 + residualCoeff.val x y = e*d^9 + 0 :=
    (tenth_numerator hx hy).symm.trans (hm.trans (add_zero _).symm)
  exact hr (add_left_cancel hz)

theorem not_order_ten_real {x y : ℝ}
    (hI : x ∈ Set.Ioo (lo:ℝ) (hi:ℝ)) (hpos : 0 < y)
    (hx : coeval innerMod x = 0) (hy : y^2 = 7) :
    ¬ HasOrder 10 (A x y) (b x y) :=
  not_order_ten hx hy (residual_nonzero hI hpos)

theorem exists_exact_real :
    ∃ (U : Matrix (Fin 10) (Fin 10) ℝ) (w : Fin 10 → ℝ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  obtain ⟨x,y,hI,hp,hx,hy⟩ := exists_real_parameters
  exact ⟨A x y,b x y,lowerTriangular x y,first_row_zero x y,order_nine hx hy,
    not_order_ten_real hI hp hx hy⟩

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

theorem exists_exact_realAlgebraic :
    ∃ (U : Matrix (Fin 10) (Fin 10) ℝₐ) (w : Fin 10 → ℝₐ),
      U.IsLowerTriangular ∧ (∀ j, U 0 j = 0) ∧ HasOrder 9 U w ∧ ¬ HasOrder 10 U w := by
  obtain ⟨x,y,hI,hp,hx,hy⟩ := exists_realAlgebraic_parameters
  let f := algebraMap ℝₐ ℝ
  have hr : residualCoeff.val x y ≠ 0 := by
    intro h
    have hh := congrArg f h
    rw [map_qval, map_zero] at hh
    exact residual_nonzero hI hp hh
  exact ⟨A x y,b x y,lowerTriangular x y,first_row_zero x y,order_nine hx hy,
    not_order_ten hx hy hr⟩

end RKResearch.Certified.LobattoDIRK109
