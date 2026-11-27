module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

/-! # Scalar obstructions in the six-tail strict SDIRK7 chart

The coefficient receipts use normalized reflected-time moments
of the monic cubic formed from three literal clocks. The exceptional
K₀=0 branch is rejected over the rationals. This module does not
assume that every nine-stage tableau has this chart.
-/

namespace RKResearch.Certified.SDIRKSixTailScalarObstruction

private theorem reduced_pair_not_both_zero {p : ℕ} (hp : ¬ p ∣ 1) (x : ℚ)
    (ha : (x.num : ZMod p) = 0) (hb : (x.den : ZMod p) = 0) : False := by
  apply hp
  have han : p ∣ x.num.natAbs := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp ha
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hbn := (ZMod.natCast_eq_zero_iff x.den p).mp hb
  have hboth := Nat.dvd_gcd han hbn
  simpa only [x.reduced.gcd_eq_one] using hboth

private theorem check_pair_via_vals (p : ℕ) [NeZero p]
    (F : ZMod p → ZMod p → ZMod p)
    (h : ∀ a b : Fin p, F (a.val : ZMod p) (b.val : ZMod p) = 0 →
      (a.val : ZMod p) = 0 ∧ (b.val : ZMod p) = 0)
    {a b : ZMod p} (h₀ : F a b = 0) : a = 0 ∧ b = 0 := by
  have hn : F ((⟨a.val,a.val_lt⟩ : Fin p).val : ZMod p)
      ((⟨b.val,b.val_lt⟩ : Fin p).val : ZMod p) = 0 := by
    simpa only [ZMod.natCast_zmod_val] using h₀
  simpa only [ZMod.natCast_zmod_val] using h ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ hn


private def d3 (z : ℚ) : ℚ := z^3 - 12*z^2 + 60*z - 120
private def d3Hom {R : Type*} [CommRing R] (a b : R) : R := a^3 - 12*a^2*b + 60*a*b^2 - 120*b^3

set_option maxRecDepth 8192 in
private theorem d3_finite : ∀ a b : Fin 17,
    d3Hom (a.val : ZMod 17) (b.val : ZMod 17) = 0 →
      (a.val : ZMod 17) = 0 ∧ (b.val : ZMod 17) = 0 := by
  decide +kernel

private theorem d3_nonzero (x : ℚ) : d3 x ≠ 0 := by
  intro hx
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hscale : x * (x.den : ℚ) = (x.num : ℚ) := by
    nth_rw 1 [← x.num_div_den]
    exact div_mul_cancel₀ _ hden
  have hq : d3Hom (x.num : ℚ) (x.den : ℚ) = (x.den : ℚ)^3 * d3 x := by
    rw [←hscale]
    simp only [d3Hom, d3]
    ring
  rw [hx, mul_zero] at hq
  have hZ : d3Hom x.num (x.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [d3Hom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 17)) hZ
  have hp' : d3Hom (x.num : ZMod 17) (x.den : ZMod 17) = 0 := by
    simp only [d3Hom, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero, map_natCast] at hp
    simpa only [d3Hom, Int.coe_castRingHom] using hp
  obtain ⟨ha,hb⟩ := check_pair_via_vals 17 d3Hom d3_finite hp'
  exact reduced_pair_not_both_zero (by decide) x ha hb


private def projection (z : ℚ) : ℚ := 4*z^12 - 300*z^11 + 9420*z^10 - 167970*z^9 + 1921860*z^8 - 14982300*z^7 + 81764775*z^6 - 313324200*z^5 + 826410600*z^4 - 1430730000*z^3 + 1488942000*z^2 - 793800000*z + 158760000
private def projectionHom {R : Type*} [CommRing R] (a b : R) : R := 4*a^12 - 300*a^11*b + 9420*a^10*b^2 - 167970*a^9*b^3 + 1921860*a^8*b^4 - 14982300*a^7*b^5 + 81764775*a^6*b^6 - 313324200*a^5*b^7 + 826410600*a^4*b^8 - 1430730000*a^3*b^9 + 1488942000*a^2*b^10 - 793800000*a*b^11 + 158760000*b^12

set_option maxRecDepth 8192 in
private theorem projection_finite : ∀ a b : Fin 11,
    projectionHom (a.val : ZMod 11) (b.val : ZMod 11) = 0 →
      (a.val : ZMod 11) = 0 ∧ (b.val : ZMod 11) = 0 := by
  decide +kernel

private theorem projection_nonzero (x : ℚ) : projection x ≠ 0 := by
  intro hx
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hscale : x * (x.den : ℚ) = (x.num : ℚ) := by
    nth_rw 1 [← x.num_div_den]
    exact div_mul_cancel₀ _ hden
  have hq : projectionHom (x.num : ℚ) (x.den : ℚ) = (x.den : ℚ)^12 * projection x := by
    rw [←hscale]
    simp only [projectionHom, projection]
    ring
  rw [hx, mul_zero] at hq
  have hZ : projectionHom x.num (x.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [projectionHom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 11)) hZ
  have hp' : projectionHom (x.num : ZMod 11) (x.den : ZMod 11) = 0 := by
    simp only [projectionHom, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero, map_natCast] at hp
    simpa only [projectionHom, Int.coe_castRingHom] using hp
  obtain ⟨ha,hb⟩ := check_pair_via_vals 11 projectionHom projection_finite hp'
  exact reduced_pair_not_both_zero (by decide) x ha hb


private def fold (z : ℚ) : ℚ := z^3 - 9*z^2 + 18*z - 6
private def foldHom {R : Type*} [CommRing R] (a b : R) : R := a^3 - 9*a^2*b + 18*a*b^2 - 6*b^3

set_option maxRecDepth 8192 in
private theorem fold_finite : ∀ a b : Fin 5,
    foldHom (a.val : ZMod 5) (b.val : ZMod 5) = 0 →
      (a.val : ZMod 5) = 0 ∧ (b.val : ZMod 5) = 0 := by
  decide +kernel

private theorem fold_nonzero (x : ℚ) : fold x ≠ 0 := by
  intro hx
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hscale : x * (x.den : ℚ) = (x.num : ℚ) := by
    nth_rw 1 [← x.num_div_den]
    exact div_mul_cancel₀ _ hden
  have hq : foldHom (x.num : ℚ) (x.den : ℚ) = (x.den : ℚ)^3 * fold x := by
    rw [←hscale]
    simp only [foldHom, fold]
    ring
  rw [hx, mul_zero] at hq
  have hZ : foldHom x.num (x.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [foldHom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 5)) hZ
  have hp' : foldHom (x.num : ZMod 5) (x.den : ZMod 5) = 0 := by
    simp only [foldHom, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero, map_natCast] at hp
    simpa only [foldHom, Int.coe_castRingHom] using hp
  obtain ⟨ha,hb⟩ := check_pair_via_vals 5 foldHom fold_finite hp'
  exact reduced_pair_not_both_zero (by decide) x ha hb

/-- A normalized third chronological row cannot have all the pure
stage features through size four over the rationals. Here x is the
preceding clock, y the new clock, and a,b the two strict taps. -/
theorem no_rational_third_pure_stage {x y a b : ℚ}
    (h₁ : a+b+1=y) (h₂ : a+x*b+y=y^2/2)
    (h₃ : a+x^2*b+y^2=y^3/3) (h₄ : a+(4*x-2-x^2)*b=0) : False := by
  apply fold_nonzero y
  simp only [fold]
  linear_combination (norm := ring) -3*(h₄+h₃-4*h₂+2*h₁)

/-- The reflected fourth tail clock is either an arithmetic continuation
of the last two, or the indicated raw quadratic moment is zero. The
arguments are literal moments of the cubic nodal polynomial. -/
theorem fourth_clock_or_exceptional {K : Type*} [Field K] [CharZero K]
    {a u m0 m1 m2 m3 : K}
    (h : 2*m3-3*(u+3)*m2+(12*u+6)*m1-6*u*m0=0)
    (k : -m3+9*m2-18*m1+6*m0=0)
    (hclock : -m3+4*m2-2*m1 = a*(-m2+4*m1-2*m0)) :
    a=2*u-1 ∨ -m2+4*m1-2*m0=0 := by
  have hs : (a-(2*u-1))*(-m2+4*m1-2*m0)=0 := by
    linear_combination (norm := ring) -(1/3:K)*(2*h+k)-hclock
  exact (mul_eq_zero.mp hs).imp sub_eq_zero.mp id

-- Cleared I(L_1 * F_3), where F_3(y)=y^3+s*y^2+t*y+w.
def lagMoment1 (z s t w : ℚ) : ℚ := -15*s*z^3 + 20*s*z^2 - 20*t*z^2 + 30*t*z - 30*w*z + 60*w - 12*z^4 + 15*z^3

-- Cleared I(L_2 * F_3), where F_3(y)=y^3+s*y^2+t*y+w.
def lagMoment2 (z s t w : ℚ) : ℚ := 12*s*z^4 - 60*s*z^3 + 40*s*z^2 + 15*t*z^3 - 80*t*z^2 + 60*t*z + 20*w*z^2 - 120*w*z + 120*w + 10*z^5 - 48*z^4 + 30*z^3

-- Cleared I(L_3 * F_3), where F_3(y)=y^3+s*y^2+t*y+w.
def lagMoment3 (z s t w : ℚ) : ℚ := -70*s*z^5 + 756*s*z^4 - 1890*s*z^3 + 840*s*z^2 - 84*t*z^4 + 945*t*z^3 - 2520*t*z^2 + 1260*t*z - 105*w*z^3 + 1260*w*z^2 - 3780*w*z + 2520*w - 60*z^6 + 630*z^5 - 1512*z^4 + 630*z^3

-- Cleared I(L_3 * (F_3/(y-r))), the quotient by a selected root.
def bridgeMoment (z s t r : ℚ) : ℚ := -15*r^2*z^3 + 180*r^2*z^2 - 540*r^2*z + 360*r^2 - 15*r*s*z^3 + 180*r*s*z^2 - 540*r*s*z + 360*r*s - 12*r*z^4 + 135*r*z^3 - 360*r*z^2 + 180*r*z - 12*s*z^4 + 135*s*z^3 - 360*s*z^2 + 180*s*z - 15*t*z^3 + 180*t*z^2 - 540*t*z + 360*t - 10*z^5 + 108*z^4 - 270*z^3 + 120*z^2

private def clearedCubic (z r : ℚ) : ℚ := 35*r^3*z^3 - 420*r^3*z^2 + 2100*r^3*z - 4200*r^3 - 60*r^2*z^4 + 675*r^2*z^3 - 3240*r^2*z^2 + 6300*r^2*z + 30*r*z^5 - 300*r*z^4 + 1350*r*z^3 - 2520*r*z^2 - 4*z^6 + 30*z^5 - 120*z^4 + 210*z^3
private def clearedBridge (z r : ℚ) : ℚ := -105*r^2*z^6 + 2520*r^2*z^5 - 25200*r^2*z^4 + 136080*r^2*z^3 - 408240*r^2*z^2 + 604800*r^2*z - 302400*r^2 + 96*r*z^7 - 2232*r*z^6 + 21600*r*z^5 - 114480*r*z^4 + 345600*r*z^3 - 535680*r*z^2 + 302400*r*z - 16*z^8 + 336*z^7 - 2931*z^6 + 14640*z^5 - 44640*z^4 + 76320*z^3 - 55440*z^2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The exceptional rational six-tail moment system is inconsistent
for every nonzero reciprocal diagonal. These are the cleared
three Laguerre moments, the selected third nodal root, and its
two-clock causal bridge. -/
theorem exceptional_branch_impossible {z s t w r : ℚ} (hz : z ≠ 0)
    (h1 : lagMoment1 z s t w = 0) (h2 : lagMoment2 z s t w = 0)
    (h3 : lagMoment3 z s t w = 0)
    (hr : r^3+s*r^2+t*r+w = 0) (hb : bridgeMoment z s t r = 0) : False := by
  simp only [lagMoment1,lagMoment2,lagMoment3,bridgeMoment] at h1 h2 h3 hb
  have hc0 : (35*s*z^3 - 420*s*z^2 + 2100*s*z - 4200*s + 60*z^4 - 675*z^3 + 3240*z^2 - 6300*z) = 0 := by
    have hmul : (-z^4/5) * (35*s*z^3 - 420*s*z^2 + 2100*s*z - 4200*s + 60*z^4 - 675*z^3 + 3240*z^2 - 6300*z) = 0 := by
      linear_combination (norm := ring) (21*z^4 - 336*z^3 + 2016*z^2 - 5040*z + 5040)*h1 + (84*z^3 - 1008*z^2 + 3780*z - 5040)*h2 + (10*z^2 - 60*z + 120)*h3
    have hn : (-z^4/5) ≠ 0 := by
      rw [show (-z^4/5) = (-1/5 : ℚ) * z ^ 4 by ring]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ hz)
    exact (mul_eq_zero.mp hmul).resolve_left hn
  have hc1 : (35*t*z^3 - 420*t*z^2 + 2100*t*z - 4200*t - 30*z^5 + 300*z^4 - 1350*z^3 + 2520*z^2) = 0 := by
    have hmul : (-z^3/5) * (35*t*z^3 - 420*t*z^2 + 2100*t*z - 4200*t - 30*z^5 + 300*z^4 - 1350*z^3 + 2520*z^2) = 0 := by
      linear_combination (norm := ring) (-28*z^4 + 420*z^3 - 2352*z^2 + 5376*z - 5040)*h1 + (-105*z^3 + 1176*z^2 - 4032*z + 5040)*h2 + (-12*z^2 + 64*z - 120)*h3
    have hn : (-z^3/5) ≠ 0 := by
      rw [show (-z^3/5) = (-1/5 : ℚ) * z ^ 3 by ring]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ hz)
    exact (mul_eq_zero.mp hmul).resolve_left hn
  have hc2 : (35*w*z^3 - 420*w*z^2 + 2100*w*z - 4200*w + 4*z^6 - 30*z^5 + 120*z^4 - 210*z^3) = 0 := by
    have hmul : (-z^2) * (35*w*z^3 - 420*w*z^2 + 2100*w*z - 4200*w + 4*z^6 - 30*z^5 + 120*z^4 - 210*z^3) = 0 := by
      linear_combination (norm := ring) (42*z^4 - 560*z^3 + 2730*z^2 - 5040*z + 4200)*h1 + (140*z^3 - 1365*z^2 + 3780*z - 4200)*h2 + (15*z^2 - 60*z + 100)*h3
    have hn : (-z^2) ≠ 0 := by
      rw [show (-z^2) = (-1 : ℚ) * z ^ 2 by ring]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ hz)
    exact (mul_eq_zero.mp hmul).resolve_left hn
  have hC : clearedCubic z r = 0 := by
    simp only [clearedCubic]
    linear_combination (norm := ring) (35*z^3 - 420*z^2 + 2100*z - 4200)*hr-r^2*hc0-r*hc1-hc2
  have hB : clearedBridge z r = 0 := by
    simp only [clearedBridge]
    linear_combination (norm := ring) (7*z^3 - 84*z^2 + 420*z - 840)*hb-(-3*r*z^3 + 36*r*z^2 - 108*r*z + 72*r - 12*z^4/5 + 27*z^3 - 72*z^2 + 36*z)*hc0-(-3*z^3 + 36*z^2 - 108*z + 72)*hc1
  have hR : (16*z^16 - 1200*z^15 + 37680*z^14 - 671880*z^13 + 7687440*z^12 - 59929200*z^11 + 327059100*z^10 - 1253296800*z^9 + 3305642400*z^8 - 5722920000*z^7 + 5955768000*z^6 - 3175200000*z^5 + 635040000*z^4) = 0 := by
    simp only [clearedCubic,clearedBridge] at hC hB
    linear_combination (norm := ring) (-630*r*z^9 + 26460*r*z^8 - 462105*r*z^7 + 4381020*r*z^6 - 24664500*r*z^5 + 84709800*r*z^4 - 175316400*r*z^3 + 206841600*r*z^2 - 122472000*r*z + 27216000*r + 396*z^10 - 15930*z^9 + 266220*z^8 - 2411235*z^7 + 12956760*z^6 - 42549300*z^5 + 84888000*z^4 - 98658000*z^3 + 59875200*z^2 - 13608000*z)*hC+(-210*r^2*z^6 + 6300*r^2*z^5 - 70875*r^2*z^4 + 378000*r^2*z^3 - 982800*r^2*z^2 + 1134000*r^2*z - 378000*r^2 + 300*r*z^7 - 8640*r*z^6 + 92700*r*z^5 - 467100*r*z^4 + 1134000*r*z^3 - 1209600*r*z^2 + 378000*r*z - 100*z^8 + 2700*z^7 - 26730*z^6 + 121200*z^5 - 255150*z^4 + 226800*z^3 - 63000*z^2)*hB
  apply projection_nonzero z
  have hFact : (4*z^4)*projection z = 0 := by
    simp only [projection]
    linear_combination (norm := ring) hR
  exact (mul_eq_zero.mp hFact).resolve_left (mul_ne_zero ((by decide)) (pow_ne_zero 4 hz))

private def quarterQuadratic (z : ℚ) : ℚ := z^2 - 9*z + 12
private def quarterQuadraticHom {R : Type*} [CommRing R] (a b : R) : R := a^2 - 9*a*b + 12*b^2

set_option maxRecDepth 8192 in
private theorem quarterQuadratic_finite : ∀ a b : Fin 5,
    quarterQuadraticHom (a.val : ZMod 5) (b.val : ZMod 5) = 0 →
      (a.val : ZMod 5) = 0 ∧ (b.val : ZMod 5) = 0 := by
  decide +kernel

private theorem quarterQuadratic_nonzero (x : ℚ) : quarterQuadratic x ≠ 0 := by
  intro hx
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hscale : x * (x.den : ℚ) = (x.num : ℚ) := by
    nth_rw 1 [← x.num_div_den]
    exact div_mul_cancel₀ _ hden
  have hq : quarterQuadraticHom (x.num : ℚ) (x.den : ℚ) = (x.den : ℚ)^2 * quarterQuadratic x := by
    rw [←hscale]
    simp only [quarterQuadraticHom, quarterQuadratic]
    ring
  rw [hx, mul_zero] at hq
  have hZ : quarterQuadraticHom x.num (x.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [quarterQuadraticHom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 5)) hZ
  have hp' : quarterQuadraticHom (x.num : ZMod 5) (x.den : ZMod 5) = 0 := by
    simp only [quarterQuadraticHom, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero, map_natCast] at hp
    simpa only [quarterQuadraticHom, Int.coe_castRingHom] using hp
  obtain ⟨ha,hb⟩ := check_pair_via_vals 5 quarterQuadraticHom quarterQuadratic_finite hp'
  exact reduced_pair_not_both_zero (by decide) x ha hb

private def quarterProjection (z : ℚ) : ℚ := 20402*z^12 - 768913*z^11 + 8128142*z^10 - 43335356*z^9 + 155297272*z^8 - 438009074*z^7 + 953817368*z^6 - 1422950776*z^5 + 1276150142*z^4 - 563936949*z^3 + 48635370*z^2 + 27831276*z - 2648376
private def quarterProjectionHom {R : Type*} [CommRing R] (a b : R) : R := 20402*a^12 - 768913*a^11*b + 8128142*a^10*b^2 - 43335356*a^9*b^3 + 155297272*a^8*b^4 - 438009074*a^7*b^5 + 953817368*a^6*b^6 - 1422950776*a^5*b^7 + 1276150142*a^4*b^8 - 563936949*a^3*b^9 + 48635370*a^2*b^10 + 27831276*a*b^11 - 2648376*b^12

set_option maxRecDepth 8192 in
private theorem quarterProjection_finite : ∀ a b : Fin 17,
    quarterProjectionHom (a.val : ZMod 17) (b.val : ZMod 17) = 0 →
      (a.val : ZMod 17) = 0 ∧ (b.val : ZMod 17) = 0 := by
  decide +kernel

private theorem quarterProjection_nonzero (x : ℚ) : quarterProjection x ≠ 0 := by
  intro hx
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hscale : x * (x.den : ℚ) = (x.num : ℚ) := by
    nth_rw 1 [← x.num_div_den]
    exact div_mul_cancel₀ _ hden
  have hq : quarterProjectionHom (x.num : ℚ) (x.den : ℚ) = (x.den : ℚ)^12 * quarterProjection x := by
    rw [←hscale]
    simp only [quarterProjectionHom, quarterProjection]
    ring
  rw [hx, mul_zero] at hq
  have hZ : quarterProjectionHom x.num (x.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [quarterProjectionHom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 17)) hZ
  have hp' : quarterProjectionHom (x.num : ZMod 17) (x.den : ZMod 17) = 0 := by
    simp only [quarterProjectionHom, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero, map_natCast] at hp
    simpa only [quarterProjectionHom, Int.coe_castRingHom] using hp
  obtain ⟨ha,hb⟩ := check_pair_via_vals 17 quarterProjectionHom quarterProjection_finite hp'
  exact reduced_pair_not_both_zero (by decide) x ha hb

-- Cleared F3 moment against L3 in y=4 times normalized time.
def qF3m1 (_u s t w : ℚ) : ℚ := 448*s + 462*t + 420*w + 411

-- Cleared F3 moment against L1+(u-3)L2 in y=4 times normalized time.
def qF3m2 (u s t w : ℚ) : ℚ := -4*s*u - 28*s - 10*t*u - 20*t - 20*u*w - u - 30

-- Cleared F3 moment against the terminal cubic in y=4 times normalized time.
def qF3m3 (u s t w : ℚ) : ℚ := 560*s*u^2 - 3052*s*u + 4060*s + 700*t*u^2 - 3710*t*u + 4816*t + 840*u^2*w + 462*u^2 - 4620*u*w - 2583*u + 5880*w + 3504

-- Cleared F2 moment against T Q in y=4 times normalized time.
def qF2m1 (u p q : ℚ) : ℚ := 33*p*u^3 - 276*p*u^2 + 513*p*u - 246*p + 30*q*u^3 - 300*q*u^2 + 630*q*u - 360*q + 32*u^3 - 242*u^2 + 416*u - 174

-- Cleared F2 moment against y T Q in y=4 times normalized time.
def qF2m2 (u p q : ℚ) : ℚ := 448*p*u^3 - 3388*p*u^2 + 5824*p*u - 2436*p + 462*q*u^3 - 3864*q*u^2 + 7182*q*u - 3444*q + 411*u^3 - 2940*u^2 + 4791*u - 1782

private def qD3 (u : ℚ) : ℚ := 280*u^3 + 1540*u^2 - 5600*u + 3780
private def qS3 (u : ℚ) : ℚ := -300*u^3 - 3270*u^2 + 11400*u - 8550
private def qT3 (u : ℚ) : ℚ := 2340*u^2 - 7680*u + 6300
private def qD2 (u : ℚ) : ℚ := 1806*u^6 - 18984*u^5 + 67116*u^4 - 75768*u^3 - 34146*u^2 + 97776*u - 29736
private def qS2 (u : ℚ) : ℚ := -2454*u^6 + 23952*u^5 - 72444*u^4 + 45144*u^3 + 117834*u^2 - 165048*u + 42264
private def qT2 (u : ℚ) : ℚ := 773*u^6 - 6376*u^5 + 12246*u^4 + 15728*u^3 - 71047*u^2 + 66000*u - 14508

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- At common diagonal 1/4, the remaining arithmetic-tail scalar chart
is also impossible over the rationals. Its input is the two initial nodal
polynomials with the forced paid chronology equations. -/
theorem generic_quarter_impossible {u s t w p q : ℚ} (hu : u ≠ 1)
    (h1 : qF3m1 u s t w = 0) (h2 : qF3m2 u s t w = 0) (h3 : qF3m3 u s t w = 0)
    (h4 : qF2m1 u p q = 0) (h5 : qF2m2 u p q = 0)
    (hd : p^2-q-s*p+t=0) : False := by
  simp only [qF3m1,qF3m2,qF3m3,qF2m1,qF2m2] at h1 h2 h3 h4 h5
  have hs : qD3 u * s - qS3 u = 0 := by
    simp only [qD3,qS3]
    linear_combination (norm := ring) (25*u^3 - 200*u^2 + 580*u - 525)*h1 + (-420*u^2 + 5145*u/2 - 6195/2)*h2 + (75/2 - 45*u/2)*h3
  have ht : qD3 u * t - qT3 u = 0 := by
    simp only [qD3,qT3]
    linear_combination (norm := ring) (-35*u^3 + 295*u^2 - 835*u + 735)*h1 + (630*u^2 - 7035*u/2 + 8295/2)*h2 + (65*u/2 - 105/2)*h3
  have hp : qD2 u * p - qS2 u = 0 := by
    simp only [qD2,qS2]
    linear_combination (norm := ring) (462*u^3 - 3864*u^2 + 7182*u - 3444)*h4 + (-30*u^3 + 300*u^2 - 630*u + 360)*h5
  have hq : qD2 u * q - qT2 u = 0 := by
    simp only [qD2,qT2]
    linear_combination (norm := ring) (-448*u^3 + 3388*u^2 - 5824*u + 2436)*h4 + (33*u^3 - 276*u^2 + 513*u - 246)*h5
  have hE : ((qS2 u)^2-qT2 u*qD2 u)*qD3 u
      -qS3 u*qS2 u*qD2 u+qT3 u*(qD2 u)^2=0 := by
    linear_combination (norm := ring)
      (qD3 u)*(qD2 u)^2*hd-(qD3 u)*(qD2 u*p+qS2 u)*hp
        +(qD3 u)*(qD2 u)*hq+(qD2 u)*(qD3 u)*s*hp+(qD2 u)*(qS2 u)*hs-(qD2 u)^2*ht
  have hh : ((-1680 : ℚ)*(u-1)*quarterQuadratic u)*quarterProjection u=0 := by
    simp only [qD3,qS3,qT3,qD2,qS2,qT2,quarterQuadratic,quarterProjection] at hE ⊢
    linear_combination (norm := ring) hE
  exact quarterProjection_nonzero u ((mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hu)) (quarterQuadratic_nonzero u)))

open scoped Matrix

private theorem mulVecThree (A : Matrix (Fin 3) (Fin 3) ℚ) (c : Fin 3 → ℚ)
    (i : Fin 3) : (A *ᵥ c) i = A i 0 * c 0 + A i 1 * c 1 + A i 2 * c 2 := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp [Fin.sum_univ_succ]; ring

/-- Literal three-row prefix obstruction. The final three assumptions
are the order-two, bush order-three and tall order-three stage
requirements, equivalently the elementary stage profiles through
rooted size four when all of them are imposed at the third stage. -/
theorem no_rational_diagonal_one_third_pure
    (A : Matrix (Fin 3) (Fin 3) ℚ) (ha : A.IsLowerTriangular)
    (hd : ∀ i, A i i = 1) (c : Fin 3 → ℚ) (hc : c = A *ᵥ 1)
    (hLin : (A *ᵥ c) 2 = (c 2)^2/2)
    (hBush : (A *ᵥ (c^2)) 2 = (c 2)^3/3)
    (hTall : (A *ᵥ (A *ᵥ c)) 2 = (c 2)^3/6) : False := by
  have z01 : A 0 1 = 0 := ha (by decide)
  have z02 : A 0 2 = 0 := ha (by decide)
  have z12 : A 1 2 = 0 := ha (by decide)
  have c0 : c 0 = 1 := by rw [hc,mulVecThree,hd 0,z01,z02]; simp
  have c1 : c 1 = A 1 0 + 1 := by rw [hc,mulVecThree,hd 1,z12]; simp
  have c2 : A 2 0 + A 2 1 + 1 = c 2 := by rw [hc,mulVecThree,hd 2]; simp
  have j0 : (A *ᵥ c) 0 = 1 := by rw [mulVecThree,c0,hd 0,z01,z02]; simp
  have j1 : (A *ᵥ c) 1 = 2*c 1-1 := by
    rw [mulVecThree,c0,hd 1,z12]
    linear_combination (norm := ring) -c1
  have h2 : A 2 0 + c 1 * A 2 1 + c 2 = (c 2)^2/2 := by
    rw [mulVecThree,c0,hd 2] at hLin
    linear_combination (norm := ring) hLin
  have h3 : A 2 0 + (c 1)^2 * A 2 1 + (c 2)^2 = (c 2)^3/3 := by
    rw [mulVecThree,hd 2] at hBush
    simp only [Pi.pow_apply,c0,one_pow,mul_one,one_mul] at hBush
    linear_combination (norm := ring) hBush
  have ht : A 2 0 + (2*c 1-1) * A 2 1 + (c 2)^2/2 = (c 2)^3/6 := by
    rw [mulVecThree,j0,j1,hd 2,hLin] at hTall
    linear_combination (norm := ring) hTall
  have h4 : A 2 0 + (4*c 1-2-(c 1)^2)*A 2 1 = 0 := by
    linear_combination (norm := ring) 2*ht-h3
  exact no_rational_third_pure_stage c2 h2 h3 h4

end RKResearch.Certified.SDIRKSixTailScalarObstruction
