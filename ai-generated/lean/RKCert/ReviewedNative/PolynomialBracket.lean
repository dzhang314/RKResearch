module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact rational brackets for real polynomial roots

This module does not require a topology import. A closed Horner calculation
certifies interval signs; a simple Lipschitz bound supplies the needed
sign-change theorem from real completeness. -/

namespace RKCert.ReviewedNative.PolynomialBracket

open Polynomial

/-- Implicit ascending coefficients, with no approximate arithmetic. -/
def horner {R : Type*} [Semiring R] : List R → R → R
  | [], _ => 0
  | c::cs, x => c + x * horner cs x

theorem map_horner {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (cs : List R) (x : R) : f (horner cs x) = horner (cs.map f) (f x) := by
  induction cs with
  | nil => exact map_zero f
  | cons c cs ih => simp only [horner,List.map_cons,map_add,map_mul,ih]

/-- The actual rational polynomial behind the Horner list. -/
noncomputable def ofCoeffs : List ℚ → ℚ[X]
  | [] => 0
  | c::cs => C c + X * ofCoeffs cs

theorem coeff_ofCoeffs (cs : List ℚ) (i : ℕ) :
    (ofCoeffs cs).coeff i = cs[i]?.getD 0 := by
  induction cs generalizing i with
  | nil => simp [ofCoeffs]
  | cons c cs ih =>
    cases i with
    | zero => simp [ofCoeffs]
    | succ i => simp [ofCoeffs, coeff_X_mul, ih]

theorem eval₂_ofCoeffs {R : Type*} [CommSemiring R] (f : ℚ →+* R)
    (cs : List ℚ) (x : R) :
    eval₂ f x (ofCoeffs cs) = horner (cs.map f) x := by
  induction cs with
  | nil => simp [ofCoeffs,horner]
  | cons c cs ih =>
    simp only [ofCoeffs, horner,List.map_cons,eval₂_add,eval₂_mul,eval₂_C,eval₂_X,ih]

/-- Lower and upper Horner endpoints for a nonnegative input interval. -/
def box {R : Type*} [LinearOrder R] [Semiring R] (lo hi : R) : List R → R × R
  | [] => (0,0)
  | c::cs =>
    let b := box lo hi cs
    (c+min (lo*b.1) (hi*b.1),c+max (lo*b.2) (hi*b.2))

theorem box_real_sound {lo hi x : ℝ} (hl : 0 ≤ lo) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (cs : List ℝ) : (box lo hi cs).1 ≤ horner cs x ∧ horner cs x ≤ (box lo hi cs).2 := by
  induction cs with
  | nil => simp [box,horner]
  | cons c cs ih =>
    have hx : 0 ≤ x := hl.trans hlo
    simp only [box,horner]
    constructor
    · apply add_le_add_right
      have h := mul_le_mul_of_nonneg_left ih.1 hx
      refine le_trans ?_ h
      by_cases hn : 0 ≤ (box lo hi cs).1
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hlo hn)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hhi (le_of_not_ge hn))
    · apply add_le_add_right
      have h := mul_le_mul_of_nonneg_left ih.2 hx
      refine h.trans ?_
      by_cases hn : 0 ≤ (box lo hi cs).2
      · exact (mul_le_mul_of_nonneg_right hhi hn).trans (le_max_right _ _)
      · exact (mul_le_mul_of_nonpos_right hlo (le_of_not_ge hn)).trans (le_max_left _ _)

theorem box_ratCast (lo hi : ℚ) (cs : List ℚ) :
    box (lo:ℝ) (hi:ℝ) (cs.map (Rat.castHom ℝ)) =
      (((box lo hi cs).1:ℝ), ((box lo hi cs).2:ℝ)) := by
  induction cs with
  | nil => simp [box]
  | cons c cs ih =>
    simp only [List.map_cons,box,ih]
    simp [Rat.cast_min,Rat.cast_max]

/-- Rational Horner enclosures prove strict positivity at all points in the bracket. -/
theorem horner_pos_of_box {lo hi : ℚ} {x : ℝ}
    (hl : 0 ≤ (lo:ℝ)) (hlo : (lo:ℝ) ≤ x) (hhi : x ≤ (hi:ℝ))
    (cs : List ℚ) (hp : 0 < (box lo hi cs).1) :
    0 < horner (cs.map (Rat.castHom ℝ)) x := by
  have hb := (box_real_sound hl hlo hhi (cs.map (Rat.castHom ℝ))).1
  rw [box_ratCast] at hb
  exact (show (0:ℝ) < ((box lo hi cs).1:ℝ) by exact_mod_cast hp).trans_le hb

private def mag (B : ℝ) : List ℝ → ℝ
  | [] => 0
  | c::cs => |c|+B*mag B cs

private def lip (B : ℝ) : List ℝ → ℝ
  | [] => 0
  | _::cs => mag B cs+B*lip B cs

private theorem mag_nonneg {B : ℝ} (hb : 0 ≤ B) (cs : List ℝ) : 0 ≤ mag B cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih => exact add_nonneg (abs_nonneg _) (mul_nonneg hb ih)

private theorem lip_nonneg {B : ℝ} (hb : 0 ≤ B) (cs : List ℝ) : 0 ≤ lip B cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih => exact add_nonneg (mag_nonneg hb cs) (mul_nonneg hb ih)

private theorem bound_mag {B x : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) (cs : List ℝ) :
    |horner cs x| ≤ mag B cs := by
  induction cs with
  | nil => simp [horner,mag]
  | cons c cs ih =>
    simp only [horner,mag]
    calc
      _ ≤ |c| + |x*horner cs x| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add_right (mul_le_mul hx ih (abs_nonneg _) hB) _

private theorem bound_lip {B x y : ℝ} (hB : 0 ≤ B)
    (hx : |x| ≤ B) (hy : |y| ≤ B) (cs : List ℝ) :
    |horner cs x - horner cs y| ≤ lip B cs * |x-y| := by
  induction cs with
  | nil => simp [horner,lip]
  | cons c cs ih =>
    simp only [horner,lip]
    rw [show (c+x*horner cs x)-(c+y*horner cs y) =
      x*(horner cs x-horner cs y)+(x-y)*horner cs y by ring]
    calc
      _ ≤ |x| * |horner cs x-horner cs y| + |x-y| * |horner cs y| := by
        simpa only [abs_mul] using abs_add_le (x*(horner cs x-horner cs y)) ((x-y)*horner cs y)
      _ ≤ B*(lip B cs * |x-y|) + |x-y| * mag B cs :=
        add_le_add (mul_le_mul hx ih (abs_nonneg _) hB)
          (mul_le_mul_of_nonneg_left (bound_mag hB hy cs) (abs_nonneg _))
      _ = _ := by ring

private theorem exists_root_of_bound {a b M : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hM : 0 < M) (ha : f a < 0) (hb : 0 < f b)
    (hbound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ M * |x - y|) :
    ∃ x ∈ Set.Ioo a b, f x = 0 := by
  let S := {x : ℝ | x ∈ Set.Icc a b ∧ f x ≤ 0}
  have haS : a ∈ S := ⟨⟨le_rfl, hab.le⟩, ha.le⟩
  have hs : S.Nonempty := ⟨a, haS⟩
  have hB : BddAbove S := ⟨b, fun _ hx => hx.1.2⟩
  let c := sSup S
  have hc : c ∈ Set.Icc a b := ⟨le_csSup hB haS, csSup_le hs fun _ hx => hx.1.2⟩
  have hfc : f c ≤ 0 := by
    by_contra! hn
    let d := f c / M
    have hd : 0 < d := div_pos hn hM
    obtain ⟨x, hx, hxc⟩ := exists_lt_of_lt_csSup hs (sub_lt_self c hd)
    have hxle : x ≤ c := le_csSup hB hx
    have hclose : |x-c| < d := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxle)]
      linarith only [hxc]
    have hscaled := (lt_div_iff₀ hM).mp hclose
    have hfx := (abs_le.mp (hbound x hx.1 c hc)).1
    rw [mul_comm M] at hfx
    linarith only [hx.2, hfx, hscaled]
  have hcb : c < b := lt_of_le_of_ne hc.2 (by
    intro h
    rw [h] at hfc
    exact hb.not_ge hfc)
  have hfc' : 0 ≤ f c := by
    by_contra! hn
    let d := min ((b-c)/2) (-f c/M)
    have hd : 0 < d := lt_min (by linarith only [hcb]) (div_pos (neg_pos.mpr hn) hM)
    have hd' : d ≤ (b-c)/2 := min_le_left _ _
    have hd'' : d ≤ -f c/M := min_le_right _ _
    let x := c+d
    have hcx : c < x := lt_add_of_pos_right _ hd
    have hx : x ∈ Set.Icc a b := ⟨hc.1.trans hcx.le, by dsimp [x]; linarith only [hcb, hd']⟩
    have hclose : |x-c| = d := by
      rw [show x-c = d by dsimp [x]; ring, abs_of_pos hd]
    have hfx := (abs_le.mp (hbound x hx c hc)).2
    rw [hclose, mul_comm M] at hfx
    have hscaled := (le_div_iff₀ hM).mp hd''
    have hxS : x ∈ S := ⟨hx, by linarith only [hfx, hscaled]⟩
    exact hcx.not_ge (le_csSup hB hxS)
  have hzero : f c = 0 := le_antisymm hfc hfc'
  have hac : a < c := lt_of_le_of_ne hc.1 (by
    intro h
    rw [← h] at hzero
    exact ha.ne hzero)
  exact ⟨c, ⟨hac, hcb⟩, hzero⟩


/-- A sign-changing interval whose endpoints are bounded by the same radius. -/
theorem exists_real_horner_root {lo hi B : ℝ} (hlo : lo < hi) (hloB : -B ≤ lo) (hhiB : hi ≤ B)
    (cs : List ℝ) (ha : horner cs lo < 0) (hb : 0 < horner cs hi) :
    ∃ x ∈ Set.Ioo lo hi, horner cs x = 0 := by
  have hB : 0 ≤ B := by linarith only [hlo,hloB,hhiB]
  have hab (x : ℝ) (hx : x ∈ Set.Icc lo hi) : |x| ≤ B :=
    abs_le.mpr ⟨hloB.trans hx.1,hx.2.trans hhiB⟩
  exact exists_root_of_bound hlo (a:=lo) (b:=hi) (M:=1+lip B cs)
    (by linarith only [lip_nonneg hB cs]) ha hb (by
      intro x hx y hy
      have h := bound_lip hB (hab x hx) (hab y hy) cs
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)))

end RKCert.ReviewedNative.PolynomialBracket
