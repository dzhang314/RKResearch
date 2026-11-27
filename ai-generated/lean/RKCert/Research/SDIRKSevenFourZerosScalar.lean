module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Rational double-opening receipts for four silent strict SDIRK stages

The scalar AP chronology is separated from the stage-space argument. -/

namespace RKResearch.Certified.SDIRKSevenFourZerosScalar

def coeffA (t : ℚ) : ℚ := -(t-2)*(t-1)^2
def coeffB (t : ℚ) : ℚ := 2*t*(t-2)*(2*t-1)
def coeffC (t : ℚ) : ℚ := -2*t^2*(t-1)
def q (t w : ℚ) : ℚ := coeffA t*w^2+coeffB t*w+coeffC t
def jq (t w : ℚ) : ℚ := coeffA t*w^3/3+coeffB t*w^2/2+coeffC t*w
def jxq (t w : ℚ) : ℚ := coeffA t*w^4/4+coeffB t*w^3/3+coeffC t*w^2/2

def firstPoly (t w : ℚ) : ℚ :=
  2*coeffA t*(w^3-3*w^2)+3*coeffB t*(w^2-2*w)+6*coeffC t*(w-1)
def secondPoly (t w : ℚ) : ℚ := coeffA t*w^2+2*coeffB t*w+6*coeffC t

private def sexticHom {R : Type*} [CommRing R] (a b : R) : R :=
  a^6-19*a^5*b+112*a^4*b^2-218*a^3*b^3+41*a^2*b^4+121*a*b^5-54*b^6
def sextic (a : ℚ) : ℚ := a^6-19*a^5+112*a^4-218*a^3+41*a^2+121*a-54

set_option maxRecDepth 8192 in
private theorem sextic_mod : ∀ a b : Fin 5,
    sexticHom (a.val : ZMod 5) (b.val : ZMod 5)=0 →
      (a.val : ZMod 5)=0 ∧ (b.val : ZMod 5)=0 := by decide +kernel

theorem sextic_ne (x : ℚ) : sextic x≠0 := by
  intro e
  have hd : (x.den : ℚ)≠0 := by exact_mod_cast x.den_nz
  have scale : x*(x.den : ℚ)=(x.num : ℚ) := by
    nth_rw 1 [←x.num_div_den]
    exact div_mul_cancel₀ _ hd
  have hx : sexticHom (x.num : ℚ) (x.den : ℚ)=(x.den : ℚ)^6*sextic x := by
    rw [←scale]
    simp only [sexticHom,sextic]
    ring
  rw [e,mul_zero] at hx
  have hz : sexticHom x.num (x.den : ℤ)=0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [sexticHom,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      Int.cast_natCast,Int.cast_zero] using hx
  have hp := congrArg (Int.castRingHom (ZMod 5)) hz
  have h₅ : sexticHom (x.num : ZMod 5) (x.den : ZMod 5)=0 := by
    simp only [sexticHom,map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero,map_natCast] at hp
    simpa only [sexticHom,Int.coe_castRingHom] using hp
  let a : ZMod 5 := x.num
  let b : ZMod 5 := x.den
  have hv : sexticHom (a.val : ZMod 5) (b.val : ZMod 5)=0 := by
    simpa only [ZMod.natCast_zmod_val] using h₅
  obtain ⟨ha,hb⟩ := sextic_mod ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ hv
  have han : (5:ℕ) ∣ x.num.natAbs := by
    have h : (x.num : ZMod 5)=0 := by simpa only [ZMod.natCast_zmod_val,a] using ha
    simpa using (Int.natAbs_dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num 5).mp h))
  have hbn : (5:ℕ) ∣ x.den := by
    have h : (x.den : ZMod 5)=0 := by simpa only [ZMod.natCast_zmod_val,b] using hb
    exact (ZMod.natCast_eq_zero_iff x.den 5).mp h
  have bad := Nat.dvd_gcd han hbn
  rw [x.reduced.gcd_eq_one] at bad
  exact (by decide : ¬ (5:ℕ) ∣ 1) bad

def bezoutU (t w : ℚ) : ℚ :=
  -t*(t-2)*(5*t^5-67*t^4+216*t^3-220*t^2+83*t-9)+
  (t-2)*(t-1)^2*(t^4-12*t^3+33*t^2-26*t+6)*w

def bezoutV (t w : ℚ) : ℚ :=
  -6*t*(t^6-16*t^5+77*t^4-145*t^3+94*t^2-9*t-6)+
  6*(t-2)*(2*t^6-28*t^5+104*t^4-149*t^3+106*t^2-39*t+6)*w-
  2*(t-2)*(t-1)^2*(t^4-12*t^3+33*t^2-26*t+6)*w^2

theorem bezout (t w : ℚ) :
    bezoutU t w*firstPoly t w+bezoutV t w*secondPoly t w =
      12*t^3*(t-1)*sextic t := by
  simp only [bezoutU,bezoutV,firstPoly,secondPoly,coeffA,coeffB,coeffC,sextic]
  ring

/-- The two exact first-tail primitive reads for an AP rank-two
opening leave only the linear seed and the zero active clock. -/
theorem double_opening {t w : ℚ} (ht : t≠0)
    (h : jq t w=q t w) (k : jxq t w=w*q t w) :
    t=1 ∧ w=0 := by
  have f : firstPoly t w=0 := by
    simp only [firstPoly,q,jq] at h ⊢
    linear_combination 6*h
  by_cases hw : w=0
  · rw [hw] at f
    have tval : (12*t^2)*(t-1)=0 := by
      simp only [firstPoly,coeffA,coeffB,coeffC] at f
      linear_combination f
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp tval).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero _ ht))),hw⟩
  · have z : w^2*secondPoly t w=0 := by
      simp only [secondPoly,jxq,jq,q] at h k ⊢
      linear_combination 12*w*h-12*k
    have g : secondPoly t w=0 :=
      ((mul_eq_zero.mp z).resolve_left (pow_ne_zero _ hw))
    have id := bezout t w
    rw [f,g,mul_zero,mul_zero,add_zero] at id
    have h1 : t=1 := sub_eq_zero.mp ((mul_eq_zero.mp
      ((mul_eq_zero.mp id.symm).resolve_right (sextic_ne t))).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero _ ht)))
    rw [h1] at g
    have wz : -4*w=0 := by
      simp only [secondPoly,coeffA,coeffB,coeffC] at g
      linear_combination g
    exact False.elim (hw ((mul_eq_zero.mp wz).resolve_left (by norm_num)))


def seed (v : ℚ) : ℚ := 1+2*v-v^2
def headDen (t : ℚ) : ℚ := t^3-4*t^2-t+2

/-- The rank-two local third row either duplicates a prior row,
lies on the zero-middle-tap reflected branch, or is arithmetic. -/
theorem head_cases {t w r : ℚ} (ht : t≠0)
    (com : r*t*(2*t-w)=0)
    (read : w*(seed w+2*r*t)=seed t*(w+r*(seed t-1))) :
    (r=0 ∧ (w=0 ∨ w=t ∨ w=2-t)) ∨
      (w=2*t ∧ headDen t*r=-2*t*(3*t-2)) := by
  by_cases hr : r=0
  · refine Or.inl ⟨hr,?_⟩
    rw [hr] at read
    have e : w*(w-t)*(2-w-t)=0 := by
      simp only [seed] at read
      linear_combination read
    rcases mul_eq_zero.mp e with e | e
    · rcases mul_eq_zero.mp e with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (sub_eq_zero.mp e))
    · exact Or.inr (Or.inr (by linear_combination -e))
  · have e : w=2*t := (sub_eq_zero.mp ((mul_eq_zero.mp com).resolve_left
      (mul_ne_zero hr ht))).symm
    rw [e] at read
    have f : t*(headDen t*r+2*t*(3*t-2))=0 := by
      simp only [seed,headDen] at read ⊢
      linear_combination -read
    have z := (mul_eq_zero.mp f).resolve_left ht
    exact Or.inr ⟨e,by linear_combination z⟩

theorem head_den_ne {t r : ℚ} (ht : t≠0)
    (h : headDen t*r=-2*t*(3*t-2)) : headDen t≠0 := by
  intro d
  rw [d,zero_mul] at h
  have t' : 3*t-2=0 := (mul_eq_zero.mp h.symm).resolve_left
    (mul_ne_zero (by norm_num) ht)
  have tv : t=2/3 := by linear_combination t'/3
  rw [tv] at d
  norm_num [headDen] at d

/-- The cleared polynomial interpolates all three actual AP seeds,
with its common scale protected by the third-row read. -/
theorem ap_interpolation {t r : ℚ}
    (h : headDen t*r=-2*t*(3*t-2)) :
    q t 1=headDen t ∧ q t (1+t)=headDen t*seed t ∧
      q t (1+2*t)=headDen t*(seed (2*t)+2*r*t) := by
  refine ⟨?_,?_,?_⟩
  · simp only [q,coeffA,coeffB,coeffC,headDen]
    ring
  · simp only [q,coeffA,coeffB,coeffC,headDen,seed]
    ring
  · simp only [q,coeffA,coeffB,coeffC,headDen,seed] at h ⊢
    linear_combination -2*t*h
/-- A first active zero clock fed by prior clocks 1,2,3 cannot
be quartic clean at unit diagonal. -/
theorem zero_clock_three_prior {a b c : ℚ}
    (h₀ : a+b+c+1=0) (h₁ : a+2*b+3*c=0)
    (h₂ : a+4*b+9*c=0) (h₃ : a+8*b+27*c=0) : False := by
  have e : (1:ℚ)=0 := by linear_combination h₀-(11/6:ℚ)*h₁+h₂-h₃/6
  norm_num at e

/-- An active clock following one zero active clock cannot
satisfy both pure primitives at unit diagonal. -/
theorem second_active_impossible {x : ℚ} (hx : x≠0)
    (h₂ : x=x^2/2) (h₃ : x^2=x^3/3) : False := by
  have p : x*(x-2)=0 := by linear_combination -2*h₂
  have q : x^2*(x-3)=0 := by linear_combination -3*h₃
  have e : x=2 := sub_eq_zero.mp ((mul_eq_zero.mp p).resolve_left hx)
  have f : x=3 := sub_eq_zero.mp ((mul_eq_zero.mp q).resolve_left (pow_ne_zero _ hx))
  rw [e] at f
  norm_num at f

/-- Scalar quotient receipt for the saturated three-dimensional
zero-profile space on four ghost coordinates. -/
theorem invariant_mass_zero {v m : ℚ}
    (h₁ : (v-1)*m=0) (h₂ : (2*v-v^2)*m=0) : m=0 := by
  by_contra hm
  have w : v=1 := sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_right hm)
  rw [w] at h₂
  have h : m=0 := by linear_combination h₂
  exact hm h

end RKResearch.Certified.SDIRKSevenFourZerosScalar
