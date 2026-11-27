module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar gates for reflection-paired order-seven clocks

The tail and head ingress assumptions are scalar. The chronological
eliminations for particular forward heads have a separate exact replay. -/

namespace RKResearch.Certified.SDIRKSevenPairedClean

section field
variable {K : Type*} [Field K]

/-- Five symmetrically placed sites and one unmatched site cannot
carry six nonzero masses at centered odd degree five. -/
theorem odd_quintic_zero_mass {a b c wa wb wd we wf : K}
    (hc : c≠0) (ha : c^2≠a^2) (hb : c^2≠b^2)
    (h₁ : (wa-wb)*a+(wd-we)*b+wf*c=0)
    (h₃ : (wa-wb)*a^3+(wd-we)*b^3+wf*c^3=0)
    (h₅ : (wa-wb)*a^5+(wd-we)*b^5+wf*c^5=0) : wf=0 := by
  have hh : wf*c*(c^2-a^2)*(c^2-b^2)=0 := by
    linear_combination h₅-(a^2+b^2)*h₃+a^2*b^2*h₁
  exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right
    (sub_ne_zero.mpr hb))).resolve_right (sub_ne_zero.mpr ha))).resolve_right hc

end field

def momDen (R U : ℚ) : ℚ := 1/5-(R+U)/3+R*U
def momNum (R U : ℚ) : ℚ := 1/7-(R+U)/5+R*U/3
def residue (U D : ℚ) : ℚ := 1/5-(U+D)/3+U*D
def shifted (U : ℚ) : ℚ := 35*U^2-30*U+3
def Mhat (r q : ℚ) : ℚ := (q+1)^2-4*(q+1)*(r+1)+2*(r+1)^2

def terminalCubic (r q : ℚ) : ℚ :=
  35*q^3*r^3+70*q^3*r^2+35*q^3*r+
  70*q^2*r^4+70*q^2*r^3+5*q^2*r^2+3*q^2-
  70*q*r^5+95*q*r^3-39*q*r-6*q-3*r^2-6*r-3

theorem terminal_factor (r q : ℚ) :
    Mhat r q*q*shifted (r^2)+(r+1)^2*r*shifted (q^2) =
      (q-r)*terminalCubic r q := by
  simp only [Mhat,shifted,terminalCubic]
  ring

theorem moment_residue {R U D : ℚ}
    (paid : momNum R U-momDen R U*D=0) :
    momDen R U*residue U D=(-4/1575)*shifted U := by
  simp only [momDen,momNum,residue,shifted] at paid ⊢
  linear_combination -(U-1/3)*paid

/-- Rational clock-radius ingress, with no division by a moment pivot. -/
theorem terminal_cubic_zero {r q D : ℚ} (distinct : q≠r)
    (paid : momNum (r^2) (q^2)-momDen (r^2) (q^2)*D=0)
    (reverse : Mhat r q*q*residue (r^2) D+
      (r+1)^2*r*residue (q^2) D=0) :
    terminalCubic r q=0 := by
  have pd : momDen (q^2) (r^2)=momDen (r^2) (q^2) := by unfold momDen; ring
  have pn : momNum (q^2) (r^2)=momNum (r^2) (q^2) := by unfold momNum; ring
  have p' : momNum (q^2) (r^2)-momDen (q^2) (r^2)*D=0 := by rw [pd,pn]; exact paid
  have kr := moment_residue p'
  rw [pd] at kr
  have kq := moment_residue paid
  have e : (-4/1575:ℚ)*(Mhat r q*q*shifted (r^2)+(r+1)^2*r*shifted (q^2))=0 := by
    linear_combination momDen (r^2) (q^2)*reverse-Mhat r q*q*kr-(r+1)^2*r*kq
  rw [terminal_factor] at e
  exact (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by norm_num))).resolve_left
    (sub_ne_zero.mpr distinct)

private theorem rat_square_three_impossible (x : ℚ) (h : x^2=3) : False := by
  have nat_no : ¬ IsSquare (3:ℕ) := by
    rintro ⟨m,e⟩
    by_cases b : 2≤m
    · have g : 4≤m*m := Nat.mul_le_mul b b
      omega
    · have q : m=0 ∨ m=1 := by omega
      rcases q with rfl | rfl <;> norm_num at e
  exact ((Rat.isSquare_natCast_iff (n:=3)).not.mpr nat_no)
    ⟨x,by linear_combination -h⟩

private theorem rat_square_thirty_impossible (x : ℚ) (h : x^2=30) : False := by
  have nat_no : ¬ IsSquare (30:ℕ) := by
    rintro ⟨m,e⟩
    by_cases b : 6≤m
    · have g : 36≤m*m := Nat.mul_le_mul b b
      omega
    · have q : m≤5 := by omega
      have g : m*m≤25 := Nat.mul_le_mul q q
      omega
  exact ((Rat.isSquare_natCast_iff (n:=30)).not.mpr nat_no)
    ⟨x,by linear_combination -h⟩

/-- The last two chronological clocks cannot be opposite members of
one symmetric pair when their masses are nonzero. -/
theorem reverse_pair_impossible {u : ℚ} (h : u^2-4*u+2=1) : False := by
  apply rat_square_three_impossible (u-2)
  linear_combination h

/-- No rational pivot is lost when degree-six exactness solves one
squared radius from the other two. -/
theorem moment_pivot {R U D : ℚ} (paid : momNum R U-momDen R U*D=0) :
    momDen R U≠0 := by
  intro e
  rw [e,zero_mul,sub_zero] at paid
  simp only [momDen,momNum] at paid e
  have s : R+U=6/7 := by linear_combination (-45/4:ℚ)*paid+(15/4:ℚ)*e
  have p : R*U=3/35 := by linear_combination (-15/4:ℚ)*paid+(9/4:ℚ)*e
  apply rat_square_thirty_impossible ((35/4)*(R-U))
  linear_combination (1225/16:ℚ)*((R+U+6/7)*s-4*p)

def starQ (a : ℚ) : ℚ := -a^2+4*a-2
def starJ (a : ℚ) : ℚ := -a^3/3+2*a^2-2*a

theorem star_head_values (t : ℚ) :
    starQ 1=1 ∧ starQ (1+t)=1+2*t-t^2 ∧ starQ (3-t)=1+2*t-t^2 := by
  simp only [starQ]
  refine ⟨?_,?_,?_⟩ <;> ring

private def lagHom {R : Type*} [CommRing R] (a b : R) : R :=
  a^3-9*a^2*b+18*a*b^2-6*b^3

set_option maxRecDepth 8192 in
private theorem lag_mod : ∀ a b : Fin 5,
    lagHom (a.val : ZMod 5) (b.val : ZMod 5)=0 →
      (a.val : ZMod 5)=0 ∧ (b.val : ZMod 5)=0 := by decide +kernel

/-- The reflected/star rank-two head's first pure chronological
read is impossible over the rationals. -/
theorem no_star_opening {x : ℚ} (h : starQ x=starJ x) : False := by
  have e : lagHom x (1:ℚ)=0 := by
    simp only [starQ,starJ,lagHom] at h ⊢
    linear_combination 3*h
  have hd : (x.den : ℚ)≠0 := by exact_mod_cast x.den_nz
  have scale : x*(x.den : ℚ)=(x.num : ℚ) := by
    nth_rw 1 [←x.num_div_den]
    exact div_mul_cancel₀ _ hd
  have hx : lagHom (x.num : ℚ) (x.den : ℚ)=(x.den : ℚ)^3*lagHom x 1 := by
    rw [←scale]
    simp only [lagHom]
    ring
  rw [e,mul_zero] at hx
  have hz : lagHom x.num (x.den : ℤ)=0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [lagHom,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      Int.cast_natCast,Int.cast_zero] using hx
  have hp := congrArg (Int.castRingHom (ZMod 5)) hz
  have h₅ : lagHom (x.num : ZMod 5) (x.den : ZMod 5)=0 := by
    simp only [lagHom,map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero,map_natCast] at hp
    simpa only [lagHom,Int.coe_castRingHom] using hp
  let a : ZMod 5 := x.num
  let b : ZMod 5 := x.den
  have hv : lagHom (a.val : ZMod 5) (b.val : ZMod 5)=0 := by
    simpa only [ZMod.natCast_zmod_val] using h₅
  obtain ⟨ha,hb⟩ := lag_mod ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ hv
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

end RKResearch.Certified.SDIRKSevenPairedClean
