module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar gates for the arithmetic-suffix dirty SDIRK7 chart

These are scalar theorems.  The ingress from stage columns, and the
rooted-tree assembly from the reduced clock core, are separate. -/

namespace RKResearch.Certified.SDIRKSevenDirtyArithmeticAtlas

private def obstructionHom {R : Type*} [CommRing R] (a b : R) : R :=
  63*a^4+405*a^3*b+1119*a^2*b^2+903*a*b^3+70*b^4

private def obstruction (k : ℚ) : ℚ := 63*k^4+405*k^3+1119*k^2+903*k+70

set_option maxRecDepth 8192 in
private theorem finite_projective : ∀ a b : Fin 11,
    obstructionHom (a.val : ZMod 11) (b.val : ZMod 11) = 0 →
      (a.val : ZMod 11) = 0 ∧ (b.val : ZMod 11) = 0 := by
  decide +kernel

private theorem obstruction_ne (k : ℚ) : obstruction k ≠ 0 := by
  intro hk
  have hd : (k.den : ℚ) ≠ 0 := by exact_mod_cast k.den_nz
  have hscale : k * (k.den : ℚ) = (k.num : ℚ) := by
    nth_rw 1 [←k.num_div_den]
    exact div_mul_cancel₀ _ hd
  have hq : obstructionHom (k.num : ℚ) (k.den : ℚ) = (k.den : ℚ)^4*obstruction k := by
    rw [←hscale]
    simp only [obstructionHom,obstruction]
    ring
  rw [hk,mul_zero] at hq
  have hZ : obstructionHom k.num (k.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [obstructionHom, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 11)) hZ
  have hp' : obstructionHom (k.num : ZMod 11) (k.den : ZMod 11) = 0 := by
    simp only [obstructionHom, map_add, map_mul, map_pow, map_ofNat, map_zero,
      map_natCast] at hp
    simpa only [obstructionHom, Int.coe_castRingHom] using hp
  let a : ZMod 11 := k.num
  let b : ZMod 11 := k.den
  have hv : obstructionHom (a.val : ZMod 11) (b.val : ZMod 11) = 0 := by
    simpa only [ZMod.natCast_zmod_val] using hp'
  obtain ⟨ha,hb⟩ := finite_projective ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ hv
  have han : (11:ℕ) ∣ k.num.natAbs := by
    have ha' : (k.num : ZMod 11) = 0 := by
      simpa only [ZMod.natCast_zmod_val,a] using ha
    simpa using (Int.natAbs_dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd k.num 11).mp ha'))
  have hbn : (11:ℕ) ∣ k.den := by
    have hb' : (k.den : ZMod 11) = 0 := by
      simpa only [ZMod.natCast_zmod_val,b] using hb
    exact (ZMod.natCast_eq_zero_iff k.den 11).mp hb'
  have impossible := Nat.dvd_gcd han hbn
  rw [k.reduced.gcd_eq_one] at impossible
  exact (by decide : ¬ (11:ℕ) ∣ 1) impossible

/-- The coefficients of the centered monic quartic
    (X-r)(X-p)((X-p)^2-d^2), in descending order after its leading one. -/
def coeff₃ (p r : ℚ) : ℚ := -(3*p+r)
def coeff₂ (p d r : ℚ) : ℚ := 3*p^2-d^2+3*p*r
def coeff₁ (p d r : ℚ) : ℚ := -p^3+p*d^2-r*(3*p^2-d^2)
def coeff₀ (p d r : ℚ) : ℚ := r*(p^3-p*d^2)

def moment₀ (p d r : ℚ) : ℚ := 1/5+coeff₂ p d r/3+coeff₀ p d r
def moment₁ (p d r : ℚ) : ℚ := coeff₃ p r/5+coeff₁ p d r/3
def moment₂ (p d r : ℚ) : ℚ := 1/7+coeff₂ p d r/5+coeff₀ p d r/3

/-- No rational quartic with an arithmetic triple of roots can annihilate
all first three centered uniform moments.  In particular, a paid
quadrature cannot have both of its coefficient-solving pivots zero. -/
theorem centered_moments_not_all_zero {p d r : ℚ}
    (m₀ : moment₀ p d r=0) (m₁ : moment₁ p d r=0)
    (m₂ : moment₂ p d r=0) : False := by
  simp only [moment₀,moment₁,moment₂] at m₀ m₁ m₂
  have e₂ : coeff₂ p d r = -6/7 := by
    linear_combination (45/4:ℚ)*m₂-(15/4:ℚ)*m₀
  have e₀ : coeff₀ p d r=3/35 := by
    linear_combination (9/4:ℚ)*m₀-(15/4:ℚ)*m₂
  have ed : d^2=3*p^2+3*p*r+6/7 := by
    unfold coeff₂ at e₂
    linear_combination -e₂
  have ep : p≠0 := by
    intro hp
    simp [coeff₀,hp] at e₀
    norm_num at e₀
  have e₁ : p*(2*p^2+3*p*r+3*r^2)=(33*p-9*r)/35 := by
    simp only [coeff₃,coeff₁] at m₁
    linear_combination 3*m₁-(p+r)*ed
  have ec : -p*r*(2*p^2+3*p*r+6/7)=3/35 := by
    unfold coeff₀ at e₀
    linear_combination e₀+p*r*ed
  let k := r/p
  have hr : r=p*k := by dsimp only [k]; rw [mul_comm p,div_mul_cancel₀ _ ep]
  rw [hr] at e₁ ec
  let D : ℚ := 3*k^2+3*k+2
  let α : ℚ := (33-9*k)/35
  have hpD : p*(p^2*D-α)=0 := by
    dsimp [D,α]
    linear_combination e₁
  have hL : p^2*D=α := sub_eq_zero.mp ((mul_eq_zero.mp hpD).resolve_left ep)
  have hC : -35*k*(2+3*k)*p^4-30*k*p^2-3=0 := by
    linear_combination 35*ec
  apply obstruction_ne k
  dsimp [obstruction,D,α] at hL ⊢
  linear_combination (-35/6 : ℚ)*((3*k^2+3*k+2)^2*hC+
    (35*k*(2+3*k)*(p^2*(3*k^2+3*k+2)+(33-9*k)/35)
      +30*k*(3*k^2+3*k+2))*hL)

def rawMoment (z u c : ℚ) (k : ℕ) : ℚ :=
  z^(k+4)/((k:ℚ)+5)+coeff₃ u c*z^(k+3)/((k:ℚ)+4)+
    coeff₂ u (u-1) c*z^(k+2)/((k:ℚ)+3)+coeff₁ u (u-1) c*z^(k+1)/((k:ℚ)+2)+
    coeff₀ u (u-1) c*z^k/((k:ℚ)+1)

/-- Actual shift and rescaling of the first three moments for
  R₄=(X-c)(X-1)(X-u)(X-(2u-1)). -/
theorem center_raw_moments {z u c : ℚ} (hz : z≠0) :
    let p := 2*u/z-1
    let d := 2*(u-1)/z
    let r := 2*c/z-1
    moment₀ p d r=16/z^4*rawMoment z u c 0 ∧
    moment₁ p d r=16/z^4*(2/z*rawMoment z u c 1-rawMoment z u c 0) ∧
    moment₂ p d r=16/z^4*(4/z^2*rawMoment z u c 2-4/z*rawMoment z u c 1+
      rawMoment z u c 0) := by
  dsimp only
  refine ⟨?_,?_,?_⟩ <;>
    norm_num [rawMoment,moment₀,moment₁,moment₂,coeff₀,coeff₁,coeff₂,coeff₃] <;>
    field_simp [hz] <;> ring

/-- For Q₂=X²-sX+p, the paid uniform moment of R₄Q₂ recovers
one of its two coefficients with a genuinely nonzero pivot. -/
theorem quadrature_pivot {z u c s p : ℚ} (hz : z≠0)
    (eq : rawMoment z u c 2-s*rawMoment z u c 1+p*rawMoment z u c 0=0) :
    (rawMoment z u c 0≠0 ∧ p=(s*rawMoment z u c 1-rawMoment z u c 2)/
      rawMoment z u c 0) ∨
    (rawMoment z u c 0=0 ∧ rawMoment z u c 1≠0 ∧ s=rawMoment z u c 2/
      rawMoment z u c 1) := by
  by_cases h₀ : rawMoment z u c 0=0
  · have h₁ : rawMoment z u c 1≠0 := by
      intro h₁
      have h₂ : rawMoment z u c 2=0 := by simpa [h₀,h₁] using eq
      obtain ⟨e₀,e₁,e₂⟩ := center_raw_moments (u:=u) (c:=c) hz
      rw [h₀,mul_zero] at e₀
      rw [h₀,h₁,mul_zero,sub_zero,mul_zero] at e₁
      rw [h₀,h₁,h₂,mul_zero,mul_zero,sub_zero,add_zero,mul_zero] at e₂
      exact centered_moments_not_all_zero e₀ e₁ e₂
    refine Or.inr ⟨h₀,h₁,(eq_div_iff h₁).mpr ?_⟩
    rw [h₀,mul_zero,add_zero] at eq
    linear_combination -eq
  · refine Or.inl ⟨h₀,(eq_div_iff h₀).mpr ?_⟩
    linear_combination eq

section field

variable {K : Type*} [Field K]

def ghostDen (L₁ Lᵤ Lᵥ : K) : K := L₁-2*Lᵤ+Lᵥ
def ghostNum (u L₁ Lᵤ Lᵥ : K) : K := L₁-2*u*Lᵤ+(2*u-1)*Lᵥ

/-- Three arithmetic sites of a genuine affine-over-linear graph
determine its non-removable pole by one division. -/
theorem ghost_pivot {u h m n L₁ Lᵤ Lᵥ : K} (hu : u≠1)
    (h₂ : (2:K)≠0) (hW : m*h+n≠0)
    (e₁ : m+n=(1-h)*L₁)
    (eᵤ : m*u+n=(u-h)*Lᵤ)
    (eᵥ : m*(2*u-1)+n=(2*u-1-h)*Lᵥ) :
    ghostDen L₁ Lᵤ Lᵥ≠0 ∧ h=ghostNum u L₁ Lᵤ Lᵥ/ghostDen L₁ Lᵤ Lᵥ := by
  have e : ghostNum u L₁ Lᵤ Lᵥ=h*ghostDen L₁ Lᵤ Lᵥ := by
    unfold ghostNum ghostDen
    linear_combination -e₁+2*eᵤ-eᵥ
  have hden : ghostDen L₁ Lᵤ Lᵥ≠0 := by
    intro z
    have ee : (u-1)*(Lᵥ-L₁)=0 := by
      simp only [ghostDen,ghostNum] at e z
      linear_combination e+(h-u)*z
    have hh := sub_eq_zero.mp ((mul_eq_zero.mp ee).resolve_left (sub_ne_zero.mpr hu))
    have hx2 : 2*(L₁-Lᵤ)=0 := by
      unfold ghostDen at z
      rw [hh] at z
      linear_combination z
    have hh2 := sub_eq_zero.mp ((mul_eq_zero.mp hx2).resolve_left h₂)
    rw [hh2] at e₁
    have hz : (u-1)*(m*h+n)=0 := by
      linear_combination (u-h)*e₁+(h-1)*eᵤ
    exact (mul_ne_zero (sub_ne_zero.mpr hu) hW) hz
  exact ⟨hden, (eq_div_iff hden).mpr e.symm⟩

def fourthDen (u c L₁ Lᵤ Lc : K) : K := (u-1)*Lc-(u-c)*L₁-(c-1)*Lᵤ
def fourthNum (u c L₁ Lᵤ Lc : K) : K := (u-1)*c*Lc-(u-c)*L₁-(c-1)*u*Lᵤ

/-- The four-site reverse compatibility is homogeneous quadratic
in the four mass numerators. They are affine in one free quadratic
hull coefficient after solving the uniform moment equation. -/
theorem fourth_cross {u c h m n L₁ Lᵤ Lᵥ Lc : K}
    (e₁ : m+n=(1-h)*L₁)
    (eᵤ : m*u+n=(u-h)*Lᵤ)
    (eᵥ : m*(2*u-1)+n=(2*u-1-h)*Lᵥ)
    (ec : m*c+n=(c-h)*Lc) :
    ghostDen L₁ Lᵤ Lᵥ*fourthNum u c L₁ Lᵤ Lc-
      ghostNum u L₁ Lᵤ Lᵥ*fourthDen u c L₁ Lᵤ Lc=0 := by
  have e : ghostNum u L₁ Lᵤ Lᵥ=h*ghostDen L₁ Lᵤ Lᵥ := by
    unfold ghostNum ghostDen
    linear_combination -e₁+2*eᵤ-eᵥ
  have f : fourthNum u c L₁ Lᵤ Lc=h*fourthDen u c L₁ Lᵤ Lc := by
    unfold fourthNum fourthDen
    linear_combination (u-c)*e₁+(c-1)*eᵤ-(u-1)*ec
  rw [e,f]
  ring

/-- Basis-free cross-ratio test: the pole is not a cancelled zero,
so its affine-over-linear transform is injective off the pole. -/
theorem graph_injective {a b h m n Lₐ Lᵦ : K} (hW : m*h+n≠0)
    (ea : m*a+n=(a-h)*Lₐ) (eb : m*b+n=(b-h)*Lᵦ)
    (he : Lₐ=Lᵦ) : a=b := by
  rw [he] at ea
  have z : (a-b)*(m*h+n)=0 := by linear_combination -(b-h)*ea+(a-h)*eb
  exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_right hW)

end field

section suffix

variable {K : Type*} [Field K]

def M (u : K) : K := u^2-4*u+2
def T (u : K) : K := u^3-7*u^2+10*u-2
def q₀ (u : K) : K := 2*(u-2)*(u-1)^2
def q₁ (u : K) : K := -2*(u-3)*(u-1)*(2*u-3)
def q₂ (u : K) : K := (u-3)*(u-2)^2
def Qhat (u c : K) : K := q₀ u+q₁ u*c+q₂ u*c^2
def Ghat (u c : K) : K :=
  6*q₀ u*(c-1)+3*q₁ u*(c^2-2*c)+2*q₂ u*(c^3-3*c^2)
def Ehat (u c : K) : K :=
  -6*M u*q₁ u+q₂ u*(-8*M u+4*(1-M u)*(c-1))-12*T u*(1-c)

theorem rank_identity (u c : K) :
    2*T u*M u*Ghat u c+Ehat u c*Qhat u c=
      -8*(c-u)*(c-1)*(c-(2*u-1))*(u-3)*(u-2)^2*(u-1)^3 := by
  simp only [M,T,q₀,q₁,q₂,Qhat,Ghat,Ehat]
  ring

/-- On the actual fourth reverse equation, its linear ratio
coefficient cannot vanish when the nodes and clocks are allowed. -/
theorem fourth_ratio {u c r : K} (h₈ : (8:K)≠0)
    (hu₁ : u≠1) (hu₂ : u≠2) (hu₃ : u≠3)
    (hc₁ : c≠1) (hcᵤ : c≠u) (hcᵥ : c≠2*u-1)
    (read : M u*Ghat u c+Ehat u c*r=0) :
    Ehat u c≠0 ∧ r=-M u*Ghat u c/Ehat u c := by
  have hp : -8*(c-u)*(c-1)*(c-(2*u-1))*(u-3)*(u-2)^2*(u-1)^3≠0 := by
    have hn : (-8:K)≠0 := neg_ne_zero.mpr h₈
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero hn (sub_ne_zero.mpr hcᵤ)) (sub_ne_zero.mpr hc₁))
      (sub_ne_zero.mpr hcᵥ)) (sub_ne_zero.mpr hu₃))
      (pow_ne_zero _ (sub_ne_zero.mpr hu₂))) (pow_ne_zero _ (sub_ne_zero.mpr hu₁))
  have hn : Ehat u c≠0 := by
    intro e
    apply hp
    have h := rank_identity u c
    rw [e,zero_mul,add_zero] at h
    rw [e,zero_mul,add_zero] at read
    rw [←h, mul_assoc,read,mul_zero]
  refine ⟨hn,(eq_div_iff hn).mpr ?_⟩
  linear_combination read

end suffix

section helper

variable {K : Type*} [Field K]

/-- On the projective linear-helper branch the tap recovery does not
require the nonzero coefficient used by monic-quadratic recovery. -/
theorem linear_helper_tap {w t : K} (ht : t≠0)
    (h : 1+t-w=(1+2*t-t^2)*(1-w)) :
    w≠1 ∧ t=2+1/(w-1) := by
  have z : t*((t-2)*(w-1)-1)=0 := by
    linear_combination -h
  have e := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left ht)
  have hw : w≠1 := by
    intro hw
    rw [hw,sub_self,mul_zero] at e
    exact zero_ne_one e
  refine ⟨hw,?_⟩
  apply (eq_add_of_sub_eq' _)
  exact (eq_div_iff (sub_ne_zero.mpr hw)).mpr e

end helper

end RKResearch.Certified.SDIRKSevenDirtyArithmeticAtlas
