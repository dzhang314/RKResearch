module

public import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Rational infeasibility of the reduced nonsymmetric eleven-stage
four-tap chart. The hypotheses are the scalar necessary moment equations;
the reduction from the chronological tableau is given separately.
This is not a general rational ERK lower bound. -/

namespace RKResearch.Certified.ERK8ElevenFourTapRational

private theorem noSq (n : ℕ) (hn : ¬ ∃ t : Nat, t*t=n) (z : ℚ)
    (hz : z*z=(n:ℚ)) : False := by
  have isq : IsSquare (n : ℚ) := ⟨z,hz.symm⟩
  obtain ⟨t,ht⟩ := Rat.isSquare_natCast_iff.mp isq
  exact hn ⟨t,ht.symm⟩

private theorem noSq2 (z : ℚ) (hz : z*z=2) : False :=
  noSq 2 (Nat.not_exists_sq (m:=1) (by decide) (by decide)) z hz
private theorem noSq7 (z : ℚ) (hz : z*z=7) : False :=
  noSq 7 (Nat.not_exists_sq (m:=2) (by decide) (by decide)) z hz
private theorem noSq21 (z : ℚ) (hz : z*z=21) : False :=
  noSq 21 (Nat.not_exists_sq (m:=4) (by decide) (by decide)) z hz

/-- Primitive moment of the degree-three polynomial
(x(x-a)(x-h)) against the monomial of degree (k) times (1-x).
Here (s=a+h) and (t=ah). -/
def pm (s t : ℚ) (k : ℕ) : ℚ :=
  1/((k:ℚ)+4)/((k:ℚ)+5) - s/((k:ℚ)+3)/((k:ℚ)+4) +
    t/((k:ℚ)+2)/((k:ℚ)+3)

/-- Moment of ((x-d)x(x-a)(x-h)) against (x^k(1-x)). -/
def vm (s t d : ℚ) (k : ℕ) : ℚ := pm s t (k+1) - d * pm s t k

/-- The polynomial equations are deliberately cleared of rational
denominators. They represent the exact moments on two primitives, the
degree-four nodal polynomial, the order-eight bush constraint, and
the strict last-column constraint, respectively. -/
structure Conditions (a h d e f p q : ℚ) : Prop where
  hasDensity : p ≠ 0 ∨ q ≠ 0
  jp : p*(15-28*(a+h)+63*(a*h)) + q*(21-42*(a+h)+105*(a*h)) = 0
  jxp : p*(9-15*(a+h)+28*(a*h)) + q*(12-21*(a+h)+42*(a*h)) = 0
  nodal : p * vm (a+h) (a*h) d 1 + q * vm (a+h) (a*h) d 0 = 0
  quadrature : vm (a+h) (a*h) d 2 - (e+f)*vm (a+h) (a*h) d 1
    + e*f*vm (a+h) (a*h) d 0 = 0
  last : vm (a+h) (a*h) d 2 - (e+1)*vm (a+h) (a*h) d 1
    + e*vm (a+h) (a*h) d 0 = 0

private def Q (r : ℚ) := 63*r^2-78*r+23
private def K (r : ℚ) := 63*r^3-126*r^2+81*r-16
private def N (r : ℚ) := (3*r-2)*(63*r^2-84*r+25)

private theorem reduced_coordinates {a h r : ℚ}
    (j : 42*(a+h)*r-28*(a+h)-105*(a*h)*r+63*(a*h)-21*r+15=0)
    (k : 21*(a+h)*r-15*(a+h)-42*(a*h)*r+28*(a*h)-12*r+9=0) :
    Q r*(a+h)=3*(2*r-1)*(9*r-7) ∧
    7*Q r*(a*h)=3*(21*r^2-28*r+9) := by
  constructor
  · unfold Q
    linear_combination (4-6*r)*j + (15*r-9)*k
  · unfold Q
    linear_combination (15-21*r)*j + (42*r-28)*k

private theorem q_ne_zero (r : ℚ) : Q r ≠ 0 := by
  intro hz
  unfold Q at hz
  apply noSq2 ((21*r-13)/2)
  linear_combination (7/4:ℚ)*hz

private theorem vm0_eq {s t d r : ℚ}
    (hs : Q r*s=3*(2*r-1)*(9*r-7))
    (ht : 7*Q r*t=3*(21*r^2-28*r+9)) :
    420*Q r*vm s t d 0 =
       (63*r^2-63*r+16) - d*9*(7*r^2-7*r+2) := by
  norm_num [vm,pm]
  unfold Q at *
  linear_combination (35*d-21)*hs + (5-10*d)*ht

private theorem vm1_eq {s t d r : ℚ}
    (hs : Q r*s=3*(2*r-1)*(9*r-7))
    (ht : 7*Q r*t=3*(21*r^2-28*r+9)) :
    420*Q r*vm s t d 1 =
       (63*r^2-66*r+17) - d*(63*r^2-63*r+16) := by
  norm_num [vm,pm]
  unfold Q at *
  linear_combination (21*d-14)*hs + (3-5*d)*ht

private theorem vm2_eq {s t d r : ℚ}
    (hs : Q r*s=3*(2*r-1)*(9*r-7))
    (ht : 7*Q r*t=3*(21*r^2-28*r+9)) :
    840*Q r*vm s t d 2 =
       (117*r^2-126*r+33) - 2*d*(63*r^2-66*r+17) := by
  norm_num [vm,pm]
  unfold Q at *
  linear_combination (28*d-20)*hs + (4-6*d)*ht

private theorem clear_vm {s t d r : ℚ}
    (hs : Q r*s=3*(2*r-1)*(9*r-7))
    (ht : 7*Q r*t=3*(21*r^2-28*r+9))
    (hv : vm s t d 1 = r*vm s t d 0) :
    K r*d = K r + r-1 ∧
      420*Q r*K r*vm s t d 0= -N r ∧
      840*Q r*K r*vm s t d 2= -(3*r^2-2*r+1)*N r := by
  have h0 := vm0_eq (d:=d) hs ht
  have h1 := vm1_eq (d:=d) hs ht
  have h2 := vm2_eq (d:=d) hs ht
  have hd : K r*d=K r+r-1 := by
    rw [hv] at h1
    unfold K
    linear_combination r*h0 - h1
  refine ⟨hd, ?_, ?_⟩
  · unfold N K at *
    linear_combination (63*r^3-126*r^2+81*r-16)*h0 - 9*(7*r^2-7*r+2)*hd
  · unfold N K at *
    linear_combination (63*r^3-126*r^2+81*r-16)*h2 - 2*(63*r^2-66*r+17)*hd

theorem no_eleven_four_tap_chart (a h d e f p q : ℚ)
    (he : e ≠ 1) (hf : f ≠ 1) (H : Conditions a h d e f p q) : False := by
  have hJ := H.jp
  have hK := H.jxp
  by_cases hp : p = 0
  · have hq : q ≠ 0 := H.hasDensity.resolve_left (fun h => h hp)
    simp only [hp,zero_mul,zero_add,mul_eq_zero,hq,false_or] at hJ hK
    have hs : a+h=6/7 := by linear_combination (2/21:ℚ)*hJ - (5/21:ℚ)*hK
    have ht : a*h=1/7 := by linear_combination (1/21:ℚ)*hJ - (2/21:ℚ)*hK
    apply noSq2 (7*(a-h)/2)
    linear_combination (49/4:ℚ)*(a+h+6/7)*hs - 49*ht
  let r := -q/p
  have hq : q = -r*p := by
    dsimp [r]
    field_simp [hp]
  rw [hq] at hJ hK
  have j : 42*(a+h)*r-28*(a+h)-105*(a*h)*r+63*(a*h)-21*r+15=0 := by
    apply (mul_eq_zero.mp (show p * _ = 0 from ?_)).resolve_left hp
    linear_combination hJ
  have k : 21*(a+h)*r-15*(a+h)-42*(a*h)*r+28*(a*h)-12*r+9=0 := by
    apply (mul_eq_zero.mp (show p * _ = 0 from ?_)).resolve_left hp
    linear_combination hK
  obtain ⟨hs,ht⟩ := reduced_coordinates j k
  let I (k : ℕ) := vm (a+h) (a*h) d k
  have Hnod : p*I 1 + q*I 0 = 0 := H.nodal
  have H1 : I 1 = r*I 0 := by
    rw [hq] at Hnod
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show p*(I 1-r*I 0)=0 from ?_)).resolve_left hp
    linear_combination Hnod
  obtain ⟨hKd,h0,h2⟩ := clear_vm hs ht H1
  change 420*Q r*K r*I 0= -N r at h0
  change 840*Q r*K r*I 2= -(3*r^2-2*r+1)*N r at h2
  have hKn : K r ≠ 0 := by
    intro hz
    have hr : r=1 := by rw [hz] at hKd; linarith
    norm_num [K,hr] at hz
  have hI0 : I 0 ≠ 0 := by
    intro hi
    have hn : N r=0 := by rw [hi] at h0; linarith
    rcases mul_eq_zero.mp hn with hr | hr
    · have rr : r=2/3 := by linarith
      rw [rr] at hs ht
      norm_num [Q] at hs ht
      apply noSq21 (7*(a-h))
      linear_combination (-49:ℚ)*(a+h+1)*hs - (28:ℚ)*ht
    · apply noSq21 (21*r-14)
      linear_combination 7*hr
  have Hz : 2*I 2 = (3*r^2-2*r+1)*I 0 := by
    apply sub_eq_zero.mp
    have hm : (420*Q r*K r) * (2*I 2-(3*r^2-2*r+1)*I 0)=0 := by
      linear_combination h2 - (3*r^2-2*r+1)*h0
    have hnon : 420*Q r*K r ≠ 0 := mul_ne_zero (mul_ne_zero (by decide) (q_ne_zero r)) hKn
    exact (mul_eq_zero.mp hm).resolve_left hnon
  have HB : I 2-(e+f)*I 1+e*f*I 0=0 := H.quadrature
  have HD : I 2-(e+1)*I 1+e*I 0=0 := H.last
  have hfn : f-1 ≠ 0 := sub_ne_zero.mpr hf
  have hre : r=e := by
    apply sub_eq_zero.mp
    have hr : ((f-1)*(r-e))*I 0 = 0 := by
      rw [H1] at HB HD
      linear_combination HD - HB
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hI0)).resolve_left hfn
  have hR : (r-1)^2=0 := by
    apply (mul_eq_zero.mp (show ((r-1)^2) * I 0=0 from ?_)).resolve_right hI0
    rw [←hre,H1] at HD
    linear_combination 2*HD - Hz
  have hm : (r-1)*(r-1)=0 := by simpa only [pow_two] using hR
  have hh : r=1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).elim id id)
  exact he (hre ▸ hh)

end RKResearch.Certified.ERK8ElevenFourTapRational

#print axioms RKResearch.Certified.ERK8ElevenFourTapRational.no_eleven_four_tap_chart
