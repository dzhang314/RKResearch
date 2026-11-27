module

public import RKCert.ReviewedNative.ERK149TwoPairAnchored

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149AnchoredChronologyCensus

variable {K : Type*} [Field K] [CharZero K]

theorem one_site_impossible (a t m : K) (ht : t ≠ 0)
    (h₁ : m*a = t^2/2) (h₂ : m*a^2 = t^3/3) (h₃ : m*a^3 = t^4/4) :
    False := by
  have h : (m*a^2)^2 = (m*a)*(m*a^3) := by ring
  rw [h₂,h₁,h₃] at h
  exact pow_ne_zero 6 ht (by linear_combination -72*h)

theorem three_first_sites_resonance
    (c a b t k v m : K) (ha : a ≠ 0) (hc : c ≠ 0)
    (hac : a ≠ c) (ht : t ≠ 0)
    (hy : (a-c)*a*v = (t-2*c)*t^3/12)
    (hh : v*k*c = t^4/24)
    (hmark : (a-b)*m*k*c = t^3*(3*t-4*b)/24)
    (hm : (a-c)*a*(a-b)*m = t^4/4-(b+c)*t^3/3+b*c*t^2/2) :
    t = b := by
  have hP := mul_ne_zero (sub_ne_zero.mpr hac) ha
  have hkc₀ : t^3*((t-2*c)*(k*c)-(a-c)*a*t/2)=0 := by
    linear_combination -12*(k*c)*hy+12*((a-c)*a)*hh
  have hkc : (t-2*c)*(k*c)=(a-c)*a*t/2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hkc₀).resolve_left (pow_ne_zero 3 ht))
  have hmq :
      (t^4/4-(b+c)*t^3/3+b*c*t^2/2)*(k*c) = (a-c)*a*t^3*(3*t-4*b)/24 := by
    linear_combination ((a-c)*a)*hmark-(k*c)*hm
  have hz : ((a-c)*a)*t^3*c*(t-b)=0 := by
    linear_combination 12*(t-2*c)*hmq-12*(t^4/4-(b+c)*t^3/3+b*c*t^2/2)*hkc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero hP (pow_ne_zero 3 ht)) hc))

def card (t x v w : K) : K :=
  (t^4/4-(v+w)*t^3/3+v*w*t^2/2)/(x*(x-v)*(x-w))

theorem second_site_minor (c a b z : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    card z c a b * card b a b c - card z a b c * card b c a b =
      -b^3*z^2*(z-b)^2/(24*a*c*(a-b)*(a-c)*(b-c)) := by
  have hca := hac.symm
  have hcb := hbc.symm
  unfold card
  field_simp [ha,hb,hc,sub_ne_zero.mpr hab,sub_ne_zero.mpr hac,
           sub_ne_zero.mpr hbc,sub_ne_zero.mpr hca,sub_ne_zero.mpr hcb]
  ring

omit [CharZero K] in
private theorem two_donor_eliminate (a b t d : K)
    (hK : 6*a*b-4*(a+b)*t+3*t^2=0) (hd : d*t=3*a*b) :
    6*a*b*d^2-12*a*b*(a+b)*d+27*a^2*b^2=0 := by
  have hs : (d*t)^2=(3*a*b)^2 := congrArg (fun x : K => x^2) hd
  linear_combination d^2*hK+4*(a+b)*d*hd-3*hs

theorem anchor_anchor_other (a b t : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hK : 6*a*b-4*(a+b)*t+3*t^2=0)
    (hG : 3*a*b+a*t-2*b*t=0) : b=2*a ∧ t=b := by
  have hd : (2*b-a)*t=3*a*b := by linear_combination -hG
  have h0 := two_donor_eliminate a b t (2*b-a) hK hd
  have h1 : 9*a^2*b*(2*a-b)=0 := by linear_combination h0
  have he : b=2*a := (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) hb))).symm
  refine ⟨he, ?_⟩
  rw [he] at hK ⊢
  by_contra hn
  exact pow_ne_zero 2 (sub_ne_zero.mpr hn) (by linear_combination hK/3)

theorem anchor_other_anchor (a b t : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hK : 6*a*b-4*(a+b)*t+3*t^2=0)
    (hG : -3*a*b+2*a*t-b*t=0) : a=2*b ∧ t=a := by
  have hd : (2*a-b)*t=3*a*b := by linear_combination hG
  have h0 := two_donor_eliminate a b t (2*a-b) hK hd
  have h1 : 9*a*b^2*(a-2*b)=0 := by linear_combination -h0
  have he : a=2*b := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 2 hb)))
  refine ⟨he, ?_⟩
  rw [he] at hK ⊢
  by_contra hn
  exact pow_ne_zero 2 (sub_ne_zero.mpr hn) (by linear_combination hK/3)

end RKResearch.Certified.ERK149AnchoredChronologyCensus
