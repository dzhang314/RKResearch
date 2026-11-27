module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact arithmetical filters for a degree-seven scalar rule whose six
sites include both endpoints. The four variable sites here are centered
in coordinates with endpoints -1 and 1. These are scalar statements,
not proof of nonexistence of a universal tableau. -/
namespace RKResearch.Certified.ERK8CenteredQuadratureConstraints

def centeredPay {K : Type*} [CommRing K] (a b c d : K) : Prop :=
  7*(a*b+a*c+a*d+b*c+b*d+c*d)+35*a*b*c*d+3=0 ∧
  3*(a+b+c+d)+7*(a*b*c+a*b*d+a*c*d+b*c*d)=0

def distinctInterior {K : Type*} [CommRing K] (a b c d : K) : Prop :=
  a≠1 ∧ a≠-1 ∧ b≠1 ∧ b≠-1 ∧ c≠1 ∧ c≠-1 ∧ d≠1 ∧ d≠-1 ∧
    a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d

set_option maxRecDepth 15000
set_option maxHeartbeats 0

theorem centered_sum_zero_mod_eleven : ∀ a b c d : ZMod 11,
    distinctInterior a b c d → centeredPay a b c d → a+b+c+d=0 := by
  unfold distinctInterior centeredPay
  decide +kernel

theorem centered_sum_zero_mod_thirteen : ∀ a b c d : ZMod 13,
    distinctInterior a b c d → centeredPay a b c d → a+b+c+d=0 := by
  unfold distinctInterior centeredPay
  decide +kernel

/-- Inverse-pair reconstruction after separating a regular pair from
two nonzero sites. These denominator-cleared equations do not need any
valuation, so they can also be evaluated modulo powers of a prime. -/
theorem reciprocal_pair_coefficients {a b c d : ℚ} (h : centeredPay a b c d)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    let S := a+b
    let P := a*b
    let C := 3+7*P
    (C^2-21*S^2)*(1/c+1/d)=56*S*P ∧
    (C^2-21*S^2)*(1/c* (1/d))=49*S^2-7*C*(1+5*P) := by
  dsimp only
  have h₁ : 7*(a+b)*(1/c+1/d)+(3+7*(a*b))*(1/c*(1/d)) =
      -7*(1+5*(a*b)) := by
    field_simp [hc,hd]
    linear_combination h.1
  have h₂ : (3+7*(a*b))*(1/c+1/d)+3*(a+b)*(1/c*(1/d)) =
      -7*(a+b) := by
    field_simp [hc,hd]
    linear_combination h.2
  constructor
  · linear_combination (3+7*(a*b))*h₂ - 3*(a+b)*h₁
  · linear_combination (3+7*(a*b))*h₁ - 7*(a+b)*h₂

private abbrev K7 := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem num_nz_of_den_z (x : ℚ) (hd : (x.den : K7) = 0) :
    (x.num : K7) ≠ 0 := by
  intro hz
  have hN : 7 ∣ x.num.natAbs := by
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 7).mp hz
    exact Int.natCast_dvd_natCast.mp ((Int.dvd_natAbs).mpr hv)
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 7) hN
    ((ZMod.natCast_eq_zero_iff _ _).mp hd) x.reduced

private theorem clear_sym {a b : ℚ}
    (h : 7*(a^2+b^2)-35*a^2*b^2=3) :
    7*a.num^2*(b.den : Int)^2+7*b.num^2*(a.den : Int)^2-35*a.num^2*b.num^2 =
      3*(a.den : Int)^2*(b.den : Int)^2 := by
  have an : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have bn : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [←a.num_div_den, ←b.num_div_den] at h
  field_simp [an,bn] at h
  linear_combination h

private theorem sym_bad_den_left {a b : ℚ}
    (h : 7*(a^2+b^2)-35*a^2*b^2=3) (hd : (a.den : K7) = 0) : False := by
  obtain ⟨n,hn⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hd
  have en := clear_sym h
  rw [hn,Nat.cast_mul,Nat.cast_ofNat] at en
  have zero : (7 : Int) *
      (a.num^2*((b.den:Int)^2-5*b.num^2) +
        49*b.num^2*(n:Int)^2 - 21*(n:Int)^2*(b.den:Int)^2)=0 := by
    linear_combination en
  have q := (mul_eq_zero.mp zero).resolve_left (by decide)
  have z := congrArg (fun x : Int => (x : K7)) q
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_zero,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast] at z
  have zz : (a.num : K7)^2*((b.den:K7)^2-5*(b.num:K7)^2)=0 := by
    have e₁ : (49 : K7) = 0 := by decide
    have e₂ : (21 : K7) = 0 := by decide
    simpa only [e₁,e₂,zero_mul,add_zero,sub_zero] using z
  have hh := sub_eq_zero.mp ((mul_eq_zero.mp zz).resolve_left
    (pow_ne_zero _ (num_nz_of_den_z _ hd)))
  have finite : ∀ x y : K7, y^2 = 5*x^2 → x=0 ∧ y=0 := by decide +kernel
  obtain ⟨hz,hden⟩ := finite _ _ hh
  exact num_nz_of_den_z b hden hz

theorem no_symmetric_rational_centered_rule (a b : ℚ) :
    7*(a^2+b^2)-35*a^2*b^2 ≠ 3 := by
  intro h
  by_cases ha : (a.den : K7) = 0
  · exact sym_bad_den_left h ha
  by_cases hb : (b.den : K7) = 0
  · apply sym_bad_den_left (a := b) (b := a) _ hb
    linear_combination h
  have u := congrArg (fun x : Int => (x : K7)) (clear_sym h)
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,
    Int.cast_ofNat,Int.cast_natCast] at u
  have e₁ : (7 : K7) = 0 := by decide
  have e₂ : (35 : K7) = 0 := by decide
  simp only [e₁,e₂,zero_mul,add_zero,sub_zero] at u
  exact mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ ha))
    (pow_ne_zero _ hb) u.symm

end RKResearch.Certified.ERK8CenteredQuadratureConstraints

#print axioms RKResearch.Certified.ERK8CenteredQuadratureConstraints.centered_sum_zero_mod_eleven
#print axioms RKResearch.Certified.ERK8CenteredQuadratureConstraints.centered_sum_zero_mod_thirteen
#print axioms RKResearch.Certified.ERK8CenteredQuadratureConstraints.no_symmetric_rational_centered_rule

#print axioms RKResearch.Certified.ERK8CenteredQuadratureConstraints.reciprocal_pair_coefficients
