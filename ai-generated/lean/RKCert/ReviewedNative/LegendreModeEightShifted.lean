module

public import RKCert.ReviewedNative.LegendreModeEight
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.LegendreModeEight

open Polynomial RKCert.ReviewedNative.LegendreEnergy
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def halfShift (K : Type*) [Field K] : K[X] :=
  C ((2:K)⁻¹)*(X+1)

def centered (L : K[X]) : K[X] := L.comp (halfShift K)

private theorem halfShift_eval (x : K) : (halfShift K).eval x=(x+1)/2 := by
  simp [halfShift,div_eq_mul_inv] <;> ring

private theorem halfShift_prime : (halfShift K).derivative=C ((2:K)⁻¹) := by
  simp [halfShift,derivative_mul,derivative_add]

theorem centered_degree {L : K[X]} (d : L.natDegree≤8) :
    (centered L).natDegree≤8 := by
  have s : (halfShift K).natDegree≤1 :=
    (natDegree_C_mul_le _ _).trans
      (natDegree_add_le_of_degree_le natDegree_X.le (by simp))
  exact natDegree_comp_le.trans (by simpa only [mul_one] using Nat.mul_le_mul d s)

theorem centered_at_one {L : K[X]} (at1 : L.eval 1=1) :
    (centered L).eval 1=1 := by
  have e : (halfShift K).eval 1=1 := by rw [halfShift_eval];norm_num
  rw [centered,eval_comp,e,at1]

theorem centered_value {L : K[X]} (r : K) :
    (centered L).eval (2*r-1)=L.eval r := by
  have e : (halfShift K).eval (2*r-1)=r := by rw [halfShift_eval];ring
  rw [centered,eval_comp,e]

theorem centered_critical {L : K[X]} {r : K} (h : L.derivative.eval r=0) :
    (centered L).derivative.eval (2*r-1)=0 := by
  have e : (halfShift K).eval (2*r-1)=r := by rw [halfShift_eval];ring
  rw [centered,derivative_comp,halfShift_prime,eval_mul,eval_comp,e,h,mul_zero]

/-- Exact transport of the shifted bubble ODE; the factor four in
1−x² cancels the two derivative factors of one half. -/
theorem centered_isMode {L : K[X]}
    (ode : ((X*(1-X))*L.derivative).derivative+C (72:K)*L=0) :
    IsMode (72:K) (centered L) := by
  letI : Infinite K := Infinite.of_injective (Nat.cast : ℕ→K) Nat.cast_injective
  let G : K[X] := (X*(1-X))*L.derivative
  have transport : (cap K)*(centered L).derivative=(2:K[X])*G.comp (halfShift K) := by
    apply Polynomial.funext
    intro x
    simp only [centered,derivative_comp,halfShift_prime,cap,G,mul_comp,sub_comp,
      X_comp,one_comp,eval_mul,eval_sub,eval_pow,eval_one,eval_X,
      eval_C,eval_ofNat,eval_comp,halfShift_eval]
    ring
  have two : (2:K[X])=C (2:K) := by norm_num [map_ofNat]
  have inv : (2:K[X])*C ((2:K)⁻¹)=1 := by
    rw [two,←map_mul,mul_inv_cancel₀ (by norm_num : (2:K)≠0),map_one]
  have back : ((cap K)*(centered L).derivative).derivative=G.derivative.comp (halfShift K) := by
    rw [transport,derivative_mul,derivative_ofNat,zero_mul,zero_add,
      derivative_comp,halfShift_prime,←mul_assoc,inv,one_mul]
  change ((cap K)*(centered L).derivative).derivative+C (72:K)*centered L=0
  rw [back,centered]
  simpa only [G,add_comp,mul_comp,C_comp,zero_comp] using
    congrArg (fun W : K[X] => W.comp (halfShift K)) ode

/-- Exact ordered-field scalar consumer after the five-coordinate
diagonal quadratic is normalized by its common endpoint value. -/
theorem not_shifted_three_critical_common_factor {L : K[X]} (d : L.natDegree≤8)
    (ode : ((X*(1-X))*L.derivative).derivative+C (72:K)*L=0)
    (at1 : L.eval 1=1) (r : Fin 3→K) (simple : Function.Injective r)
    (inside : ∀ i, 0<r i ∧ r i<1) (critical : ∀ i, L.derivative.eval (r i)=0)
    (g : K) (paid : ∀ i, 1=L.eval (r i)^2*(1+g*r i*(1-r i))) : False := by
  let x (i : Fin 3) := 2*r i-1
  apply not_three_critical_common_factor (centered_degree d) (centered_isMode ode)
    (centered_at_one at1) x ?_ ?_ ?_ (g/4) ?_
  · intro i j e
    apply simple
    change 2*r i-1=2*r j-1 at e
    linarith only [e]
  · intro i
    apply abs_lt.mpr
    obtain ⟨h₀,h₁⟩ := inside i
    change -1<2*r i-1 ∧ 2*r i-1<1
    exact ⟨by linarith only [h₀],by linarith only [h₁]⟩
  · exact fun i => centered_critical (critical i)
  · intro i
    change 1=(centered L).eval (2*r i-1)^2*(1+(g/4)*(1-(2*r i-1)^2))
    rw [centered_value]
    have e : (g/4)*(1-(2*r i-1)^2)=g*r i*(1-r i) := by ring
    rw [e]
    exact paid i

end
end RKCert.ReviewedNative.LegendreModeEight
