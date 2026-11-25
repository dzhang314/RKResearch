module

public import RKCert.ReviewedNative.LegendreEnergyRatio
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.LegendreModeEight

open Polynomial RKCert.ReviewedNative.LegendreEnergy

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def raw (K : Type*) [Field K] : K[X] :=
  6435*X^8-12012*X^6+6930*X^4-1260*X^2+35

def polynomial (K : Type*) [Field K] : K[X] := C ((128:K)⁻¹)*raw K

private theorem raw_prime :
    (raw K).derivative=51480*X^7-72072*X^5+27720*X^3-2520*X := by
  norm_num [raw,derivative_sub,derivative_add,derivative_mul,derivative_X_pow,
    derivative_ofNat,derivative_natCast,map_ofNat] <;> ring

theorem value (x : K) :
    (polynomial K).eval x=(6435*x^8-12012*x^6+6930*x^4-1260*x^2+35)/128 := by
  simp [polynomial,raw,div_eq_mul_inv] <;> ring

theorem prime_value (x : K) :
    (polynomial K).derivative.eval x=(51480*x^7-72072*x^5+27720*x^3-2520*x)/128 := by
  rw [polynomial,derivative_mul,derivative_C,zero_mul,zero_add,raw_prime]
  simp [div_eq_mul_inv] <;> ring

@[simp] theorem at_one : (polynomial K).eval 1=1 := by norm_num [value]

private theorem nz : polynomial K≠0 := by
  intro h
  have v := at_one (K:=K)
  rw [h,eval_zero] at v
  exact zero_ne_one v

theorem degree : (polynomial K).natDegree≤8 := by
  have term (n k : ℕ) (hk : k≤8) : ((n:K[X])*X^k).natDegree≤8 := by
    rw [←C_eq_natCast]
    exact (natDegree_C_mul_X_pow_le _ _).trans hk
  have rawD : (raw K).natDegree≤8 :=
    natDegree_add_le_of_degree_le
      (natDegree_sub_le_of_le
        (natDegree_add_le_of_degree_le
          (natDegree_sub_le_of_le (term 6435 8 le_rfl) (term 12012 6 (by decide)))
          (term 6930 4 (by decide)))
        (term 1260 2 (by decide)))
      (by simp)
  exact (natDegree_C_mul_le _ _).trans rawD

private theorem coeff_eight : (polynomial K).coeff 8≠0 := by
  norm_num [polynomial,raw,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_ofNat_mul]

private theorem mode_C_mul {l a : K} {P : K[X]} (h : IsMode l P) : IsMode l (C a*P) := by
  change ((cap K)*P.derivative).derivative+C l*P=0 at h
  change ((cap K)*(C a*P).derivative).derivative+C l*(C a*P)=0
  rw [derivative_C_mul, show (cap K)*(C a*P.derivative)=C a*((cap K)*P.derivative) by ring, derivative_C_mul]
  linear_combination (C a)*h

private theorem mode_sub {l : K} {P Q : K[X]} (p : IsMode l P) (q : IsMode l Q) :
    IsMode l (P-Q) := by
  change ((cap K)*P.derivative).derivative+C l*P=0 at p
  change ((cap K)*Q.derivative).derivative+C l*Q=0 at q
  simp only [IsMode,derivative_sub,mul_sub]
  linear_combination p-q

theorem isMode : IsMode (72:K) (polynomial K) := by
  unfold polynomial
  apply mode_C_mul
  change ((cap K)*(raw K).derivative).derivative+C (72:K)*raw K=0
  rw [raw_prime]
  norm_num [cap,raw,derivative_mul,derivative_sub,derivative_add,derivative_X_pow,
    derivative_ofNat,derivative_natCast,map_ofNat] <;> ring

private theorem op_coeff (S : K[X]) (k : ℕ) :
    (((cap K)*S.derivative).derivative).coeff k =
      (S.coeff (k+2)*((k:K)+2)-S.coeff k*(k:K))*((k:K)+1) := by
  rw [coeff_derivative,cap,sub_mul,one_mul,coeff_sub,coeff_derivative,coeff_X_pow_mul']
  cases k with
  | zero => norm_num
  | succ k =>
    have a : 2≤k.succ+1 := by omega
    have b : (k.succ+1)-2+1=k.succ := by omega
    rw [if_pos a,coeff_derivative,b]
    simp only [Nat.succ_eq_add_one]
    rw [show k + 1 + 1 - 2 = k by omega]
    push_cast
    ring

private theorem small_mode_zero {S : K[X]} (d : S.natDegree≤7) (ode : IsMode (72:K) S) :
    S=0 := by
  by_contra sn
  let k := S.natDegree
  have zd : S.coeff (k+2)=0 := coeff_eq_zero_of_natDegree_lt (by dsimp [k];omega)
  change ((cap K)*S.derivative).derivative+C (72:K)*S=0 at ode
  have ko := congrArg (fun z : K[X] => z.coeff k) ode
  simp only [coeff_add,op_coeff,coeff_C_mul,zd,zero_mul,zero_sub,coeff_zero] at ko
  have ke : ((72:K)-(k:K)*((k:K)+1))*S.coeff k=0 := by linear_combination ko
  have hkn : k*(k+1)<(72:ℕ) :=
    (Nat.mul_le_mul d (Nat.succ_le_succ d)).trans_lt (by decide : 7*8<72)
  have hk : (k:K)*((k:K)+1)<72 := by exact_mod_cast hkn
  have non : S.coeff k≠0 := by simpa only [k,coeff_natDegree] using leadingCoeff_ne_zero.mpr sn
  exact non ((mul_eq_zero.mp ke).resolve_left (sub_ne_zero.mpr hk.ne'))

/-- No reference to a precomputed mesh or a root embedding: the mode
equation and endpoint value identify the usual normalized polynomial. -/
theorem eq_polynomial {P : K[X]} (d : P.natDegree≤8)
    (ode : IsMode (72:K) P) (at1 : P.eval 1=1) : P=polynomial K := by
  let a := P.coeff 8/(polynomial K).coeff 8
  let S := P-C a*polynomial K
  have am : a*(polynomial K).coeff 8=P.coeff 8 := div_mul_cancel₀ _ coeff_eight
  have s8 : S.natDegree≤8 := natDegree_sub_le_of_le d
    ((natDegree_C_mul_le _ _).trans degree)
  have s7 : S.natDegree≤7 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases e : n=8
    · subst n
      simp only [S,coeff_sub,coeff_C_mul,am,sub_self]
    · exact coeff_eq_zero_of_natDegree_lt (s8.trans_lt (by omega))
  have h := sub_eq_zero.mp (small_mode_zero s7 (mode_sub ode (mode_C_mul isMode)))
  have v := congrArg (Polynomial.eval (1:K)) h
  simp only [at1,eval_mul,eval_C,at_one,mul_one] at v
  rw [h,←v,C_1,one_mul]

private theorem prime_pos_at_anchor {x : K} (ax : (9:K)/10≤x) :
    0<(polynomial K).derivative.eval x := by
  let z := 10*x-9
  have z0 : 0≤z := by dsimp [z]; linarith
  have shift :
      (128:K)*10^7*(polynomial K).derivative.eval x =
      48091320+z*(19917482760+z*(18780604920+z*(6260977800+
        z*(989188200+z*(80360280+z*(3243240+51480*z)))))) := by
    rw [prime_value]
    dsimp only [z]
    ring
  have pos : 0<(128:K)*10^7*(polynomial K).derivative.eval x := by
    rw [shift]
    exact add_pos_of_pos_of_nonneg (by norm_num) (by positivity)
  exact (mul_pos_iff_of_pos_left (by norm_num : (0:K)<128*10^7)).mp pos

private theorem anchor_energy :
    (energy (72:K) (polynomial K)).eval ((9:K)/10)<(72:K)/4 := by
  simp only [energy,cap,eval_add,eval_mul,eval_sub,eval_C,eval_one,eval_X,eval_pow,
    value,prime_value]
  norm_num

private theorem energy_bound {x : K} (x0 : 0≤x) (dx : (polynomial K).derivative.eval x=0) :
    (energy (72:K) (polynomial K)).eval x<(72:K)/4 := by
  have xt : x<(9:K)/10 := lt_of_not_ge (fun h => (prime_pos_at_anchor h).ne' dx)
  exact (energy_le_of_nonneg degree isMode x0 xt.le).trans_lt anchor_energy

private theorem value_neg (x : K) : (polynomial K).eval (-x)=(polynomial K).eval x := by
  simp only [value]
  ring

private theorem prime_neg (x : K) :
    (polynomial K).derivative.eval (-x)=-(polynomial K).derivative.eval x := by
  simp only [prime_value]
  ring

private theorem prime_abs {x : K} (hx : (polynomial K).derivative.eval x=0) :
    (polynomial K).derivative.eval |x|=0 := by
  rcases abs_choice x with h | h
  · rwa [h]
  · rw [h,prime_neg,hx,neg_zero]

private theorem scale_abs (x : K) :
    criticalScale (polynomial K) |x|=criticalScale (polynomial K) x := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h]
    simp [criticalScale,value_neg,neg_sq]

theorem critical_sq_lt_quarter {P : K[X]} (d : P.natDegree≤8) (ode : IsMode (72:K) P)
    (at1 : P.eval 1=1) {x : K} (dx : P.derivative.eval x=0) :
    P.eval x^2<(1:K)/4 := by
  rw [eq_polynomial d ode at1] at dx ⊢
  have u := energy_bound (abs_nonneg x) (prime_abs dx)
  have e : (polynomial K).eval |x|=(polynomial K).eval x := by
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h,value_neg]
  have ev : (energy (72:K) (polynomial K)).eval |x|=(72:K)*(polynomial K).eval x^2 := by
    simp [energy,prime_abs dx,e]
  rw [ev] at u
  linarith only [u]

theorem criticalScale_eq_abs {P : K[X]} (d : P.natDegree≤8) (ode : IsMode (72:K) P)
    (at1 : P.eval 1=1) {x y : K} (x1 : |x|<1) (y1 : |y|<1)
    (dx : P.derivative.eval x=0) (dy : P.derivative.eval y=0)
    (same : criticalScale P x=criticalScale P y) : |x|=|y| := by
  rw [eq_polynomial d ode at1] at dx dy same
  have ex := energy_bound (abs_nonneg x) (prime_abs dx)
  have ey := energy_bound (abs_nonneg y) (prime_abs dy)
  rw [←scale_abs x,←scale_abs y] at same
  rcases lt_trichotomy |x| |y| with h | h | h
  · have v := criticalScale_strict_drop (by norm_num : (0:K)<72) nz degree isMode
      (abs_nonneg x) h y1 (prime_abs dx) (prime_abs dy) (ey.trans (by norm_num))
    exact False.elim (v.ne same.symm)
  · exact h
  · have v := criticalScale_strict_drop (by norm_num : (0:K)<72) nz degree isMode
      (abs_nonneg y) h x1 (prime_abs dy) (prime_abs dx) (ex.trans (by norm_num))
    exact False.elim (v.ne same)

/-- The exact three-node scalar input from the symplectic diagonal
obstruction. The common factor need not be positive as a premise. -/
theorem not_three_critical_common_factor {P : K[X]} (d : P.natDegree≤8)
    (ode : IsMode (72:K) P) (at1 : P.eval 1=1) (x : Fin 3 → K)
    (simple : Function.Injective x) (inside : ∀ i, |x i|<1)
    (critical : ∀ i, P.derivative.eval (x i)=0) (g : K)
    (paid : ∀ i, 1=P.eval (x i)^2*(1+g*(1-(x i)^2))) : False := by
  have small (i : Fin 3) := critical_sq_lt_quarter d ode at1 (critical i)
  have gn : g≠0 := by
    intro e
    have v := paid 0
    rw [e,zero_mul,add_zero,mul_one] at v
    linarith only [v,small 0]
  have level (i : Fin 3) : criticalScale P (x i)=1/g := by
    unfold criticalScale
    have h : 1-P.eval (x i)^2 ≠ 0 := (by linarith only [small i] : 0<1-P.eval (x i)^2).ne'
    apply (div_eq_div_iff h gn).mpr
    linear_combination -(paid i)
  have s₁ := criticalScale_eq_abs d ode at1 (inside 1) (inside 0) (critical 1) (critical 0)
    ((level 1).trans (level 0).symm)
  have s₂ := criticalScale_eq_abs d ode at1 (inside 2) (inside 0) (critical 2) (critical 0)
    ((level 2).trans (level 0).symm)
  have a : x 1=-(x 0) := (abs_eq_abs.mp s₁).resolve_left
    (fun h => (by decide : (1:Fin 3)≠0) (simple h))
  have b : x 2=-(x 0) := (abs_eq_abs.mp s₂).resolve_left
    (fun h => (by decide : (2:Fin 3)≠0) (simple h))
  exact (by decide : (1:Fin 3)≠2) (simple (a.trans b.symm))

end
end RKCert.ReviewedNative.LegendreModeEight
