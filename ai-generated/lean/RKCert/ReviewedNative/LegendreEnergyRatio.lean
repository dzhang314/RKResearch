module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.LegendreEnergy

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev cap (K : Type*) [Field K] : K[X] := 1-X^2

def IsMode (l : K) (P : K[X]) : Prop :=
  ((cap K)*P.derivative).derivative + C l*P = 0

def energy (l : K) (P : K[X]) : K[X] :=
  C l*P^2+(cap K)*P.derivative^2

def criticalScale (P : K[X]) (x : K) : K :=
  (1-x^2)*P.eval x^2/(1-P.eval x^2)

private def flux (l : K) (P : K[X]) : K[X] :=
  C (2*l)*(X*P*((cap K)*P.derivative)) + ((cap K)*P.derivative)^2

private theorem cap_prime : (cap K).derivative = -(C (2:K))*X := by
  norm_num [cap, derivative_X_sq, neg_mul, map_ofNat]

theorem energy_prime {l : K} {P : K[X]} (ode : IsMode l P) :
    (energy l P).derivative = C (2:K)*(X*P.derivative^2) := by
  change ((cap K)*P.derivative).derivative+C l*P=0 at ode
  rw [derivative_mul,cap_prime] at ode
  simp only [energy,derivative_add,derivative_mul,derivative_sq,
    derivative_C,zero_mul,zero_add,cap_prime]
  simp only [map_ofNat] at ode ⊢
  linear_combination (2 * P.derivative) * ode

private theorem cap_energy_prime {l : K} {P : K[X]} (ode : IsMode l P) :
    ((cap K)*energy l P).derivative = C (-(2*l))*(X*P^2) := by
  rw [derivative_mul,cap_prime,energy_prime ode]
  simp only [energy,map_neg,map_mul]
  ring

private theorem flux_prime {l : K} {P : K[X]} (ode : IsMode l P) :
    (flux l P).derivative = C (2*l)*(X*(energy l P-C (2*l)*P^2)) := by
  have B : ((cap K)*P.derivative).derivative = -(C l*P) := by
    change ((cap K)*P.derivative).derivative+C l*P=0 at ode
    linear_combination ode
  have pr : (X*P*((cap K)*P.derivative)).derivative =
      (P+X*P.derivative)*((cap K)*P.derivative)+(X*P)*(-(C l*P)) := by
    rw [derivative_mul,B,derivative_mul,derivative_X,one_mul]
  rw [flux,derivative_add,derivative_mul,derivative_C,zero_mul,zero_add,
    derivative_sq,B,pr]
  simp only [energy,map_mul,map_ofNat]
  ring

/-- Exact fundamental theorem for the zero-based formal primitive. -/
theorem integral_derivative (a b : K) (F : K[X]) :
    integral a b F.derivative = F.eval b-F.eval a := by
  have h : formalPrimitive F.derivative=F-C (F.eval 0) := by
    apply eq_of_derivative_and_eval_zero
    · simp only [derivative_formalPrimitive,derivative_sub,derivative_C,sub_zero]
    · simp
  rw [integral_apply,h]
  simp only [eval_sub,eval_C]
  ring

theorem integral_C_mul (a b l : K) (F : K[X]) :
    integral a b (C l*F)=l*integral a b F := by
  simpa only [smul_eq_C_mul,smul_eq_mul] using (integral a b).map_smul l F

private theorem integral_nonneg {r s : K} {F : K[X]} (rs : r<s)
    (d : F.natDegree≤19) (h : ∀ x∈Set.Ioo r s, 0≤F.eval x) :
    0 ≤ integral r s F := by
  rw [interval_exact r s F d]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (intervalWeight_pos rs i).le
    (h _ (intervalPoint_mem rs i))

private theorem derivative_deg {P : K[X]} (d : P.natDegree≤8) :
    P.derivative.natDegree≤7 := (natDegree_derivative_le P).trans (by omega)

private theorem cap_deg : (cap K).natDegree≤2 := by
  exact natDegree_sub_le_of_le (p := (1 : K[X])) (q := X ^ 2) (by rw [natDegree_one]) (by rw [natDegree_X_pow])

private theorem energy_deg {l : K} {P : K[X]} (d : P.natDegree≤8) :
    (energy l P).natDegree≤16 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 2 d)
  · exact natDegree_mul_le_of_le cap_deg
      (natDegree_pow_le_of_le 2 (derivative_deg d))

private theorem x_deriv_sq_deg {P : K[X]} (d : P.natDegree≤8) :
    ((X:K[X])*P.derivative^2).natDegree≤15 := by
  exact natDegree_mul_le_of_le natDegree_X.le (natDegree_pow_le_of_le 2 (derivative_deg d))

/-- Monotonicity on the nonnegative half-line, from the exact finite
polynomial integral of the derivative. -/
theorem energy_le_of_nonneg {l : K} {P : K[X]} (d : P.natDegree≤8)
    (ode : IsMode l P) {r s : K} (r0 : 0≤r) (rs : r≤s) :
    (energy l P).eval r≤(energy l P).eval s := by
  rcases rs.lt_or_eq with rs | rfl
  · have e := integral_derivative r s (energy l P)
    rw [energy_prime ode,integral_C_mul] at e
    have n : 0 ≤ integral r s ((X:K[X])*P.derivative^2) :=
      integral_nonneg rs ((x_deriv_sq_deg d).trans (by decide)) (by
        intro x hx
        simpa only [eval_mul,eval_X,eval_pow] using
          mul_nonneg (r0.trans hx.1.le) (sq_nonneg (P.derivative.eval x)))
    linarith only [e,n]
  · exact le_rfl

/-- The positive energy ratio strictly decreases along nonnegative
interior critical points, as long as the larger endpoint energy is
below half of the mode scale. -/
theorem criticalScale_strict_drop {l : K} {P : K[X]}
    (l0 : 0<l) (pn : P≠0) (d : P.natDegree≤8) (ode : IsMode l P)
    {r s : K} (r0 : 0≤r) (rs : r<s) (s1 : s<1)
    (dr : P.derivative.eval r=0) (ds : P.derivative.eval s=0)
    (capS : (energy l P).eval s<l/2) :
    criticalScale P s<criticalScale P r := by
  let U : K[X] := cap K
  let E : K[X] := energy l P
  let A := integral r s (X*P^2)
  let B := integral r s (X*(U*P.derivative^2))
  let D := integral r s (X*P.derivative^2)
  let T := integral r s (X*E)
  change E.eval s<l/2 at capS
  have fluxZero : integral r s (X*(E-C (2*l)*P^2))=0 := by
    have f := integral_derivative r s (flux l P)
    rw [flux_prime ode,integral_C_mul] at f
    change 2*l*integral r s (X*(E-C (2*l)*P^2)) =
      (flux l P).eval s-(flux l P).eval r at f
    simp only [flux,eval_add,eval_mul,eval_pow,ds,dr,mul_zero,
      zero_pow (by decide : (2:ℕ)≠0),add_zero,sub_zero] at f
    exact (mul_eq_zero.mp f).resolve_left (mul_ne_zero (by norm_num) l0.ne')
  have eqA : T=(2*l)*A := by
    have eq : X*(E-C (2*l)*P^2)=X*E-C (2*l)*(X*P^2) := by ring
    rw [eq,map_sub,integral_C_mul] at fluxZero
    exact sub_eq_zero.mp fluxZero
  have split : T=l*A+B := by
    dsimp only [T,A,B]
    rw [show X*E=C l*(X*P^2)+X*(U*P.derivative^2) by dsimp [E,U,energy]; ring,
      map_add,integral_C_mul]
  have eqB : T=2*B := by linear_combination 2*split-eqA
  have dE : E.eval s-E.eval r=2*D := by
    have h := integral_derivative r s E
    rw [show E.derivative=C (2:K)*(X*P.derivative^2) from energy_prime ode,
      integral_C_mul] at h
    exact h.symm
  have drop : U.eval r*E.eval r-U.eval s*E.eval s=T := by
    have h := integral_derivative r s (U*E)
    rw [show (U*E).derivative=C (-(2*l))*(X*P^2) from cap_energy_prime ode,
      integral_C_mul,eval_mul,eval_mul] at h
    linear_combination h-eqA
  have uDeg : (U-C (U.eval s)).natDegree≤2 :=
    natDegree_sub_le_of_le (p := U) (q := C (U.eval s)) cap_deg (by rw [natDegree_C])
  have testD : (X*((U-C (U.eval s))*P.derivative^2)).natDegree≤19 := by
    have e : (X*((U-C (U.eval s))*P.derivative^2)).natDegree≤17 :=
      natDegree_mul_le_of_le natDegree_X.le
        (natDegree_mul_le_of_le uDeg (natDegree_pow_le_of_le 2 (derivative_deg d)))
    exact e.trans (by decide)
  have diff : 0 ≤ integral r s (X*((U-C (U.eval s))*P.derivative^2)) :=
    integral_nonneg rs testD (by
      intro x hx
      have x0 := r0.trans hx.1.le
      have v : x^2≤s^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.le) (add_nonneg x0 (x0.trans hx.2.le))]
      simpa only [U,cap,eval_mul,eval_sub,eval_one,eval_C,eval_pow,eval_X] using
        mul_nonneg x0 (mul_nonneg (by linarith : 0≤(1-x^2)-(1-s^2))
          (sq_nonneg (P.derivative.eval x))))
  have rewrite : X*((U-C (U.eval s))*P.derivative^2) =
      X*(U*P.derivative^2)-C (U.eval s)*(X*P.derivative^2) := by ring
  rw [rewrite,map_sub,integral_C_mul] at diff
  have dCap : U.eval s*(E.eval s-E.eval r)≤T := by
    rw [dE,eqB]
    change 0≤B-U.eval s*D at diff
    nlinarith only [diff]
  have tDegree : (X*E).natDegree≤19 :=
    (natDegree_mul_le_of_le natDegree_X.le (energy_deg d) :
      (X*E).natDegree≤17).trans (by decide)
  have tPos : 0<T := by
    obtain ⟨i,ni⟩ := exists_nonzero_grid_sample rs pn (d.trans_lt (by decide))
    have es (x : K) (hx : x∈Set.Ioo r s) : 0≤U.eval x := by
      have x0 := r0.trans hx.1.le
      have x1 := hx.2.trans s1
      have h := mul_nonneg (sub_nonneg.mpr x1.le) (by linarith : 0≤1+x)
      simp only [U,cap,eval_sub,eval_one,eval_pow,eval_X]
      nlinarith only [h]
    have evalE (x : K) : E.eval x=l*P.eval x^2+U.eval x*P.derivative.eval x^2 := by
      simp only [E,energy,U,eval_add,eval_mul,eval_C,eval_pow]
    apply integral_pos_of_grid_samples rs tDegree
    · intro j
      have hj := intervalPoint_mem rs j
      rw [eval_mul,eval_X,evalE]
      exact mul_nonneg (r0.trans hj.1.le) (add_nonneg
        (mul_nonneg l0.le (sq_nonneg _)) (mul_nonneg (es _ hj) (sq_nonneg _)))
    · refine ⟨i,?_⟩
      have hi := intervalPoint_mem rs i
      rw [eval_mul,eval_X,evalE]
      exact mul_pos (r0.trans_lt hi.1) (add_pos_of_pos_of_nonneg
        (mul_pos l0 (sq_pos_of_ne_zero ni)) (mul_nonneg (es _ hi) (sq_nonneg _)))
  have es0 : 0≤E.eval s := by
    simpa [E,energy,ds] using mul_nonneg l0.le (sq_nonneg (P.eval s))
  have dR : 0<l-E.eval r := by
    have z := energy_le_of_nonneg d ode r0 rs.le
    change E.eval r≤E.eval s at z
    linarith only [l0,capS,z]
  have dS : 0<l-E.eval s := by linarith only [l0,capS]
  have sharp : 0<(l-2*E.eval s)*T := mul_pos (by linarith only [capS]) tPos
  have mulCap := mul_le_mul_of_nonneg_left dCap es0
  have cross : U.eval s*E.eval s*(l-E.eval r) <
      U.eval r*E.eval r*(l-E.eval s) := by
    calc
      _ < U.eval s*E.eval s*(l-E.eval r)+(l-2*E.eval s)*T :=
        lt_add_of_pos_right _ sharp
      _ ≤ U.eval r*E.eval r*(l-E.eval s) := by
        nlinarith only [mulCap, congrArg (fun v : K => (l-E.eval s)*v) drop]
  have compare := (div_lt_div_iff₀ dS dR).mpr cross
  have atCrit (x : K) (dx : P.derivative.eval x=0) (den : 0<l-E.eval x) :
      U.eval x*E.eval x/(l-E.eval x)=criticalScale P x := by
    have ev : E.eval x=l*P.eval x^2 := by simp [E,energy,dx]
    have last : 1-P.eval x^2 ≠ 0 := by
      intro e
      have h : l-E.eval x=l*(1-P.eval x^2) := by rw [ev]; ring
      rw [e,mul_zero] at h
      exact den.ne' h
    rw [ev]
    unfold criticalScale
    rw [show U.eval x=1-x^2 by simp [U,cap]]
    field_simp [l0.ne',last] <;> ring
  rwa [atCrit s ds dS,atCrit r dr dR] at compare

end
end RKCert.ReviewedNative.LegendreEnergy
