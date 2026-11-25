module

public import RKCert.ReviewedNative.LegendreModeEightShifted
public import RKCert.ReviewedNative.LegendreModeEightWindows
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.LegendreModeEight

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.LegendreEnergy
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def chordFlux (l : K) (P : K[X]) : K[X] :=
  C (2*l)*(X*P*((cap K)*P.derivative)) + ((cap K)*P.derivative)^2

private theorem cap_prime : (cap K).derivative = -(C (2:K))*X := by
  norm_num [cap, derivative_X_sq, neg_mul, map_ofNat]

private theorem cap_energy_prime {l : K} {P : K[X]} (ode : IsMode l P) :
    ((cap K)*energy l P).derivative = C (-(2*l))*(X*P^2) := by
  rw [derivative_mul,cap_prime,energy_prime ode]
  simp only [energy,map_neg,map_mul]
  ring

private theorem chordFlux_prime {l : K} {P : K[X]} (ode : IsMode l P) :
    (chordFlux l P).derivative = C (2*l)*(X*(energy l P-C (2*l)*P^2)) := by
  have B : ((cap K)*P.derivative).derivative = -(C l*P) := by
    change ((cap K)*P.derivative).derivative+C l*P=0 at ode
    linear_combination ode
  have pr : (X*P*((cap K)*P.derivative)).derivative =
      (P+X*P.derivative)*((cap K)*P.derivative)+(X*P)*(-(C l*P)) := by
    rw [derivative_mul,B,derivative_mul,derivative_X,one_mul]
  rw [chordFlux,derivative_add,derivative_mul,derivative_C,zero_mul,zero_add,
    derivative_sq,B,pr]
  simp only [energy,map_mul,map_ofNat]
  ring

private theorem chord_integral_nonneg {r s : K} {F : K[X]} (rs : r<s)
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

private theorem capBalance {l : K} {P : K[X]} (lp : 0<l) (ode : IsMode l P)
    {r s : K} (dr : P.derivative.eval r=0) (ds : P.derivative.eval s=0) :
    (1-r^2)*(energy l P).eval r-(1-s^2)*(energy l P).eval s =
      integral r s (X*energy l P) := by
  let U : K[X] := cap K
  let E : K[X] := energy l P
  let A := integral r s (X*P^2)
  let T := integral r s (X*E)
  have zero : integral r s (X*(E-C (2*l)*P^2))=0 := by
    have f := integral_derivative r s (chordFlux l P)
    rw [chordFlux_prime ode,integral_C_mul] at f
    change 2*l*integral r s (X*(E-C (2*l)*P^2)) =
      (chordFlux l P).eval s-(chordFlux l P).eval r at f
    simp only [chordFlux,eval_add,eval_mul,eval_pow,ds,dr,mul_zero,
      zero_pow (by decide : (2:ℕ)≠0),add_zero,sub_zero] at f
    exact (mul_eq_zero.mp f).resolve_left (mul_ne_zero (by norm_num) lp.ne')
  have eqA : T=(2*l)*A := by
    have eq : X*(E-C (2*l)*P^2)=X*E-C (2*l)*(X*P^2) := by ring
    rw [eq,map_sub,integral_C_mul] at zero
    exact sub_eq_zero.mp zero
  have drop : U.eval r*E.eval r-U.eval s*E.eval s=T := by
    have h := integral_derivative r s (U*E)
    rw [show (U*E).derivative=C (-(2*l))*(X*P^2) from cap_energy_prime ode,
      integral_C_mul,eval_mul,eval_mul] at h
    linear_combination h-eqA
  simpa only [U,E,T,cap,eval_sub,eval_one,eval_pow,eval_X] using drop

private theorem integral_X_eq (r s : K) :
    integral r s (X:K[X])=(s^2-r^2)/2 := by
  have e := integral_derivative r s (X^2:K[X])
  rw [derivative_X_sq,integral_C_mul] at e
  simp only [eval_pow,eval_X] at e
  linarith only [e]

private theorem weightedEnergyBounds {l : K} {P : K[X]}
    (de : P.natDegree≤8) (ode : IsMode l P) {r s : K} (r0 : 0≤r) (rs : r<s) :
    (energy l P).eval r*(s^2-r^2)/2 ≤ integral r s (X*energy l P) ∧
      integral r s (X*energy l P)≤(energy l P).eval s*(s^2-r^2)/2 := by
  let E := energy l P
  have dg (a : K) : (X*(E-C a)).natDegree≤19 := by
    have e16 : E.natDegree ≤ 16 := energy_deg (l := l) de
    have c16 : (C a).natDegree ≤ 16 := by simp
    have v : (E-C a).natDegree ≤ 16 := natDegree_sub_le_of_le e16 c16
    exact (natDegree_mul_le_of_le natDegree_X.le v : _ ≤ 17).trans (by decide)
  have lo : 0 ≤ integral r s (X*(E-C (E.eval r))) :=
    chord_integral_nonneg rs (dg _) (by
      intro x hx
      rw [eval_mul,eval_X,eval_sub,eval_C]
      exact mul_nonneg (r0.trans hx.1.le)
        (sub_nonneg.mpr (energy_le_of_nonneg de ode r0 hx.1.le)))
  have hi : 0 ≤ integral r s (-(X*(E-C (E.eval s)))) :=
    chord_integral_nonneg rs ((natDegree_neg _).trans_le (dg _)) (by
      intro x hx
      simp only [eval_neg,eval_mul,eval_X,eval_sub,eval_C,←mul_neg,neg_sub]
      exact mul_nonneg (r0.trans hx.1.le)
        (sub_nonneg.mpr (energy_le_of_nonneg de ode (r0.trans hx.1.le) hx.2.le)))
  have expansion (a : K) : X*(E-C a)=X*E-C a*X := by ring
  rw [expansion,map_sub,integral_C_mul,integral_X_eq] at lo
  rw [map_neg,expansion,map_sub,integral_C_mul,integral_X_eq] at hi
  change E.eval r*(s^2-r^2)/2 ≤ integral r s (X*E) ∧
    integral r s (X*E)≤E.eval s*(s^2-r^2)/2
  constructor <;> linarith only [lo,hi]

private theorem parity_value (t : K) : (polynomial K).eval (-t)=(polynomial K).eval t := by
  rw [value,value]
  ring

private theorem parity_prime (t : K) :
    (polynomial K).derivative.eval (-t)=-(polynomial K).derivative.eval t := by
  rw [prime_value,prime_value]
  ring

private theorem parity_scale (t : K) :
    criticalScale (polynomial K) (-t)=criticalScale (polynomial K) t := by
  simp only [criticalScale,parity_value,neg_sq]

private theorem scale_abs_eq (t : K) :
    criticalScale (polynomial K) |t|=criticalScale (polynomial K) t := by
  rcases abs_choice t with e|e
  · rw [e]
  · rw [e,parity_scale]

private theorem prime_at_abs {t : K} (d : (polynomial K).derivative.eval t=0) :
    (polynomial K).derivative.eval |t|=0 := by
  rcases abs_choice t with e|e
  · rwa [e]
  · rw [e,parity_prime,d,neg_zero]

private theorem upper_energy_at_critical {t : K} (t0 : 0≤t)
    (dt : (polynomial K).derivative.eval t=0) :
    (energy (72:K) (polynomial K)).eval t<(72:K)/5 := by
  have anchor : (energy (72:K) (polynomial K)).eval ((9:K)/10)<(72:K)/5 := by
    simp only [energy,cap,eval_add,eval_mul,eval_sub,eval_C,eval_one,eval_X,eval_pow,
      value,prime_value]
    norm_num
  have le9 : t≤(9:K)/10 := by
    rcases t0.eq_or_lt with h|h
    · rw [←h]
      norm_num
    · rcases LegendreModeEightWindows.positive_critical_windows h dt with u|u|u
      · exact u.2.le.trans (by norm_num)
      · exact u.2.le.trans (by norm_num)
      · exact u.2.le
  exact (energy_le_of_nonneg degree isMode t0 le9).trans_lt anchor

private theorem critical_value_bounds {t : K} (t0 : 0≤t)
    (dt : (polynomial K).derivative.eval t=0) :
    0<(polynomial K).eval t^2 ∧ (polynomial K).eval t^2<1/5 := by
  have lo : 0<(energy (72:K) (polynomial K)).eval 0 := by
    simp only [energy,cap,eval_add,eval_mul,eval_sub,eval_C,eval_one,eval_X,eval_pow,
      value,prime_value]
    norm_num
  have l := lo.trans_le (energy_le_of_nonneg degree isMode (show (0:K)≤0 from le_rfl) t0)
  have u := upper_energy_at_critical t0 dt
  simp only [energy,eval_add,eval_mul,eval_C,eval_pow,dt,
    zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero] at l u
  constructor <;> linarith only [l,u]

private theorem drop_at_radii {r s : K} (r0 : 0≤r) (rs : r<s) (s1 : s<1)
    (dr : (polynomial K).derivative.eval r=0) (ds : (polynomial K).derivative.eval s=0) :
    criticalScale (polynomial K) s<criticalScale (polynomial K) r := by
  have pn : polynomial K≠0 := by intro h;have v := at_one (K:=K);rw [h,eval_zero] at v;exact zero_ne_one v
  exact criticalScale_strict_drop (by norm_num : (0:K)<72) pn degree isMode r0 rs s1 dr ds
    ((upper_energy_at_critical (r0.trans rs.le) ds).trans (by norm_num))

/-- Bounds for each normalized secant of the even degree-eight mode.
The weighted energy integral costs at most degree seventeen. -/
theorem critical_secant_bounds {r s : K} (r0 : 0≤r) (rs : r<s)
    (dr : (polynomial K).derivative.eval r=0) (ds : (polynomial K).derivative.eval s=0) :
    let u := (polynomial K).eval r^2
    let v := (polynomial K).eval s^2
    3*(r+s)*u/(8*(1-u))≤(criticalScale (polynomial K) r-criticalScale (polynomial K) s)/(s-r) ∧
      (criticalScale (polynomial K) r-criticalScale (polynomial K) s)/(s-r)≤
        (r+s)*v/(2*(1-v)) := by
  let P := polynomial K
  let u := P.eval r^2
  let v := P.eval s^2
  let T := (integral r s (X*energy (72:K) P))/72
  let D := (1-u)*(1-v)
  let M := (criticalScale P r-criticalScale P s)/(s-r)
  change 3*(r+s)*u/(8*(1-u))≤M ∧ M≤(r+s)*v/(2*(1-v))
  have s0 : 0≤s := r0.trans rs.le
  obtain ⟨u0,u5⟩ := critical_value_bounds r0 dr
  obtain ⟨v0,v5⟩ := critical_value_bounds s0 ds
  change 0<u at u0
  change u<1/5 at u5
  change 0<v at v0
  change v<1/5 at v5
  have ul : 0<1-u := by linarith only [u5]
  have vl : 0<1-v := by linarith only [v5]
  have D0 : 0<D := mul_pos ul vl
  have rs0 : 0<r+s := add_pos_of_nonneg_of_pos r0 (r0.trans_lt rs)
  have sep : 0<s-r := sub_pos.mpr rs
  have int := weightedEnergyBounds (K:=K) degree isMode r0 rs
  have bal := capBalance (by norm_num : (0:K)<72) isMode dr ds
  have er : (energy (72:K) P).eval r=72*u := by
    simp only [energy,eval_add,eval_mul,eval_C,eval_pow,show P.derivative.eval r=0 from dr,
      zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero,u]
  have es : (energy (72:K) P).eval s=72*v := by
    simp only [energy,eval_add,eval_mul,eval_C,eval_pow,show P.derivative.eval s=0 from ds,
      zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero,v]
  change (energy (72:K) P).eval r*(s^2-r^2)/2 ≤ integral r s (X*energy (72:K) P) ∧
    integral r s (X*energy (72:K) P)≤(energy (72:K) P).eval s*(s^2-r^2)/2 at int
  change (1-r^2)*(energy (72:K) P).eval r-(1-s^2)*(energy (72:K) P).eval s=
    integral r s (X*energy (72:K) P) at bal
  rw [er,es] at int bal
  have lo : (s^2-r^2)*u/2≤T := by dsimp only [T]; linarith only [int.1]
  have hi : T≤(s^2-r^2)*v/2 := by dsimp only [T]; linarith only [int.2]
  have bal' : (1-r^2)*u-(1-s^2)*v=T := by dsimp only [T];linear_combination (1/72:K)*bal
  have numerator : (criticalScale P r-criticalScale P s)*D=T-(s^2-r^2)*u*v := by
    change (((1-r^2)*u/(1-u))-((1-s^2)*v/(1-v)))*((1-u)*(1-v))=_
    calc
      _ = (1-r^2)*u*(1-v)-(1-s^2)*v*(1-u) := by
        field_simp [ul.ne',vl.ne'] <;> ring
      _ = _ := by linear_combination bal'
  have scaleM : M*D=(T-(s^2-r^2)*u*v)/(s-r) := by
    dsimp only [M]
    rw [div_mul_eq_mul_div₀,numerator]
  have lower : (3*(r+s)*u/(8*(1-u)))*D≤(r+s)*(u/2-u*v) := by
    rw [show (3*(r+s)*u/(8*(1-u)))*D=3*(r+s)*u*(1-v)/8 by
      dsimp only [D];field_simp [ul.ne'] <;> ring]
    have w := mul_nonneg (mul_nonneg rs0.le u0.le) (show 0≤1-5*v by linarith only [v5])
    nlinarith only [w]
  have upper : (r+s)*(v/2-u*v)≤((r+s)*v/(2*(1-v)))*D := by
    rw [show ((r+s)*v/(2*(1-v)))*D=(r+s)*v*(1-u)/2 by
      dsimp only [D];field_simp [vl.ne'] <;> ring]
    nlinarith only [mul_nonneg (mul_nonneg rs0.le u0.le) v0.le]
  have rewrite (a : K) : ((s^2-r^2)*a/2-(s^2-r^2)*u*v)/(s-r)=(r+s)*(a/2-u*v) := by
    field_simp [sep.ne'] <;> ring
  have low := (div_le_div_iff_of_pos_right sep).mpr
    (sub_le_sub_right lo ((s^2-r^2)*u*v))
  have high := (div_le_div_iff_of_pos_right sep).mpr
    (sub_le_sub_right hi ((s^2-r^2)*u*v))
  rw [rewrite,←scaleM] at low
  rw [rewrite,←scaleM] at high
  exact ⟨(mul_le_mul_iff_of_pos_right D0).mp (lower.trans low),
    (mul_le_mul_iff_of_pos_right D0).mp (high.trans upper)⟩

private theorem strict_positive_chord {p r s : K} (p0 : 0≤p) (pr : p<r) (rs : r<s)
    (dp : (polynomial K).derivative.eval p=0) (dr : (polynomial K).derivative.eval r=0)
    (ds : (polynomial K).derivative.eval s=0) :
    (criticalScale (polynomial K) p-criticalScale (polynomial K) r)/(r-p)<
      (criticalScale (polynomial K) r-criticalScale (polynomial K) s)/(s-r) := by
  have a := (critical_secant_bounds p0 pr dp dr).2
  have b := (critical_secant_bounds (p0.trans pr.le) rs dr ds).1
  let v := (polynomial K).eval r^2
  change (criticalScale (polynomial K) p-criticalScale (polynomial K) r)/(r-p)≤
    (p+r)*v/(2*(1-v)) at a
  change 3*(r+s)*v/(8*(1-v))≤
    (criticalScale (polynomial K) r-criticalScale (polynomial K) s)/(s-r) at b
  obtain ⟨v0,v5⟩ := critical_value_bounds (p0.trans pr.le) dr
  have spacing := LegendreModeEightWindows.critical_three_spacing p0 pr rs dp dr ds
  have dv : 0<1-v := by
    change 0<1-(polynomial K).eval r^2
    linarith only [v5]
  have aD : 0<2*(1-v) := mul_pos (by norm_num) dv
  have bD : 0<8*(1-v) := mul_pos (by norm_num) dv
  have comparison : (p+r)*v/(2*(1-v))<3*(r+s)*v/(8*(1-v)) := by
    apply (div_lt_div_iff₀ aD bD).mpr
    have vf : 0<v*(1-v) := mul_pos v0 dv
    nlinarith only [mul_pos (show 0<3*s-(4*p+r) by linarith only [spacing]) vf]
  exact a.trans_lt (comparison.trans_le b)

private theorem three_sorted {x : Fin 3→K} (inj : Function.Injective x) :
    ∃ i j k : Fin 3, x i<x j ∧ x j<x k := by
  have ne01 : x 0≠x 1 := fun e=>(by decide : (0:Fin 3)≠1) (inj e)
  have ne12 : x 1≠x 2 := fun e=>(by decide : (1:Fin 3)≠2) (inj e)
  have ne02 : x 0≠x 2 := fun e=>(by decide : (0:Fin 3)≠2) (inj e)
  rcases lt_or_gt_of_ne ne01 with h01|h10
  · rcases lt_or_gt_of_ne ne12 with h12|h21
    · exact ⟨0,1,2,h01,h12⟩
    · rcases lt_or_gt_of_ne ne02 with h02|h20
      · exact ⟨0,2,1,h02,h21⟩
      · exact ⟨2,0,1,h20,h01⟩
  · rcases lt_or_gt_of_ne ne02 with h02|h20
    · exact ⟨1,0,2,h10,h02⟩
    · rcases lt_or_gt_of_ne ne12 with h12|h21
      · exact ⟨1,2,0,h12,h20⟩
      · exact ⟨2,1,0,h21,h10⟩

private theorem no_negative_chord (x : Fin 3→K) (simple : Function.Injective x)
    (inside : ∀ i, |x i|<1) (critical : ∀ i, (polynomial K).derivative.eval (x i)=0)
    (a b : K) (bn : b<0) (affine : ∀ i, criticalScale (polynomial K) (x i)=a+b*x i) :
    False := by
  have radInj : Function.Injective (fun i=>|x i|) := by
    intro i j h
    apply simple
    have h' : criticalScale (polynomial K) |x i|=criticalScale (polynomial K) |x j| :=
      congrArg (criticalScale (polynomial K)) h
    rw [scale_abs_eq,scale_abs_eq,affine,affine] at h'
    exact mul_left_cancel₀ bn.ne (add_left_cancel h')
  obtain ⟨i,j,k,hij,hjk⟩ := three_sorted radInj
  have sameOrder {i j : Fin 3} (r : |x i| < |x j|) : x i<x j := by
    have e := drop_at_radii (abs_nonneg _) r (inside j)
      (prime_at_abs (critical i)) (prime_at_abs (critical j))
    rw [scale_abs_eq,scale_abs_eq,affine,affine] at e
    by_contra! h
    nlinarith only [e,mul_nonpos_of_nonpos_of_nonneg bn.le (sub_nonneg.mpr h)]
  have pos {i j : Fin 3} (r : |x i| < |x j|) : 0≤x j := by
    have h := sameOrder r
    by_contra! z
    rw [abs_of_neg z] at r
    linarith only [r,h,neg_abs_le (x i)]
  have j0 := pos hij
  have k0 := pos hjk
  have ij := sameOrder hij
  have jk := sameOrder hjk
  have cj := prime_at_abs (critical j)
  have ck := prime_at_abs (critical k)
  have c := strict_positive_chord (abs_nonneg _) hij hjk
    (prime_at_abs (critical i)) cj ck
  have strictD := drop_at_radii (abs_nonneg _) hij (inside j)
    (prime_at_abs (critical i)) cj
  rw [scale_abs_eq,scale_abs_eq] at strictD
  rw [scale_abs_eq,abs_of_nonneg j0,abs_of_nonneg k0] at c
  let D := criticalScale (polynomial K) (x i)-criticalScale (polynomial K) (x j)
  have d0 : 0≤D := (sub_pos.mpr strictD).le
  have sd : D/(x j-x i)≤D/(x j-|x i|) :=
    div_le_div_of_nonneg_left d0 (sub_pos.mpr (by simpa only [abs_of_nonneg j0] using hij))
      (sub_le_sub_left (le_abs_self (x i)) _)
  have ai : D/(x j-x i)= -b := by
    dsimp only [D]
    rw [affine,affine]
    field_simp [sub_ne_zero.mpr ij.ne'] <;> ring
  have ak : (criticalScale (polynomial K) (x j)-criticalScale (polynomial K) (x k))/(x k-x j)= -b := by
    rw [affine,affine]
    field_simp [sub_ne_zero.mpr jk.ne'] <;> ring
  exact (lt_irrefl (-b)) (ai.symm.trans_lt (sd.trans_lt (c.trans_eq ak)))

/-- A line meets the finite critical-value set in at most two distinct
centred nodes. The argument uses only the supplied ordered field. -/
theorem no_critical_scale_affine {P : K[X]} (d : P.natDegree≤8)
    (ode : IsMode (72:K) P) (at1 : P.eval 1=1) (x : Fin 3→K)
    (simple : Function.Injective x) (inside : ∀ i, |x i|<1)
    (critical : ∀ i, P.derivative.eval (x i)=0) (a b : K)
    (affine : ∀ i, criticalScale P (x i)=a+b*x i) : False := by
  rw [eq_polynomial d ode at1] at critical affine
  rcases lt_trichotomy b 0 with bn|bz|bp
  · exact no_negative_chord x simple inside critical a b bn affine
  · have v (i : Fin 3) : criticalScale (polynomial K) (x i)=a := by simpa [bz] using affine i
    have eq (i : Fin 3) : |x i|=|x 0| := criticalScale_eq_abs degree isMode at_one
      (inside i) (inside 0) (critical i) (critical 0) ((v i).trans (v 0).symm)
    have jump (i : Fin 3) (i0 : i≠0) : x i=-(x 0) :=
      (abs_eq_abs.mp (eq i)).resolve_left (fun h=>i0 (simple h))
    exact (by decide : (1:Fin 3)≠2) (simple ((jump 1 (by decide)).trans (jump 2 (by decide)).symm))
  · let y (i : Fin 3) := -(x i)
    have ys : Function.Injective y := fun i j e=>simple (neg_injective e)
    have yin (i : Fin 3) : |y i|<1 := by simpa only [y,abs_neg] using inside i
    have dy (i : Fin 3) : (polynomial K).derivative.eval (y i)=0 := by
      change (polynomial K).derivative.eval (-(x i)) = 0
      rw [parity_prime,critical,neg_zero]
    refine no_negative_chord y ys yin dy a (-b) (neg_lt_zero.mpr bp) ?_
    intro i
    change criticalScale (polynomial K) (-(x i)) = a + (-b) * (-(x i))
    rw [parity_scale,affine]
    ring

/-- Shifted form used by the diagonal proof. No associated knot
polynomial or pointer to a particular tableau is part of the premise. -/
theorem no_shifted_critical_scale_affine {L : K[X]} (d : L.natDegree≤8)
    (ode : ((X*(1-X))*L.derivative).derivative+C (72:K)*L=0)
    (at1 : L.eval 1=1) (r : Fin 3→K) (simple : Function.Injective r)
    (inside : ∀ i, 0<r i ∧ r i<1) (critical : ∀ i, L.derivative.eval (r i)=0)
    (a b : K) (affine : ∀ i, r i*(1-r i)*L.eval (r i)^2/(1-L.eval (r i)^2)=a+b*r i) :
    False := by
  let x (i : Fin 3) := 2*r i-1
  apply no_critical_scale_affine (centered_degree d) (centered_isMode ode) (centered_at_one at1)
    x ?_ ?_ (fun i=>centered_critical (critical i)) (4*a+2*b) (2*b) ?_
  · intro i j e
    apply simple
    change 2*r i-1=2*r j-1 at e
    linarith only [e]
  · intro i
    apply abs_lt.mpr
    have h := inside i
    change -1<2*r i-1 ∧ 2*r i-1<1
    exact ⟨by linarith only [h.1],by linarith only [h.2]⟩
  · intro i
    change (1-(2*r i-1)^2)*(centered L).eval (2*r i-1)^2/
      (1-(centered L).eval (2*r i-1)^2)=4*a+2*b+(2*b)*(2*r i-1)
    rw [centered_value]
    rw [show 1-(2*r i-1)^2=4*(r i*(1-r i)) by ring, mul_assoc,mul_div_assoc,affine]
    ring

end
end RKCert.ReviewedNative.LegendreModeEight
