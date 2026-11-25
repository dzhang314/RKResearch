module

public import RKCert.ReviewedNative.HankelQuarticLegendreReceipts
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Div

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Seven concrete Legendre quartic obstruction ports

No port is a hypothesis. Each contradiction exposes its actual
polynomial divisions and paid coefficient arithmetic. -/
namespace RKResearch.Certified.Graded.HankelQuarticLegendre

open Polynomial HankelLegendreIntData
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K] {I : K[X] →ₗ[K] K}

private theorem paid_nat_ne (R : PaidLegendre28 I) : (paidNat : K) ≠ 0 := by
  have h : ∀ n ≤ 20, ((n.factorial : ℕ) : K) ≠ 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Nat.factorial_succ, Nat.cast_mul]
      exact mul_ne_zero (R.units (n+1) (by omega) (by omega)) (ih (by omega))
  rw [paidNat_eq_factorial]
  exact h 20 (by decide)

private theorem paid_divisor_ne (R : PaidLegendre28 I) (n : ℕ)
    (divides : n ∣ paidNat^2) : (n : K) ≠ 0 := by
  intro hn
  obtain ⟨m,he⟩ := divides
  apply pow_ne_zero 2 (paid_nat_ne R)
  rw [← Nat.cast_pow, he, Nat.cast_mul, hn, zero_mul]

private theorem beta_ne (R : PaidLegendre28 I) (n : ℕ) (lo : 0<n) (hi : n≤9) : beta K n ≠ 0 :=
  div_ne_zero (pow_ne_zero 2 (R.units n lo (by omega)))
    (mul_ne_zero (R.units _ (by omega) (by omega)) (R.units _ (by omega) (by omega)))

private theorem mode_lead (R : PaidLegendre28 I) (n : ℕ) (hn : n≤10) :
    (L K n).coeff n = 1 := by
  simpa only [R.modeDegree n hn] using (R.modeMonic n hn).coeff_natDegree

private theorem tail_lead (R : PaidLegendre28 I) (a n : ℕ)
    (al : 5≤a) (ar : a≤7) (an : a+n≤11) : (T K a n).coeff n = 1 := by
  simpa only [R.tailDegree a n al ar an] using (R.tailMonic a n al ar an).coeff_natDegree

@[simp] private theorem reflect_X : reflect K (X : K[X]) = -X := by
  simp only [reflect, Polynomial.coe_compRingHom_apply, X_comp]

@[simp] private theorem reflect_C (a : K) : reflect K (C a) = C a := by
  simp only [reflect, Polynomial.coe_compRingHom_apply, C_comp]

private theorem poly_two : C (2 : K) = (2 : K[X]) := by
  exact Polynomial.C_ofNat 2

private theorem cancel_C_dvd {P Q : K[X]} {a : K} (a0 : a≠0) (h : P∣C a*Q) : P∣Q := by
  have h' := h.mul_left (C (a⁻¹))
  rwa [←mul_assoc, ←map_mul, inv_mul_cancel₀ a0, map_one, one_mul] at h'

private theorem split_even_odd_eq {E O E' O' : K[X]} (two : (2:K)≠0)
    (ee : reflect K E=E) (oo : reflect K O=-O)
    (ee' : reflect K E'=E') (oo' : reflect K O'=-O') (eq : E+O=E'+O') :
    E=E' ∧ O=O' := by
  have re := congrArg (reflect K) eq
  simp only [map_add, ee, oo, ee', oo'] at re
  have twoP : (2 : K[X]) ≠ 0 := by rw [←poly_two]; exact C_ne_zero.mpr two
  constructor
  · apply mul_left_cancel₀ twoP
    linear_combination eq + re
  · apply mul_left_cancel₀ twoP
    linear_combination eq - re

/-- Division by an even monic polynomial is not needed: reflect the
literal divisibility and cancel the paid factor two. -/
private theorem even_divisor_splits {P E O : K[X]} (two : (2:K)≠0)
    (pp : reflect K P=P) (ee : reflect K E=E) (oo : reflect K O=-O) (h : P∣E+O) :
    P∣E ∧ P∣O := by
  have hr : reflect K P ∣ reflect K (E+O) := map_dvd (reflect K) h
  simp only [pp,map_add,ee,oo] at hr
  constructor
  · apply cancel_C_dvd two
    convert dvd_add h hr using 1
    rw [poly_two]
    ring
  · apply cancel_C_dvd two
    convert dvd_sub h hr using 1
    rw [poly_two]
    ring

private theorem monic_mix {A B : K[X]} (am : A.Monic)
    (lt : B.natDegree<A.natDegree) (a : K) :
    (A+C a*B).Monic ∧ (A+C a*B).natDegree=A.natDegree := by
  have hdeg : (C a*B).degree < A.degree := by
    rw [degree_eq_natDegree am.ne_zero]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr ((natDegree_C_mul_le a B).trans_lt lt))
  exact ⟨am.add_of_left hdeg, natDegree_add_eq_left_of_natDegree_lt ((natDegree_C_mul_le a B).trans_lt lt)⟩

private theorem linear_quotient {P F : K[X]} {n : ℕ} (pm : P.Monic) (pd : P.natDegree=n)
    (fm : F.Monic) (fd : F.natDegree=n+1) (dvd : P∣F) : ∃ v : K, F=(X+C v)*P := by
  obtain ⟨D,e⟩ := dvd
  have dm : D.Monic := pm.of_mul_monic_left (e ▸ fm)
  have hdeg := natDegree_mul pm.ne_zero dm.ne_zero
  rw [←e,fd,pd] at hdeg
  have dd : D.natDegree=1 := by omega
  refine ⟨D.coeff 0, ?_⟩
  calc
    F = P * D := e
    _ = D * P := mul_comm _ _
    _ = (X + C (D.coeff 0)) * P :=
      congrArg (fun W : K[X] => W * P) (dm.eq_X_add_C dd)

private theorem divisor_coprime_mix {P A B : K[X]} {a : K} (cop : IsCoprime A B)
    (d : P∣A+C a*B) : IsCoprime P B := by
  obtain ⟨u,v,e⟩ := cop
  have c : IsCoprime (A+C a*B) B := ⟨u,v-u*C a,by linear_combination e⟩
  exact c.of_isCoprime_of_dvd_left d

private theorem reduce_mix {P A B U V : K[X]} {a b : K}
    (cop : IsCoprime A B) (d : P∣A+C a*B) (e : P∣U*A-C b*V*B) :
    P∣C a*U+C b*V := by
  have h := dvd_sub (d.mul_left U) e
  have z : U*(A+C a*B)-(U*A-C b*V*B) = (C a*U+C b*V)*B := by ring
  rw [z] at h
  exact (divisor_coprime_mix cop d).dvd_of_dvd_mul_right h

private theorem reduce_scaled_mix {P A B U V : K[X]} {a b : K}
    (cop : IsCoprime A B) (a0 : a≠0) (d : P∣A+C a*B) (e : P∣U*A-C b*V*B) :
    P∣ U+C (b/a)*V := by
  apply cancel_C_dvd a0
  rw [mul_add,←mul_assoc,←map_mul,mul_div_cancel₀ b a0]
  exact reduce_mix cop d e

private theorem reduce_pure {P A B U V : K[X]} {b : K}
    (cop : IsCoprime A B) (b0 : b≠0) (d : P∣A) (e : P∣U*A-C b*V*B) : P∣V := by
  have h : P∣C (0:K)*U+C b*V := reduce_mix cop (by simpa using d) e
  apply cancel_C_dvd b0
  simpa using h

private theorem fatal_frac {F : K[X]} {i a d : ℕ} (R : PaidLegendre28 I)
    (pa : a∣paidNat^2) (pd : d∣paidNat^2) (c : F.coeff i=(a:K)/(d:K)) (z : F=0) : False := by
  have h : F.coeff i=0 := by simp [z]
  rw [c] at h
  exact (div_ne_zero (paid_divisor_ne R a pa) (paid_divisor_ne R d pd)) h

private theorem coeff_zero_of_zero {F : K[X]} (z : F=0) (j : ℕ) : F.coeff j=0 := by simp [z]

private theorem fatal_neg_frac {F : K[X]} {i a d : ℕ} (R : PaidLegendre28 I)
    (pa : a∣paidNat^2) (pd : d∣paidNat^2) (c : F.coeff i=-(a:K)/(d:K)) (z : F=0) : False := by
  have h := coeff_zero_of_zero z i
  rw [c] at h
  exact (div_ne_zero (neg_ne_zero.mpr (paid_divisor_ne R a pa)) (paid_divisor_ne R d pd)) h

/-- `5,5*`: reduction modulo the initial pure quartic. -/
theorem no_five_five (R : PaidLegendre28 I) (h : L K 4 ∣ L K 9) : False := by
  rw [R.step94] at h
  have d : L K 4 ∣ T K 6 4 := reduce_pure R.cop43 (beta_ne R 4 (by decide) (by decide)) (dvd_refl _) h
  have eq : T K 6 4 = L K 4 := eq_of_monic_of_dvd_of_natDegree_le
    (R.modeMonic 4 (by decide)) (R.tailMonic 6 4 (by decide) (by decide) (by decide)) d
    (by rw [R.tailDegree 6 4 (by decide) (by decide) (by decide),R.modeDegree 4 (by decide)] <;> decide)
  exact fatal_frac (a := 135) (d := 1309) R (by decide +kernel) (by decide +kernel) R.coeff55 (sub_eq_zero.mpr eq)

/-- `4,5*`: a nonzero odd companion and a pure terminal mode. -/
theorem no_four_five (R : PaidLegendre28 I) {a : K} (ha : a≠0)
    (h : L K 4+C a*L K 3 ∣ L K 8) : False := by
  let P := L K 4+C a*L K 3
  have pd := monic_mix (R.modeMonic 4 (by decide)) (B := L K 3)
    (by rw [R.modeDegree 3 (by decide),R.modeDegree 4 (by decide)]; decide) a
  change P∣L K 8 at h
  rw [R.step84] at h
  have d : P∣ T K 5 4+C (beta K 4/a)*T K 6 3 := reduce_scaled_mix (a := a) R.cop43 ha (dvd_refl P) h
  have td := monic_mix (R.tailMonic 5 4 (by decide) (by decide) (by decide)) (B := T K 6 3)
    (by rw [R.tailDegree 5 4 (by decide) (by decide) (by decide),R.tailDegree 6 3 (by decide) (by decide) (by decide)]; decide)
    (beta K 4/a)
  have eq : T K 5 4+C (beta K 4/a)*T K 6 3 = P := eq_of_monic_of_dvd_of_natDegree_le pd.1 td.1 d
    (by rw [td.2,pd.2,R.tailDegree 5 4 (by decide) (by decide) (by decide),R.modeDegree 4 (by decide)] <;> decide)
  have e := split_even_odd_eq (R.units 2 (by decide) (by decide))
    (R.tailEven 5 4 (by decide) (by decide) (by decide) (by decide))
    (show reflect K (C (beta K 4/a)*T K 6 3) = -(C (beta K 4/a)*T K 6 3) by
      simp [R.tailOdd 6 3 (by decide) (by decide) (by decide) (by decide)])
    (R.modeEven 4 (by decide) (by decide))
    (show reflect K (C a*L K 3) = -(C a*L K 3) by simp [R.modeOdd 3 (by decide) (by decide)]) eq
  exact fatal_frac (a := 32) (d := 315) R (by decide +kernel) (by decide +kernel) R.coeff45 (sub_eq_zero.mpr e.1)

/-- `5,4*`: split the even-mask divisibility instead of assuming any
uniqueness or parity of a masked residual. -/
theorem no_five_four (R : PaidLegendre28 I) (a : K) (h : L K 4 ∣ L K 9+C a*L K 8) : False := by
  have h' : L K 4 ∣ C a*L K 8+L K 9 := by simpa only [add_comm] using h
  exact no_five_five R (even_divisor_splits (R.units 2 (by decide) (by decide))
    (R.modeEven 4 (by decide) (by decide))
    (show reflect K (C a*L K 8) = C a*L K 8 by simp [R.modeEven 8 (by decide) (by decide)])
    (R.modeOdd 9 (by decide) (by decide)) h').2

private theorem forbid_pair_I (R : PaidLegendre28 I) (h1 : (6432:K)/1446445=0)
    (h2 : (33603:K)/187187=0) : False := by
  have a := (div_eq_zero_iff.mp h1).resolve_right (paid_divisor_ne R 1446445 (by decide +kernel))
  have b := (div_eq_zero_iff.mp h2).resolve_right (paid_divisor_ne R 187187 (by decide +kernel))
  have h : (3004:K)*6432+(-575:K)*33603=3 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z:K)) row9i_bezout
  rw [a,b,mul_zero,mul_zero,zero_add] at h
  exact R.units 3 (by decide) (by decide) h.symm

private theorem forbid_pair_II (R : PaidLegendre28 I) (h1 : (-796:K)/2223=0)
    (h2 : (77192:K)/440895=0) : False := by
  have a := (div_eq_zero_iff.mp h1).resolve_right (paid_divisor_ne R 2223 (by decide +kernel))
  have b := (div_eq_zero_iff.mp h2).resolve_right (paid_divisor_ne R 440895 (by decide +kernel))
  have h : (-3879:K)*(-796)+(-40:K)*77192=4 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z:K)) row9ii_bezout
  rw [a,b,mul_zero,mul_zero,zero_add] at h
  exact R.units 4 (by decide) (by decide) h.symm

/-- `1,4,5*`: two independent coefficient tests; a single one could
leave an erroneous characteristic-67 exception. -/
theorem no_one_four_five (R : PaidLegendre28 I) {P : K[X]} (pm : P.Monic)
    (pd : P.natDegree=4) {a : K} (ha : a≠0)
    (p5 : P∣L K 5+C a*L K 4) (p9 : P∣L K 9) : False := by
  let U := T K 6 4
  let V := T K 7 3
  let t := beta K 5/a
  have d9 : P∣U*L K 5-C (beta K 5)*V*L K 4 := R.step95 ▸ p9
  have d : P∣U+C t*V := reduce_scaled_mix R.cop54 ha p5 d9
  have du : U.natDegree=4 := R.tailDegree 6 4 (by decide) (by decide) (by decide)
  have dv : V.natDegree=3 := R.tailDegree 7 3 (by decide) (by decide) (by decide)
  have tm := monic_mix (R.tailMonic 6 4 (by decide) (by decide) (by decide))
    (B := V) (by rw [du,dv] <;> decide) t
  have eqP : U+C t*V=P := eq_of_monic_of_dvd_of_natDegree_le pm tm.1 d
    (by rw [tm.2,du,pd] <;> decide)
  have fm := monic_mix (R.modeMonic 5 (by decide)) (B := L K 4)
    (by rw [R.modeDegree 5 (by decide),R.modeDegree 4 (by decide)] <;> decide) a
  obtain ⟨v,q⟩ := linear_quotient pm pd fm.1 (fm.2.trans (R.modeDegree 5 (by decide))) p5
  rw [←eqP] at q
  let E := C t*(X*V)+C v*U
  let O := X*U+C (v*t)*V
  have eU : reflect K U=U := R.tailEven 6 4 (by decide) (by decide) (by decide) (by decide)
  have oV : reflect K V=-V := R.tailOdd 7 3 (by decide) (by decide) (by decide) (by decide)
  have sum : E+O=C a*L K 4+L K 5 := by
    calc
      _ = (X+C v)*(U+C t*V) := by dsimp only [E,O]; rw [map_mul]; ring
      _ = _ := q.symm.trans (add_comm _ _)
  have split := split_even_odd_eq (R.units 2 (by decide) (by decide))
    (show reflect K E=E by simp [E,eU,oV])
    (show reflect K O=-O by simp [O,eU,oV] <;> ac_rfl)
    (show reflect K (C a*L K 4)=C a*L K 4 by simp [R.modeEven 4 (by decide) (by decide)])
    (R.modeOdd 5 (by decide) (by decide)) sum
  have leadU : U.coeff 4=1 := tail_lead R 6 4 (by decide) (by decide) (by decide)
  have leadV : V.coeff 3=1 := tail_lead R 7 3 (by decide) (by decide) (by decide)
  have lead4 := mode_lead R 4 (by decide)
  have ev := congrArg (fun F : K[X] => F.coeff 4) split.1
  have ao : t+v=a := by
    simpa only [E,coeff_add,coeff_C_mul,coeff_X_mul V 3,leadU,leadV,lead4,mul_one] using ev
  have ko : U.coeff 2+v*t=(L K 5).coeff 3 := by
    simpa only [O,coeff_add,coeff_X_mul U 2,coeff_C_mul,leadV,mul_one] using
      congrArg (fun F : K[X] => F.coeff 3) split.2
  have ci : U.coeff 2-(L K 5).coeff 3=deltaI K := by
    simpa only [U,coeff_sub,coeff_X_mul] using R.cubicI
  have hv : v*t=-deltaI K := by linear_combination ko - ci
  have hb : a*t=beta K 5 := mul_div_cancel₀ _ ha
  have ht : t*t=deltaI K+beta K 5 := by linear_combination t*ao - hv + hb
  have oz : X*U-C (deltaI K)*V-L K 5=0 := by
    have h := split.2
    change X*U+C (v*t)*V=L K 5 at h
    rw [hv,map_neg] at h
    linear_combination h
  have e1 : C (t*t)*(X*V)+C (v*t)*U=C (a*t)*L K 4 := by
    have h := split.1
    change C t*(X*V)+C v*U=C a*L K 4 at h
    simp only [map_mul]
    linear_combination C t*h
  rw [ht,hv,hb,map_neg] at e1
  have ez : C (deltaI K+beta K 5)*(X*V)-C (deltaI K)*U-C (beta K 5)*L K 4=0 := by
    linear_combination e1
  have co := coeff_zero_of_zero oz 1
  have ce := coeff_zero_of_zero ez 2
  change (X*T K 6 4-C (deltaI K)*T K 7 3-L K 5).coeff 1=0 at co
  change (C (deltaI K+beta K 5)*(X*T K 7 3)-C (deltaI K)*T K 6 4-C (beta K 5)*L K 4).coeff 2=0 at ce
  rw [R.oddI] at co
  rw [R.evenI] at ce
  exact forbid_pair_I R co ce

/-- `1,5,≥4*`: use the paid two-mode band at the terminal rise. -/
theorem no_one_five_rise (R : PaidLegendre28 I) {P : K[X]} (pm : P.Monic)
    (pd : P.natDegree=4) (a : K) (p5 : P∣L K 5) (p10 : P∣L K 10+C a*L K 9) : False := by
  let V3 := T K 7 3
  let V4 := T K 7 4
  have z := dvd_sub (p5.mul_left (T K 6 5+C a*T K 6 4)) p10
  have ez : (T K 6 5+C a*T K 6 4)*L K 5-(L K 10+C a*L K 9) =
      (C (beta K 5)*(V4+C a*V3))*L K 4 := by
    rw [R.step105,R.step95]; dsimp only [V4,V3]; ring
  rw [ez] at z
  have cp := R.cop54.of_isCoprime_of_dvd_left p5
  have dvd : P∣V4+C a*V3 := cancel_C_dvd (beta_ne R 5 (by decide) (by decide))
    (cp.dvd_of_dvd_mul_right z)
  have d4 : V4.natDegree=4 := R.tailDegree 7 4 (by decide) (by decide) (by decide)
  have d3 : V3.natDegree=3 := R.tailDegree 7 3 (by decide) (by decide) (by decide)
  have m := monic_mix (R.tailMonic 7 4 (by decide) (by decide) (by decide))
    (B := V3) (by rw [d3,d4] <;> decide) a
  have eqP : V4+C a*V3=P := eq_of_monic_of_dvd_of_natDegree_le pm m.1 dvd
    (by rw [m.2,d4,pd] <;> decide)
  obtain ⟨v,q⟩ := linear_quotient pm pd (R.modeMonic 5 (by decide)) (R.modeDegree 5 (by decide)) p5
  rw [←eqP] at q
  let E := C a*(X*V3)+C v*V4
  let O := X*V4+C (v*a)*V3
  have e4 : reflect K V4=V4 := R.tailEven 7 4 (by decide) (by decide) (by decide) (by decide)
  have o3 : reflect K V3=-V3 := R.tailOdd 7 3 (by decide) (by decide) (by decide) (by decide)
  have sum : E+O=0+L K 5 := by
    calc
      _ = (X+C v)*(V4+C a*V3) := by dsimp only [E,O]; rw [map_mul]; ring
      _ = _ := by rw [←q,zero_add]
  have evenZero := (split_even_odd_eq (R.units 2 (by decide) (by decide))
    (show reflect K E=E by simp [E,e4,o3])
    (show reflect K O=-O by simp [O,e4,o3] <;> ac_rfl) (map_zero _) (R.modeOdd 5 (by decide) (by decide)) sum).1
  have leadV3 : V3.coeff 3=1 := tail_lead R 7 3 (by decide) (by decide) (by decide)
  have leadV4 : V4.coeff 4=1 := tail_lead R 7 4 (by decide) (by decide) (by decide)
  have av : a+v=0 := by
    simpa only [E,coeff_add,coeff_C_mul,coeff_X_mul V3 3,leadV3,leadV4,mul_one,coeff_zero] using
      coeff_zero_of_zero evenZero 4
  have hv : v=-a := by linear_combination av
  by_cases a0 : a=0
  · have l5 : L K 5=X*V4 := by simpa [hv,a0] using q
    have zero : L K 5-X*V4=0 := sub_eq_zero.mpr l5
    have c3 := coeff_zero_of_zero zero 3
    have c1 := coeff_zero_of_zero zero 1
    change (L K 5-X*T K 7 4).coeff 3=0 at c3
    change (L K 5-X*T K 7 4).coeff 1=0 at c1
    rw [R.cubicII] at c3
    rw [R.linearII] at c1
    exact forbid_pair_II R c3 c1
  · have h : C a*(X*V3-V4)=0 := by
      have h := evenZero
      change C a*(X*V3)+C v*V4=0 at h
      rw [hv,map_neg] at h
      linear_combination h
    have eq : X*V3=V4 := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (C_ne_zero.mpr a0))
    have recurrence : V4=X*V3-C (beta K 9)*T K 7 2 := R.tail74
    have z : C (beta K 9)*T K 7 2=0 := by linear_combination recurrence + eq
    exact (mul_ne_zero (C_ne_zero.mpr (beta_ne R 9 (by decide) (by decide)))
      (R.tailMonic 7 2 (by decide) (by decide) (by decide)).ne_zero) z

/-- `4,1,5*`: quotient by the same initial mixed quartic. -/
theorem no_four_one_five (R : PaidLegendre28 I) {a : K} (a0 : a≠0)
    (h : L K 4+C a*L K 3 ∣ L K 9) : False := by
  let P := L K 4+C a*L K 3
  let U := T K 5 5
  let V := T K 6 4
  let t := beta K 4/a
  have mp := monic_mix (R.modeMonic 4 (by decide)) (B := L K 3)
    (by rw [R.modeDegree 4 (by decide),R.modeDegree 3 (by decide)] <;> decide) a
  have pdeg : P.natDegree=4 := mp.2.trans (R.modeDegree 4 (by decide))
  have d9 : P∣U*L K 4-C (beta K 4)*V*L K 3 := R.step94 ▸ h
  have d : P∣U+C t*V := reduce_scaled_mix R.cop43 a0 (dvd_refl P) d9
  have du : U.natDegree=5 := R.tailDegree 5 5 (by decide) (by decide) (by decide)
  have dv : V.natDegree=4 := R.tailDegree 6 4 (by decide) (by decide) (by decide)
  have monicT := monic_mix (R.tailMonic 5 5 (by decide) (by decide) (by decide))
    (B := V) (by rw [du,dv] <;> decide) t
  obtain ⟨v,q⟩ := linear_quotient (P := P) mp.1 pdeg monicT.1 (monicT.2.trans du) d
  let E := C a*(X*L K 3)+C v*L K 4
  let O := X*L K 4+C (v*a)*L K 3
  have sum : C t*V+U=E+O := by
    calc
      _ = U+C t*V := add_comm _ _
      _ = (X+C v)*P := q
      _ = _ := by dsimp only [P,E,O]; rw [map_mul]; ring
  have o3 := R.modeOdd 3 (by decide) (by decide)
  have e4 := R.modeEven 4 (by decide) (by decide)
  have odd := (split_even_odd_eq (R.units 2 (by decide) (by decide))
    (show reflect K (C t*V)=C t*V by simp [V,R.tailEven 6 4 (by decide) (by decide) (by decide) (by decide)])
    (R.tailOdd 5 5 (by decide) (by decide) (by decide) (by decide))
    (show reflect K E=E by simp [E,o3,e4]) (show reflect K O=-O by simp [O,o3,e4] <;> ac_rfl) sum).2
  have lead3 := mode_lead R 3 (by decide)
  have ec : U.coeff 3=(L K 4).coeff 2+v*a := by
    simpa only [O,coeff_add,coeff_X_mul (L K 4) 2,coeff_C_mul,lead3,mul_one] using
      congrArg (fun F : K[X] => F.coeff 3) odd
  have cd : (L K 4).coeff 2-U.coeff 3=deltaIII K := by
    simpa only [U,coeff_sub,coeff_X_mul] using R.cubicIII
  have va : v*a=-deltaIII K := by linear_combination -ec - cd
  have z : X*L K 4-C (deltaIII K)*L K 3-T K 5 5=0 := by
    change U=X*L K 4+C (v*a)*L K 3 at odd
    rw [va,map_neg] at odd
    change X*L K 4-C (deltaIII K)*L K 3-U=0
    linear_combination -odd
  exact fatal_neg_frac (a := 96) (d := 6545) R (by decide +kernel) (by decide +kernel) R.linearIII z

/-- `5,1,≥4*`: separate the pure terminal term by reflection without
assuming anything about a masked residual after the paid frontier. -/
theorem no_five_one_rise (R : PaidLegendre28 I) (a : K)
    (h : L K 4 ∣ L K 10+C a*L K 9) : False := by
  have d10 : L K 4∣L K 10 := (even_divisor_splits (R.units 2 (by decide) (by decide))
    (R.modeEven 4 (by decide) (by decide)) (R.modeEven 10 (by decide) (by decide))
    (show reflect K (C a*L K 9)=-(C a*L K 9) by simp [R.modeOdd 9 (by decide) (by decide)]) h).1
  rw [R.step104] at d10
  have d : L K 4∣T K 6 5 := reduce_pure R.cop43 (beta_ne R 4 (by decide) (by decide)) (dvd_refl _) d10
  obtain ⟨v,q⟩ := linear_quotient (R.modeMonic 4 (by decide)) (R.modeDegree 4 (by decide))
    (R.tailMonic 6 5 (by decide) (by decide) (by decide))
    (R.tailDegree 6 5 (by decide) (by decide) (by decide)) d
  have e4 := R.modeEven 4 (by decide) (by decide)
  have sum : 0+T K 6 5=C v*L K 4+X*L K 4 := by
    rw [zero_add,q,add_mul]; exact add_comm _ _
  have eq := (split_even_odd_eq (R.units 2 (by decide) (by decide)) (map_zero _)
    (R.tailOdd 6 5 (by decide) (by decide) (by decide) (by decide))
    (show reflect K (C v*L K 4)=C v*L K 4 by simp [e4])
    (show reflect K (X*L K 4)=-(X*L K 4) by simp [e4]) sum).2
  exact fatal_neg_frac (a := 216) (d := 1463) R (by decide +kernel) (by decide +kernel) R.cubicIV (sub_eq_zero.mpr eq)

end
end RKResearch.Certified.Graded.HankelQuarticLegendre
