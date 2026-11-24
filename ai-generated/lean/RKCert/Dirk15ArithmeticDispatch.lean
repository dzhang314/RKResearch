module

public import RKCert.Dirk15ArithmeticSpecialize
public import RKCert.Dirk15ReplayInterface
public import RKCert.Dirk15ScalarBase

@[expose] public section

/-! # Reduce unrestricted order 15 to the checked package of finite replays

The sole premise not about the genuinely lower tableau is an explicit
degree-preserving modular coprimality package for five finite lists of
fixed integer polynomials. No theorem here assumes a particular free
parameter, squarefree coefficient polynomial, or real embedding. -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Paired RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem pencil_root {D : K[X]} {n : ℕ} {a t u : K} (a0 : a≠0)
    (e : D=C a*(X*fieldPencil K n t)) (u0 : u≠0) (root : D.eval u=0) :
    (fieldPencil K n t).eval u=0 := by
  rw [e,eval_mul,eval_C,eval_mul,eval_X] at root
  exact (mul_eq_zero.mp ((mul_eq_zero.mp root).resolve_left a0)).resolve_left u0

omit [CharZero K] in
private theorem reflected_root {n : ℕ} {a y : K} (p : (fieldPencil K n a).eval (1-y)=0) :
    (fieldPencil K n (-a)).eval y=0 := by
  have r := congrArg (eval y) (fieldJacobi_pencil_reflect n a)
  rw [reflectPolynomial_eval_exact,p,eval_mul,eval_C] at r
  exact (mul_eq_zero.mp r.symm).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

omit [CharZero K] in
private theorem reflect_ne {V : K[X]} (V0 : V≠0) : reflectPolynomial V≠0 := by
  intro z
  apply V0
  have t := reflectPolynomial_involutive V
  rwa [z,reflectPolynomial,zero_comp,eq_comm] at t

private theorem no_node_moment_pair {n k j w : ℕ} (hn : 0<n) (hk : 0<k) (den : j+k+w+2≤10)
    (cert : Order15GoodPrimePair (nodeMomentNorm n k j w) (nodeMomentNorm n k (j+1) w)
      (momentCap n k w) (momentCap n k w))
    {t u : K} (u0 : u≠0) {V : K[X]} (vk : V.natDegree=k) (VU : V.eval u≠0)
    (root : (fieldPencil K n t).eval u=0) (vd : V∣fieldPencil K n t)
    (p : paidMoment ((1-X)^w*V) u j=0) (q : paidMoment ((1-X)^w*V) u (j+1)=0) :
    False := cert.no_common
      (nodeMomentNorm_degree hn hk _ _) (nodeMomentNorm_degree hn hk _ _) u
      (nodeMomentNorm_zero hn (by omega) u0 vk root vd VU p)
      (nodeMomentNorm_zero hn (by omega) u0 vk root vd VU q)

set_option maxHeartbeats 950000 in
theorem Order15FiniteReplay.forward (Ck : Order15FiniteReplay)
    {D : K[X]} (shape : Order15PencilShape D) {T : K[X]} (T0 : T≠0)
    (dT : T.natDegree≤4) (Tdiv : T∣D) {u : K} (u0 : u≠0) (root : D.eval u=0)
    (omitU : T.eval u≠0) (one : paidMoment T u 1=0) (two : paidMoment T u 2=0) : False := by
  obtain ⟨n,ns,a,t,a0,de⟩ := integer_pencil_shape shape
  have n0 : 0<n := by omega
  have vdiv : T∣X*fieldPencil K n t := cancel_nonzero_constant_factor a0 (de ▸ Tdiv)
  obtain ⟨e,e1,V,V0,T_eq,Vdiv,_⟩ := factor_remove_one_endpoint T0 vdiv
  let k := V.natDegree
  have bound : k+e≤4 := by have d := factor_degree_one_endpoint V0 e T_eq; omega
  have root := pencil_root a0 de u0 root
  have vU := factor_omit_eval e T_eq omitU
  rw [T_eq,paidMoment_remove_origin] at one two
  have h1 : paidMoment ((1-X)^0*V) u (1+e)=0 := by simpa only [pow_zero,one_mul] using one
  have h2 : paidMoment ((1-X)^0*V) u (1+e+1)=0 := by
    simpa only [pow_zero,one_mul,show 1+e+1=2+e by omega] using two
  by_cases k0 : k=0
  · exact no_weighted_constant_moments V0 k0 u0 (1+e) 0 (by decide) h1 h2
  · exact no_node_moment_pair n0 (Nat.pos_of_ne_zero k0) (by omega)
      (by simpa only [show 1+e+1=2+e by omega] using Ck.forwardMoments n k e ns (by omega) e1 bound)
      u0 rfl vU root Vdiv h1 h2

set_option maxHeartbeats 950000 in
theorem Order15FiniteReplay.reverse (Ck : Order15FiniteReplay)
    {D : K[X]} (shape : Order15PencilShape D) {T : K[X]} (T0 : T≠0)
    (dT : T.natDegree≤4) (Tdiv : T∣D) {y : K} (y0 : y≠0) (root : D.eval (1-y)=0)
    (omitY : T.eval (1-y)≠0) (one : paidMoment (reflectPolynomial T) y 1=0)
    (two : paidMoment (reflectPolynomial T) y 2=0) : False := by
  obtain ⟨n,ns,a,t,a0,de⟩ := integer_pencil_shape shape
  have n0 : 0<n := by omega
  have vdiv : T∣X*fieldPencil K n t := cancel_nonzero_constant_factor a0 (de ▸ Tdiv)
  obtain ⟨e,e1,V,V0,T_eq,Vdiv,endpoint⟩ := factor_remove_one_endpoint T0 vdiv
  let k := V.natDegree
  have bound : k+e≤4 := by have d := factor_degree_one_endpoint V0 e T_eq; omega
  let W := reflectPolynomial V
  have WK : W.natDegree=k := reflectPolynomial_degree_eq V
  have W0 : W≠0 := reflect_ne V0
  have Wy : W.eval y≠0 := by
    change (reflectPolynomial V).eval y≠0
    rw [reflectPolynomial_eval_exact]
    exact factor_omit_eval e T_eq omitY
  have Wdiv := factor_reflected_pencil n t Vdiv
  rw [T_eq,reflectPolynomial_endpoint] at one two
  by_cases k0 : k=0
  · exact no_weighted_constant_moments W0 (WK.trans k0) y0 1 e e1 one two
  have kp : 0<k := Nat.pos_of_ne_zero k0
  by_cases at1 : 1-y=0
  · have y1 : y=1 := (sub_eq_zero.mp at1).symm
    have e0 : e=0 := endpoint (by simpa only [at1] using omitY)
    subst y
    subst e
    have kp1 : k≤4 := by omega
    exact (Ck.fixedMoments n k ns kp kp1).no_common
      (anchorMomentNorm_degree n kp 1) (anchorMomentNorm_degree n kp 2) (-t)
      (anchorMomentNorm_zero (by omega) W0 WK Wdiv (by simpa only [pow_zero,one_mul] using one))
      (anchorMomentNorm_zero (by omega) W0 WK Wdiv (by simpa only [pow_zero,one_mul] using two))
  · have ry := reflected_root (pencil_root a0 de at1 root)
    have options : e=0∨e=1 := by omega
    rcases options with e0|eOne
    · subst e
      exact no_node_moment_pair n0 kp (by omega) (by
        simpa only [Nat.add_zero] using Ck.forwardMoments n k 0 ns kp (by decide) bound)
        y0 WK Wy ry Wdiv one two
    · subst e
      exact no_node_moment_pair n0 kp (by omega) (Ck.reflectedMoments n k ns kp (by omega))
        y0 WK Wy ry Wdiv one two

set_option maxHeartbeats 1150000 in
theorem Order15FiniteReplay.both (Ck : Order15FiniteReplay)
    {D : K[X]} (shape : Order15PencilShape D) {T : K[X]} (T0 : T≠0)
    (dT : T.natDegree≤3) (Tdiv : T∣D) {u y : K} (u0 : u≠0) (y0 : y≠0)
    (rootU : D.eval u=0) (rootY : D.eval (1-y)=0) (omitU : T.eval u≠0) (omitY : T.eval (1-y)≠0)
    (pU : paidMoment T u 1*paidMoment T u 3-(paidMoment T u 2)^2=0)
    (pY : paidMoment (reflectPolynomial T) y 1*paidMoment (reflectPolynomial T) y 3-
      (paidMoment (reflectPolynomial T) y 2)^2=0) : False := by
  obtain ⟨n,ns,a,t,a0,de⟩ := integer_pencil_shape shape
  have n0 : 0<n := by omega
  have vdiv : T∣X*fieldPencil K n t := cancel_nonzero_constant_factor a0 (de ▸ Tdiv)
  obtain ⟨e,e1,V,V0,T_eq,Vdiv,endpoint⟩ := factor_remove_one_endpoint T0 vdiv
  let k := V.natDegree
  have band : k+e≤3 := by have d := factor_degree_one_endpoint V0 e T_eq; omega
  let W := reflectPolynomial V
  have WK : W.natDegree=k := reflectPolynomial_degree_eq V
  have W0 : W≠0 := reflect_ne V0
  have Vy : W.eval y≠0 := by
    change (reflectPolynomial V).eval y≠0
    rw [reflectPolynomial_eval_exact]
    exact factor_omit_eval e T_eq omitY
  have VU := factor_omit_eval e T_eq omitU
  have Wdiv := factor_reflected_pencil n t Vdiv
  have ru := pencil_root a0 de u0 rootU
  rw [T_eq] at pU
  simp only [paidMoment_remove_origin] at pU
  have gf : paidMoment V u (1+e)*paidMoment V u (1+e+2)-
      (paidMoment V u (1+e+1))^2=0 := by
    simpa only [show 1+e+2=3+e by omega,show 1+e+1=2+e by omega] using pU
  rw [T_eq,reflectPolynomial_endpoint] at pY
  by_cases k0 : k=0
  · exact constant_gram_nonzero V0 k0 u0 (1+e) gf
  have kp : 0<k := Nat.pos_of_ne_zero k0
  have left : (parameterGramNorm n k (1+e) 0).eval₂ (Int.castRingHom K) t=0 :=
    parameterGramNorm_zero n0 kp (by omega) u0 rfl ru Vdiv VU
      (by simpa only [pow_zero,one_mul] using gf)
  by_cases at1 : 1-y=0
  · have y1 : y=1 := (sub_eq_zero.mp at1).symm
    have e0 : e=0 := endpoint (by simpa only [at1] using omitY)
    subst y
    subst e
    exact (Ck.gramFixedReverse n k ns kp (by omega)).no_common
      (parameterGramNorm_degree _ _ _ _) ((minusParameter_degree _).trans (anchorGramNorm_degree _ kp))
      t left (by
        rw [minusParameter_eval₂]
        exact anchorGramNorm_zero (by omega) W0 WK Wdiv
          (by simpa only [pow_zero,one_mul] using pY))
  · have ry := reflected_root (pencil_root a0 de at1 rootY)
    exact (Ck.gramBothRoots n k e ns kp e1 band).no_common
      (parameterGramNorm_degree _ _ _ _) ((minusParameter_degree _).trans (parameterGramNorm_degree _ _ _ _))
      t left (by
        rw [minusParameter_eval₂]
        exact parameterGramNorm_zero n0 kp (by omega) y0 WK ry Wdiv Vy pY)

theorem Order15FiniteReplay.pencilCertificates (cert : Order15FiniteReplay) :
    Order15PencilCertificates K :=
  ⟨fun _ sh _ tn td div _ u0 root omitU p1 p2 =>
      cert.forward sh tn td div u0 root omitU p1 p2,
    fun _ sh _ tn td div _ y0 root omitY p1 p2 =>
      cert.reverse sh tn td div y0 root omitY p1 p2,
    fun _ sh _ tn td div _ _ u0 y0 rootU rootY omitU omitY pU pY =>
      cert.both sh tn td div u0 y0 rootU rootY omitU omitY pU pY⟩

end
end RKCert.FixedPolynomial

namespace RKCert.Paired
open RKCert.FixedPolynomial

theorem dirk_order15_ge21_of_finite_replay {K : Type*} [Field K] [CharZero K]
    (cert : Order15FiniteReplay) {s : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) : 21≤s :=
  dirk_order15_ge21_of_pencil_certificates cert.pencilCertificates ha ho

end RKCert.Paired
