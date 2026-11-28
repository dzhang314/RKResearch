module

public import RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixLateGhostScalar
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Two chronology gates for the no-late invisible six-ghost phase -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixNoLate

open Polynomial OrderElevenInvisibleSixLateGhost

variable {K : Type*} [Field K] [CharZero K]

/-- The two cubic-labelled donor taps cannot be paid at the first
nonzero clean stage by one or two preceding dirty rows. An absent
donor may be represented by a zero tap and a distinct dummy clock. -/
theorem two_ghost_forward_impossible (x p q l r d g h : K)
    (x0 : x≠0) (pg : g≠0) (qh : h≠0) (pq : p≠q)
    (m0 : l*g+r*h=0) (m1 : l*p*g+r*q*h=0)
    (h1 : l*p+r*q+d*x=x^2/2) (h2 : l*p^2+r*q^2+d*x^2=x^3/3) : False := by
  have e : (p-q)*(l*g)=0 := by linear_combination m1-q*m0
  have lz : l=0 := (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr pq))).resolve_right pg
  have e' : r*h=0 := by linear_combination m0-g*lz
  have rz : r=0 := (mul_eq_zero.mp e').resolve_right qh
  have pow : x^3=0 := by
    rw [lz,rz] at h1 h2
    linear_combination 6*(h2-x*h1)
  exact (pow_ne_zero 3 x0) pow

/-- The two inclusive primitive ratios at the old ordinary stages
cannot coincide, including when one primitive value is zero. -/
theorem nodal_ratio_determinant (u v : K) :
    IXP u v v*IP u v u-IXP u v u*IP u v v=u^3*v^3*(u-v)^3/120 := by
  unfold IXP IP
  ring

/-- The low paid primitive multipliers at the first two clean
donors cannot have proportionality at all three distinct ghosts
in the next gap. Only the old *weights* are canceled, not their
cubic marks or primitive values. -/
theorem no_three_ghosts_next_gap (u v w fu fv : K)
    (u0 : u≠0) (v0 : v≠0) (uv : u≠v)
    (P Q : K[X]) (dP : P.natDegree≤1) (dQ : Q.natDegree≤2)
    (hu : P.eval u*fu=IP u v u) (hv : P.eval v*fv=IP u v v)
    (ju : Q.eval u*fu=IXP u v u) (jv : Q.eval v*fv=IXP u v v)
    (ghosts : Fin 3 → K) (distinct : Function.Injective ghosts)
    (hg : ∀ i, Q.eval (ghosts i)=w*P.eval (ghosts i)) : False := by
  let H := Q-C w*P
  have degM : (C w*P).natDegree ≤ 2 := by
    have h := natDegree_mul_le (p:=C w) (q:=P)
    rw [natDegree_C] at h
    omega
  have deg : H.natDegree≤2 := natDegree_sub_le_of_le dQ degM
  have ev i : H.eval (ghosts i)=0 := by
    simp [H,hg i]
  have Hz := eq_zero_of_natDegree_lt_card_of_eval_eq_zero H distinct ev (by
    rw [Fintype.card_fin]
    omega)
  have eq (s : K) : Q.eval s=w*P.eval s := by
    have E := congrArg (fun R : K[X] => R.eval s) Hz
    simpa only [H,eval_sub,eval_mul,eval_C,eval_zero,sub_eq_zero] using E
  rw [eq u,mul_assoc,hu] at ju
  rw [eq v,mul_assoc,hv] at jv
  have h := nodal_ratio_determinant u v
  rw [←ju,←jv] at h
  have hvv : u^3*v^3*(u-v)^3/120=0 := by linear_combination -h
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ u0)
    (pow_ne_zero _ v0)) (pow_ne_zero _ (sub_ne_zero.mpr uv))) (by norm_num)) hvv

/-- If both actual paid transpose marks vanish at the third regular
and no ghost intervenes, the two prior regular taps vanish. The
literal first positive moment then contradicts a zero cubic there. -/
theorem third_clean_mark_live (u v w l r d k1 k2 : K)
    (uv : u≠v) (w0 : w≠0) (k1z : k1≠0) (k2z : k2≠0)
    (m0 : l*k1+r*k2=0) (m1 : u*l*k1+v*r*k2=0)
    (h1 : l*u+r*v+d*w=w^2/2) (h2 : l*u^2+r*v^2+d*w^2=w^3/3) : False := by
  apply two_ghost_forward_impossible w u v l r d k1 k2 w0 k1z k2z uv m0 ?_ h1 h2
  linear_combination m1

end RKResearch.Certified.Graded.OrderElevenInvisibleSixNoLate
