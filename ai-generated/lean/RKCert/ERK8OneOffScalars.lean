module

public import RKCert.ReviewedNative.ERKOrderEightLobattoScalar

public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! SOURCE CANDIDATE. Standalone scalar helpers. Their proofs use no
order-nine tableau hypotheses, and none is the numerical width-ten theorem. -/
namespace RKResearch.Certified.Graded.OneOff.Eight

open Polynomial
open scoped BigOperators Classical

variable {K : Type*} [Field K] [CharZero K]

/-- Same explicit cubic, from the admitted p8 scalar object. -/
noncomputable abbrev lobattoCubic : K[X] := LobattoEight.lobattoCubic

/-! The seven order-independent scalar definitions/identities are
public donor slices in this new, independent namespace. -/
def hzero (d x : K) : K := x^2*(x-2*d)/(4*d)
def m1 (x H : K) : K := x^2/2+2*H
def m2 (d x H : K) : K := x^3/3+(4*d/3)*H
def m3 (d x H : K) : K := x^4/4+(2*d^2-d*x)*H

def jValue (d z x H : K) : K :=
  2*d*(d-x)*H + ((z-d)*m3 d x H-d*(3*z-2*d)*m2 d x H+2*d^2*z*m1 x H)/(4*d)

def vValue (d z x H : K) : K :=
  (3*d+z)*m3 d x H-(2*d^2+3*d*z)*m2 d x H+2*d^2*z*m1 x H-x^5/5

theorem j_value_doubled (d z H : K) (dn : d≠0) :
    jValue d z (2*d) H=d^4/3-(4*d^2/3)*H := by
  unfold jValue m1 m2 m3
  field_simp [dn]
  ring

omit [CharZero K] in
theorem common_clock_affine_parameters {u v J slope P Q : K}
    (diff : v≠u) (a0 : J+u*slope=P+u*Q) (a1 : J+v*slope=P+v*Q) :
    P=J ∧ Q=slope := by
  have sq : Q=slope := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr diff)
    linear_combination a0-a1
  rw [sq] at a0
  exact ⟨(add_right_cancel a0).symm,sq⟩

theorem lobatto_eval_factor (x : K) :
    (lobattoCubic : K[X]).eval x = (x-1/2)*(x^2-x+1/7) := by
  simp only [lobattoCubic,LobattoEight.lobattoCubic,eval_add,eval_monomial]
  ring

theorem lobatto_at_one : (lobattoCubic : K[X]).eval 1 = 1/14 := by
  rw [lobatto_eval_factor]
  norm_num

theorem lobatto_no_doubled_root {d : K}
    (hD : (lobattoCubic : K[X]).eval (2*d)=0) :
    (lobattoCubic : K[X]).eval d≠0 := by
  intro hd
  by_cases half : d=1/2
  · rw [half,lobatto_eval_factor] at hD
    norm_num at hD
  by_cases Dhalf : 2*d=1/2
  · have quarter : d=1/4 := by linear_combination (1/2:K)*Dhalf
    rw [quarter,lobatto_eval_factor] at hd
    norm_num at hd
  rw [lobatto_eval_factor] at hd hD
  have q1 := (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr half)
  have q2 := (mul_eq_zero.mp hD).resolve_left (sub_ne_zero.mpr Dhalf)
  have e : d=3/14 := by linear_combination (1/2:K)*q2-2*q1
  rw [e] at q1
  norm_num at q1

/-- Directly reuse the admitted p8 cubic proof, not the p9 quartic
decoder. It consumes the same three paid rows of four coefficients. -/
theorem beta_cubic_decoder (Q : K[X]) (hd : Q.natDegree≤3)
    (hm : ∀ k : Fin 3,
      (∑ j : Fin 4, Q.coeff j.val / ((k.val+j.val+3:ℕ):K)) -
      (∑ j : Fin 4, Q.coeff j.val / ((k.val+j.val+2:ℕ):K)) = 0) :
    Q = C (Q.coeff 3)*lobattoCubic :=
  LobattoEight.lobatto_cubic_decoder Q hd hm

theorem beta_quadratic_zero (Q : K[X]) (hd : Q.natDegree≤2)
    (hm : ∀ k : Fin 3,
      (∑ j : Fin 3, Q.coeff j.val / ((k.val+j.val+3:ℕ):K)) -
      (∑ j : Fin 3, Q.coeff j.val / ((k.val+j.val+2:ℕ):K)) = 0) :
    Q=0 := by
  have zz : Q.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have extended (k : Fin 3) :
      (∑ j : Fin 4, Q.coeff j.val / ((k.val+j.val+3:ℕ):K)) -
      (∑ j : Fin 4, Q.coeff j.val / ((k.val+j.val+2:ℕ):K)) = 0 := by
    rw [Fin.sum_univ_castSucc (fun j : Fin 4 => Q.coeff j.val / ((k.val+j.val+3:ℕ):K)),
        Fin.sum_univ_castSucc (fun j : Fin 4 => Q.coeff j.val / ((k.val+j.val+2:ℕ):K))]
    simpa only [Fin.val_castSucc,Fin.val_last,zz,zero_div,add_zero] using hm k
  have e := beta_cubic_decoder Q (by omega) extended
  simpa only [zz,map_zero,zero_mul] using e

/-- The exact scalar discriminant for the seventh physical receiver;
no Radau value, no wide p9 coefficient formula, and no extra knot. -/
theorem masterCombination (d z x U : K) (dn : d≠0) :
    vValue d z x U-(4*d/5)*jValue d z x U + (4*d/5)*(x^2-2*d^2)*U =
      (x-2*d)*(x-z)*(4*d*U-x^2*(x-2*d))/5 := by
  unfold jValue vValue m1 m2 m3
  field_simp [dn] <;> ring

end RKResearch.Certified.Graded.OneOff.Eight
