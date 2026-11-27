module

public import RKCert.ReviewedNative.ERK8PaidLobatto

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid terminal decoder and closing gate for the ERK8 one-off branch

These terminal adapters remove the characteristic-zero requirement from
the last part of the accepted one-off argument. They do not assume an
ordered field. The actual paid forward chart and grade-five chronological
argument remain separate from this module. -/
namespace RKResearch.Certified.Graded.OneOff.EightPaid

open RKResearch Polynomial ERK8PaidField ERKTaggedHorizon LobattoEight
open scoped Matrix Classical

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem lobatto_eval_cleared (ho : HasOrder 8 A b) (u : K) :
    14*(lobattoCubic : K[X]).eval u=(2*u-1)*(7*u^2-7*u+1) := by
  have e₀ := div_mul_cancel₀ (-1:K) (fourteen_ne ho)
  have e₁ := div_mul_cancel₀ (9:K) (fourteen_ne ho)
  have e₂ := div_mul_cancel₀ (-3:K) (ERK8PaidField.two_ne ho)
  simp only [lobattoCubic,eval_add,eval_monomial,pow_zero,pow_one,mul_one,one_mul]
  linear_combination e₀+u*e₁+7*u^2*e₂

/-- The interior cubic never has a root at both d and 2d in a paid field. -/
theorem lobatto_no_doubled_root_paid (ho : HasOrder 8 A b) {d : K}
    (hd : (lobattoCubic : K[X]).eval d=0)
    (hD : (lobattoCubic : K[X]).eval (2*d)=0) : False := by
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have n7 : (7:K)≠0 := (ho.natCast_isUnit (n:=7) (by decide) (by decide)).ne_zero
  have e := lobatto_eval_cleared ho d
  have f := lobatto_eval_cleared ho (2*d)
  rw [hd,mul_zero] at e
  rw [hD,mul_zero] at f
  rcases mul_eq_zero.mp e.symm with a|a <;> rcases mul_eq_zero.mp f.symm with z|z
  · exact one_ne_zero (by linear_combination z-2*a : (1:K)=0)
  · have one := sub_eq_zero.mp a
    simp [one] at z
  · apply n5
    linear_combination (28*d-21)*z-16*a
  · have n35 : (5:K)*7≠0 := mul_ne_zero n5 n7
    apply n35
    have q : 14*d-3=0 := by linear_combination z-4*a
    linear_combination (98*d-77)*q-196*a

private theorem shift_probe_paid
    (A : Matrix (Fin s) (Fin s) K) (b v : Fin s → K) (k : ℕ) :
    probe A b k (diag (nodes A) v)=probe A b (k+1) v := by
  simp only [probe,row_apply,dotProduct,diag_apply,pow_succ]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Four equal order-eight probes pin the degree-four pure part of the
terminal coordinate, over all paid fields. -/
theorem terminal_polynomial_paid (ho : HasOrder 8 A b) {P : K[X]} (deg : P.natDegree≤4)
    (p0 : P.eval 0=0) (p1 : P.eval 1=1) (w : K)
    (paid : ∀ k : Fin 4, probe A b k.val (evalNodes A P)=w) :
    P=X*(C (14:K)*lobattoCubic) := by
  obtain ⟨B,e⟩ := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero P).trans p0)
  have h1 : B.eval 1=1 := by simpa only [e,eval_mul,eval_X,one_mul] using p1
  have non : B≠0 := by
    intro h
    rw [h,eval_zero] at h1
    exact zero_ne_one h1
  have bd : B.natDegree≤3 := by
    have d := natDegree_mul X_ne_zero non
    rw [←e,natDegree_X] at d
    omega
  have glue :
      evalNodes A ((X^2-X)*B)=diag (nodes A) (evalNodes A P)-evalNodes A P := by
    ext j
    simp only [evalNodes_apply,diag_apply,Pi.sub_apply,e,eval_mul,eval_sub,eval_pow,eval_X]
    ring
  have test (k : Fin 3) : probe A b k.val (evalNodes A ((X^2-X)*B))=0 := by
    have pk1 := paid k.succ
    have pk0 := paid k.castSucc
    change probe A b (k.val+1) (evalNodes A P)=w at pk1
    change probe A b k.val (evalNodes A P)=w at pk0
    rw [glue,map_sub,shift_probe_paid,pk1,pk0,sub_self]
  have Bshape := beta_cubic_from_probes_paid ho B bd test
  have u := congrArg (fun Q : K[X] => Q.eval 1) Bshape
  rw [h1,eval_mul,eval_C] at u
  have v : 14*(lobattoCubic : K[X]).eval 1=1 := calc
    _ = (2*(1:K)-1)*(7*(1:K)^2-7*1+1) := lobatto_eval_cleared ho (1:K)
    _ = _ := by ring
  have coef : B.coeff 3=14 := by linear_combination -14*u-B.coeff 3*v
  exact e.trans (congrArg (fun Q : K[X] => X*Q) (by simpa only [coef] using Bshape))

private theorem two_zero_affine {R L a b : K} (ab : a≠b)
    (h₁ : R+a*L=0) (h₂ : R+b*L=0) : R=0 ∧ L=0 := by
  have e : (a-b)*L=0 := by linear_combination h₁-h₂
  have z := (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr ab)
  exact ⟨by simpa [z] using h₁,z⟩

/-- Once two distinct actual clean pairs have different scaled defect
values within each pair, the terminal coefficient of the defect is
zero. Its two incompatible Lobatto roots then close the paid branch. -/
theorem repeated_clean_terminal_paid (ho : HasOrder 8 A b)
    {P Q : K[X]} (Qd : Q.natDegree≤1) (shape : P=X*(C (14:K)*lobattoCubic))
    {d z H₁ H₂ U₁ U₂ V : K}
    (dn : d≠0) (zd : z≠2*d) (Hne : H₁≠H₂) (Une : U₁≠U₂)
    (D₁ : P.eval (2*d)+H₁*Q.eval (2*d)=0) (D₂ : P.eval (2*d)+H₂*Q.eval (2*d)=0)
    (Z₁ : P.eval z+U₁*Q.eval z=0) (Z₂ : P.eval z+U₂*Q.eval z=0)
    (D₀ : P.eval d+V*Q.eval d=0) : False := by
  have ⟨pd,qd⟩ := two_zero_affine Hne D₁ D₂
  have ⟨_,qz⟩ := two_zero_affine Une Z₁ Z₂
  have Q0 : Q=0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ ({z, 2*d} : Finset K) ?_ ?_
    · intro y h
      simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h|h
      · simpa [h] using qz
      · simpa [h] using qd
    · simpa [Finset.card_insert_of_notMem,zd] using (show Q.natDegree<2 by omega)
  have ps : P.eval d=0 := by simpa [Q0] using D₀
  rw [shape,eval_mul,eval_mul,eval_X,eval_C] at pd ps
  have n14 := fourteen_ne ho
  have Dn := mul_ne_zero (ERK8PaidField.two_ne ho) dn
  have rd := (mul_eq_zero.mp ((mul_eq_zero.mp ps).resolve_left dn)).resolve_left n14
  have rD := (mul_eq_zero.mp ((mul_eq_zero.mp pd).resolve_left Dn)).resolve_left n14
  exact lobatto_no_doubled_root_paid ho rd rD

end RKResearch.Certified.Graded.OneOff.EightPaid

#print axioms RKResearch.Certified.Graded.OneOff.EightPaid.terminal_polynomial_paid
#print axioms RKResearch.Certified.Graded.OneOff.EightPaid.repeated_clean_terminal_paid
