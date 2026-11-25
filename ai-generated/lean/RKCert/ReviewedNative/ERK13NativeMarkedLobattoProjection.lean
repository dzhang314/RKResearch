module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoGradeThree
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The low-delta Lobatto projection has no scalar residue

The degree-four and degree-five representatives of the three paid
endpoint differences are compared modulo the degree-six mesh by an
integral recurrence and one Bézout identity. No splitting, order on the
field, or stage hypotheses are needed. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open Polynomial MarkedAdjacent
open scoped Classical BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {P Q : K[X]}
set_option maxHeartbeats 1700000

private def little3 (K : Type*) [Field K] : K[X] := 14*X^3-21*X^2+9*X-1
private def little4 (K : Type*) [Field K] : K[X] := 42*X^4-84*X^3+56*X^2-14*X+1
private def little5 (K : Type*) [Field K] : K[X] := 132*X^5-330*X^4+300*X^3-120*X^2+20*X-1
private def data3 (K : Type*) [Field K] : Fin 5→K := ![0,-1,9,-21,14]
private def data4 (K : Type*) [Field K] : Fin 6→K := ![0,1,-14,56,-84,42]

private theorem p3_form : ofFn 5 (data3 K)=X*little3 K := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  simp only [little3,ofFn_eq_sum_monomial,eval_finsetSum,eval_monomial,
    eval_mul,eval_sub,eval_add,eval_pow,eval_X,eval_one,eval_ofNat,Fin.sum_univ_succ]
  norm_num [data3] <;> ring

private theorem p4_form : ofFn 6 (data4 K)=X*little4 K := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  simp only [little4,ofFn_eq_sum_monomial,eval_finsetSum,eval_monomial,
    eval_mul,eval_sub,eval_add,eval_pow,eval_X,eval_one,eval_ofNat,Fin.sum_univ_succ]
  norm_num [data4] <;> ring

private theorem mesh_form : earlyLobattoMesh K=X*little5 K := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  rw [earlyLobattoMesh_eval,eval_mul,eval_X]
  simp only [little5, NativeLobatto.lobattoValue,eval_mul,eval_add,eval_sub,eval_pow,
    eval_X,eval_one,eval_ofNat]

private theorem d5 : (little5 K).natDegree=5 := by
  have d := earlyLobattoMesh_degree (K:=K)
  rw [mesh_form] at d
  have nz : little5 K≠0 := by intro z; rw [z,mul_zero,natDegree_zero] at d; omega
  rw [natDegree_X_mul nz] at d
  omega

private theorem d3 : (ofFn 5 (data3 K)).natDegree=4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) (data3 K)))
  rw [ofFn_coeff_eq_val_of_lt _ (by decide : 4<5)]
  norm_num [data3]

private theorem d4 : (ofFn 6 (data4 K)).natDegree=5 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) (data4 K)))
  rw [ofFn_coeff_eq_val_of_lt _ (by decide : 5<6)]
  norm_num [data4]

private theorem endpoint_ofFn {n : ℕ} (d : Fin n→K) (k : ℕ) :
    endpointMoment K k (ofFn n d)=
    (∑ i : Fin n, d i/((i.val+k+1:ℕ):K)) -
      (∑ i : Fin n, d i/((i.val+k+1+1:ℕ):K)) := by
  have unit (m : ℕ) : unitMoment K m (ofFn n d) =
      ∑ i : Fin n, d i/((i.val+m+1:ℕ):K) := by
    rw [unitMoment_apply,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one]
  change unitMoment K k (ofFn n d)-unitMoment K (k+1) (ofFn n d)=_
  rw [unit,unit]
  simp only [Nat.add_assoc]

private theorem moment3 (k : Fin 3) : endpointMoment K k.val (ofFn 5 (data3 K))=0 := by
  rw [endpoint_ofFn]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,data3]

private theorem moment4 (k : Fin 3) : endpointMoment K k.val (ofFn 6 (data4 K))=0 := by
  rw [endpoint_ofFn]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,data4]

private theorem little_recurrence :
    (4:K[X])*little3 K=(22*X-11)*little4 K-7*little5 K := by
  unfold little3 little4 little5
  ring

private theorem little_coprime : IsCoprime (little5 K) (little4 K) := by
  let A0 : K[X] := -(1470*X^3)+2205*X^2-931*X+98
  let B0 : K[X] := 4620*X^4-9240*X^3+6111*X^2-1491*X+100
  have bez : A0*little5 K+B0*little4 K=2 := by
    dsimp [A0,B0,little5,little4]
    ring
  refine ⟨C ((2:K)⁻¹)*A0,C ((2:K)⁻¹)*B0,?_⟩
  calc
    _ = C ((2:K)⁻¹)*(A0*little5 K+B0*little4 K) := by ring
    _ = 1 := by
      rw [bez,(Polynomial.C_ofNat (R:=K) 2).symm,←map_mul,
        inv_mul_cancel₀ (by norm_num : (2:K)≠0),map_one]

/-- Purely scalar: the three square moments and low complement suffice
to cancel the entire projection, even before the roots are adjoined. -/
theorem lobatto_small_square_projection_zero (pd : P.natDegree≤5) (p0 : P.eval 0=0)
    (tests : ∀ k : Fin 3, endpointMoment K k.val P=0)
    (qd : Q.natDegree≤3) (qn : Q≠0)
    (divides : earlyLobattoMesh K∣P*Q) : P=0 := by
  obtain ⟨v,dv⟩ := reduction_by_next_degree (a:=4) pd (d4 (K:=K))
  obtain ⟨u,du⟩ := reduction_by_next_degree (a:=3) dv (d3 (K:=K))
  let Z := P-v • ofFn 6 (data4 K)-u • ofFn 5 (data3 K)
  have z0 : Z.eval 0=0 := by
    simp only [Z,p3_form,p4_form,eval_sub,eval_smul,eval_mul,eval_X,p0,
      zero_mul,smul_zero,sub_zero]
  have zz : Z=0 := NativeMoments.endpoint_moments_detect du z0 (fun k=>by
    rw [←endpointMoment_apply]
    simp only [Z,map_sub,map_smul,tests k,moment3 k,moment4 k,smul_zero,sub_zero])
  let V : K[X] := C v*little4 K+C u*little3 K
  have pForm : P=X*V := by
    change P-v • ofFn 6 (data4 K)-u • ofFn 5 (data3 K)=0 at zz
    rw [p4_form,p3_form,smul_eq_C_mul,smul_eq_C_mul] at zz
    dsimp only [V]
    linear_combination zz
  obtain ⟨J,hJ⟩ := divides
  have vdiv : little5 K∣V*Q := by
    refine ⟨J,mul_left_cancel₀ (X_ne_zero : (X:K[X])≠0) ?_⟩
    rw [pForm,mesh_form] at hJ
    simpa only [mul_assoc] using hJ
  let W : K[X] := 4*C v+C u*(22*X-11)
  have blend : W*little4 K=4*V+(7*C u)*little5 K := by
    dsimp only [W,V]
    linear_combination -(C u)*little_recurrence (K:=K)
  obtain ⟨T,hT⟩ := vdiv
  have canc : little5 K∣little4 K*(W*Q) := by
    refine ⟨4*T+7*C u*Q,?_⟩
    calc
      _ = (W*little4 K)*Q := by ring
      _ = _ := by rw [blend,add_mul,mul_assoc,hT]; ring
  have wd : W.natDegree≤1 := by
    dsimp only [W]
    have e1 : ((4:K[X])*C v).natDegree≤0 :=
      natDegree_mul_le_of_le (show (4:K[X]).natDegree≤0 by simp)
        (show (C v).natDegree≤0 by simp)
    have e2 : (22*X:K[X]).natDegree≤1 :=
      natDegree_mul_le_of_le (show (22:K[X]).natDegree≤0 by simp)
        (show (X:K[X]).natDegree≤1 by simp)
    have ef : (22*X-11:K[X]).natDegree≤1 :=
      (natDegree_sub_le _ _).trans (max_le e2 (by simp))
    have v2 : (C u*(22*X-11)).natDegree≤1 :=
      natDegree_mul_le_of_le (show (C u).natDegree≤0 by simp) ef
    exact (natDegree_add_le _ _).trans (max_le (e1.trans (by decide : 0≤1)) v2)
  have w0 : W=0 := by
    by_contra wn
    have deg := natDegree_le_of_dvd (little_coprime.dvd_of_dvd_mul_left canc) (mul_ne_zero wn qn)
    rw [d5,natDegree_mul wn qn] at deg
    omega
  have at0 : W.eval 0=4*v-11*u := by
    simp [W] <;> ring
  have at1 : W.eval 1=4*v+11*u := by
    simp [W] <;> ring
  rw [w0,eval_zero] at at0 at1
  have twoU : 22*u=0 := by linear_combination at0 - at1
  have u0 : u=0 := (mul_eq_zero.mp twoU).resolve_left (by norm_num)
  have fourV : 4*v=0 := by simpa only [u0,mul_zero,sub_zero] using at0.symm
  have v0 : v=0 := (mul_eq_zero.mp fourV).resolve_left (by norm_num)
  rw [pForm]
  simp [V,u0,v0]

end
end RKResearch.Certified.Graded.ERK13NativeFirst
