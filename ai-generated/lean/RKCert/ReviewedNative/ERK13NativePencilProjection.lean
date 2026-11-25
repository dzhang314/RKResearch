module

public import RKCert.ReviewedNative.ERK13NativePencilCubicBridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Low-degree square projections in the full degree-seven pencil

The degree-five and degree-six representatives of four paid endpoint
differences are compared modulo the whole degree-seven mesh by an
integral recurrence and one Bézout identity. No splitting, order on the
field, or stage hypotheses are needed. -/
namespace RKResearch.Certified.Graded.ERK13NativePencil

open ERK13NativeFirst Polynomial MarkedAdjacent NativeLobatto
open scoped Classical BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {P Q : K[X]}
set_option maxHeartbeats 1700000

private def little4 (K : Type*) [Field K] : K[X] := 42*X^4-84*X^3+56*X^2-14*X+1
private def little5 (K : Type*) [Field K] : K[X] := 132*X^5-330*X^4+300*X^3-120*X^2+20*X-1
private def data4 (K : Type*) [Field K] : Fin 6→K := ![0,1,-14,56,-84,42]

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

private theorem moment4 (k : Fin 4) : endpointMoment K k.val (ofFn 6 (data4 K))=0 := by
  rw [endpoint_ofFn]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,data4]

private theorem moment5 (k : Fin 4) : endpointMoment K k.val (earlyLobattoMesh K)=0 := by
  change endpointMoment K k.val (ofFn 7 (meshCoeffs K))=0
  rw [endpoint_ofFn]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,meshCoeffs]

private theorem little_recurrence :
    5*little4 K=(26*X-19)*little5 K-2*radauQuotient X := by
  unfold little4 little5 radauQuotient
  ring

private theorem pencil_coprime (a b : K) (an : a≠0) : IsCoprime (pencilB a b) (little5 K) := by
  let M : K[X] := -4620*X^4+9240*X^3-6111*X^2+1491*X-100
  let N : K[X] := 60060*X^5-164010*X^4+163548*X^3-71925*X^2+13137*X-705
  have base : M*radauQuotient X+N*little5 K=5 := by
    dsimp [M,N,radauQuotient,little5]; ring
  have F : lobattoValue (X:K[X])=little5 K := rfl
  have bez : M*pencilB a b+(C a*N-C b*M)*little5 K=C (5*a) := by
    rw [pencilB,F,map_mul,Polynomial.C_ofNat (R:=K) 5]
    linear_combination (C a)*base
  have den : 5*a≠0 := mul_ne_zero (by norm_num) an
  refine ⟨C (5*a)⁻¹*M,C (5*a)⁻¹*(C a*N-C b*M),?_⟩
  calc
    _=C (5*a)⁻¹*(M*pencilB a b+(C a*N-C b*M)*little5 K) := by ring
    _=1 := by rw [bez,←map_mul,inv_mul_cancel₀ den,map_one]

/-- Four true endpoint differences force a degree-six square projection to vanish
whenever the order-seven pencil mesh divides PQ with deg Q ≤ 3. -/
theorem pencil_small_square_projection_zero {alpha beta : K} {b : Fin 19→K} {G : K[X]}
    (E : NativeEarlyPencilData b G alpha beta) (dg : G.natDegree=7)
    (pd : P.natDegree≤6) (p0 : P.eval 0=0) (tests : ∀ k : Fin 4, endpointMoment K k.val P=0)
    (qd : Q.natDegree≤3) (qn : Q≠0) (divides : G∣P*Q) : P=0 := by
  obtain ⟨v,dv⟩ := reduction_by_next_degree (a:=5) pd (earlyLobattoMesh_degree (K:=K))
  obtain ⟨u,du⟩ := reduction_by_next_degree (a:=4) dv (d4 (K:=K))
  let Z := P-v • earlyLobattoMesh K-u • ofFn 6 (data4 K)
  have z0 : Z.eval 0=0 := by
    simp only [Z,p4_form,mesh_form,eval_sub,eval_smul,eval_mul,eval_X,p0,zero_mul,smul_zero,sub_zero]
  have zz : Z=0 := NativeMoments.endpoint_moments_detect du z0 (fun k=>by
    rw [←endpointMoment_apply]
    simp only [Z,map_sub,map_smul,tests k,moment4 k,moment5 k,smul_zero,sub_zero])
  let V : K[X] := C v*little5 K+C u*little4 K
  have pForm : P=X*V := by
    change P-v • earlyLobattoMesh K-u • ofFn 6 (data4 K)=0 at zz
    rw [mesh_form,p4_form,smul_eq_C_mul,smul_eq_C_mul] at zz
    dsimp only [V]; linear_combination zz
  let B := pencilB alpha beta
  have gForm : G=X*B := pencil_data_factor E
  have bn : B≠0 := by intro z; rw [gForm,z,mul_zero,natDegree_zero] at dg; omega
  have bd : B.natDegree=6 := by rw [gForm,natDegree_X_mul bn] at dg; omega
  obtain ⟨J,hJ⟩ := divides
  have vdiv : B∣V*Q := by
    refine ⟨J,mul_left_cancel₀ (X_ne_zero : (X:K[X])≠0) ?_⟩
    rw [pForm,gForm] at hJ
    simpa only [mul_assoc] using hJ
  let W : K[X] := 5*C alpha*C v+C u*(C alpha*(26*X-19)+2*C beta)
  have blend : W*little5 K=5*C alpha*V+(2*C u)*B := by
    dsimp only [W,V,B,pencilB]
    rw [show lobattoValue (X:K[X])=little5 K from rfl]
    linear_combination -(C alpha*C u)*little_recurrence (K:=K)
  obtain ⟨T,hT⟩ := vdiv
  have canc : B∣little5 K*(W*Q) := by
    refine ⟨5*C alpha*T+2*C u*Q,?_⟩
    calc
      _=(W*little5 K)*Q := by ring
      _=_ := by rw [blend,add_mul,mul_assoc,hT]; ring
  have wd : W.natDegree≤1 := by
    have f : (26*X-19:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans
      (max_le (natDegree_mul_le_of_le (show (26:K[X]).natDegree≤0 by simp)
        (show (X:K[X]).natDegree≤1 by simp)) (by simp))
    have k0 (x y : K) : ((5:K[X])*C x*C y).natDegree≤0 :=
      natDegree_mul_le_of_le (natDegree_mul_le_of_le (show (5:K[X]).natDegree≤0 by simp)
       (show (C x).natDegree≤0 by simp)) (show (C y).natDegree≤0 by simp)
    have k1 : (C alpha*(26*X-19)+2*C beta).natDegree≤1 :=
      (natDegree_add_le _ _).trans (max_le (natDegree_mul_le_of_le (show (C alpha).natDegree≤0 by simp) f)
        ((natDegree_mul_le_of_le (show (2:K[X]).natDegree≤0 by simp) (show (C beta).natDegree≤0 by simp)).trans (by decide)))
    exact (natDegree_add_le _ _).trans (max_le ((k0 alpha v).trans (by decide))
      (natDegree_mul_le_of_le (show (C u).natDegree≤0 by simp) k1))
  have w0 : W=0 := by
    by_contra wn
    have deg := natDegree_le_of_dvd ((pencil_coprime alpha beta E.radauNonzero).dvd_of_dvd_mul_left canc) (mul_ne_zero wn qn)
    change B.natDegree≤(W*Q).natDegree at deg
    rw [bd,natDegree_mul wn qn] at deg
    omega
  have at0 : W.eval 0=5*alpha*v+u*(alpha*(-19)+2*beta) := by
    simp only [W,eval_add,eval_mul,eval_C,eval_sub,eval_X,eval_ofNat] <;> ring
  have at1 : W.eval 1=5*alpha*v+u*(alpha*7+2*beta) := by
    simp only [W,eval_add,eval_mul,eval_C,eval_sub,eval_X,eval_ofNat] <;> ring
  rw [w0,eval_zero] at at0 at1
  have tU : (26*alpha)*u=0 := by linear_combination at0-at1
  have uz : u=0 := (mul_eq_zero.mp tU).resolve_left (mul_ne_zero (by norm_num) E.radauNonzero)
  rw [uz,zero_mul,add_zero] at at0
  have vz : v=0 := (mul_eq_zero.mp at0.symm).resolve_left (mul_ne_zero (by norm_num) E.radauNonzero)
  rw [pForm]
  simp [V,uz,vz]

end
end RKResearch.Certified.Graded.ERK13NativePencil
