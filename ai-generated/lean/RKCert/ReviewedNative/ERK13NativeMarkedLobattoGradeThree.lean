module

public import RKCert.ReviewedNative.ERK13NativeMarkedCubicPorts
public import RKCert.ReviewedNative.NativeLobattoCubic
public import Mathlib.Algebra.Polynomial.OfFn

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Original degree-six marked escape: every grade-three defect is in the core

The native primitive, six genuinely paid moments and the measured physical
terminal determine both normalizations. The already checked distinct-root
Lobatto theorem then kills the nonzero profile from the actual two ports.
There is no hypothesis selecting a Lobatto mesh or a Radau mode. -/

namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module MarkedAdjacent NativeLobatto
open scoped Classical BigOperators Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {r : ℕ} {G J : K[X]}

def meshCoeffs (K : Type*) [Field K] : Fin 7 → K :=
  ![0,-1,20,-120,300,-330,132]

def modeCoeffs (K : Type*) [Field K] : Fin 8 → K :=
  ![0,7,-168,1260,-4200,6930,-5544,1716]

/-- The degree-six mesh normalized to value one at the actual endpoint. -/
def earlyLobattoMesh (K : Type*) [Field K] : K[X] := ofFn 7 (meshCoeffs K)

/-- The degree-at-most-seven unmarked F7 mode, normalized at one. -/
def earlyRadauMode (K : Type*) [Field K] : K[X] := ofFn 8 (modeCoeffs K)

theorem earlyLobattoMesh_eval (x : K) :
    (earlyLobattoMesh K).eval x=x*lobattoValue x := by
  rw [earlyLobattoMesh,ofFn_eq_sum_monomial,eval_finsetSum]
  simp only [eval_monomial]
  norm_num [Fin.sum_univ_succ,meshCoeffs,lobattoValue] <;> ring

theorem earlyRadauMode_eval (x : K) :
    (earlyRadauMode K).eval x=radauValue x := by
  rw [earlyRadauMode,ofFn_eq_sum_monomial,eval_finsetSum]
  simp only [eval_monomial]
  norm_num [Fin.sum_univ_succ,modeCoeffs,radauValue,radauQuotient] <;> ring

theorem earlyLobattoMesh_degree : (earlyLobattoMesh K).natDegree=6 := by
  have upper : (earlyLobattoMesh K).natDegree<7 := ofFn_natDegree_lt (by decide) (meshCoeffs K)
  apply natDegree_eq_of_le_of_coeff_ne_zero (by omega)
  rw [earlyLobattoMesh,ofFn_coeff_eq_val_of_lt _ (by decide : 6<7)]
  norm_num [meshCoeffs]

theorem earlyRadauMode_degree : (earlyRadauMode K).natDegree≤7 :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) (modeCoeffs K))

/-- A finite exact coefficient calculation in the native zero-constant primitive. -/
private theorem unitMoment_ofFn {n : ℕ} (c : Fin n → K) (k : ℕ) :
    unitMoment K k (ofFn n c) =
    ∑ i : Fin n, c i/((i.val+k+1:ℕ):K) := by
  rw [unitMoment_apply,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one]

set_option maxHeartbeats 800000 in
theorem early_mesh_unit_moment (k : Fin 6) :
    unitMoment K k.val (earlyLobattoMesh K)=1/42 := by
  rw [earlyLobattoMesh,unitMoment_ofFn]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,meshCoeffs]

set_option maxHeartbeats 800000 in
theorem early_mode_unit_moment (k : Fin 6) :
    unitMoment K k.val (earlyRadauMode K)=0 := by
  rw [earlyRadauMode,unitMoment_ofFn]
  fin_cases k <;> norm_num [Fin.sum_univ_succ,modeCoeffs]

/-- The physical first alias is a nonzero scalar times the Lobatto mesh.
Degree reduction spends the top coefficient; the remaining degree-five
polynomial has its origin and five endpoint differences paid. -/
theorem NativeMarkedEscapeChart.degree_six_mesh_is_lobatto
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ t : K, t≠0 ∧ G=t • earlyLobattoMesh K := by
  obtain ⟨t,td⟩ := reduction_by_next_degree (a:=5) H.first.degree.le
    (earlyLobattoMesh_degree (K:=K))
  have mesh := H.mesh_moments ha ho
  have e0 : (earlyLobattoMesh K).eval 0=0 := by rw [earlyLobattoMesh_eval,zero_mul]
  have cut0 : (G-t • earlyLobattoMesh K).eval 0=0 := by
    rw [eval_sub,eval_smul,mesh.1,e0,smul_zero,sub_zero]
  have result := NativeMoments.endpoint_moments_detect td cut0 (fun i => by
    rw [←endpointMoment_apply,map_sub,map_smul,mesh.2.2 i.val i.isLt]
    have both : endpointMoment K i.val (earlyLobattoMesh K)=0 := by
      change unitMoment K i.val (earlyLobattoMesh K) -
        unitMoment K (i.val+1) (earlyLobattoMesh K)=0
      rw [early_mesh_unit_moment (K:=K) (⟨i.val,by have := i.isLt; omega⟩ : Fin 6),
        early_mesh_unit_moment (K:=K) (⟨i.val+1,by have := i.isLt; omega⟩ : Fin 6),sub_self]
    rw [both,smul_zero,sub_zero])
  have repr := sub_eq_zero.mp result
  have tn : t≠0 := by
    intro z
    have gz : G=0 := by simpa only [z,zero_smul] using repr
    have dg := H.first.degree
    rw [gz,natDegree_zero] at dg
    omega
  exact ⟨t,tn,repr⟩

/-- The concrete polynomial value needed by the scalar checker is forced,
not merely chosen as a formal representative of a marked subspace. -/
theorem NativeEarlyF7Mode.eval_eq_radauValue
    (M : NativeEarlyF7Mode A U w r J)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (one : nodes A (Fin.last 18)=1) (x : K) :
    J.eval x=radauValue x := by
  let D := J-earlyRadauMode K
  have dd : D.natDegree≤7 := by
    simpa only [D,max_self] using natDegree_sub_le_of_le M.degree (earlyRadauMode_degree (K:=K))
  have d0 : D.eval 0=0 := by
    simp only [D,eval_sub,M.origin,earlyRadauMode_eval,radauValue,zero_mul,sub_zero]
  have d1 : D.eval 1=0 := by
    rw [show D=J-earlyRadauMode K from rfl,eval_sub,M.lastOne,earlyRadauMode_eval]
    norm_num [radauValue,radauQuotient]
  have first0 : nodes A 0=0 := by
    have h (j : Fin 19) : A 0 j=0 := ha 0 j (Fin.zero_le _)
    simp [nodes,Matrix.mulVec,dotProduct,h]
  have tested (k : ℕ) (hk : k<6) : probe A b k (evalNodes A D)=0 := by
    rw [probe_evalNodes ho D k (by omega)]
    change unitMoment K k D=0
    rw [show D=J-earlyRadauMode K from rfl,map_sub,M.moments k (by omega),
      early_mode_unit_moment (K:=K) (⟨k,hk⟩ : Fin 6),sub_zero]
  have dz := polynomial_zero_of_endpoint_probes ha ho (n:=6) (by decide) one dd
    (by simpa only [evalNodes_apply,first0] using d0)
    (by simpa only [evalNodes_apply,one] using d1) tested
  have same : J=earlyRadauMode K := sub_eq_zero.mp dz
  rw [same,earlyRadauMode_eval]

/-- Every grade-three defect is in the original invariant core for a=5,
including either actual F7 rank. No early-terminal premise is needed:
the true entry in E7 is already a theorem of the degree-six escape. -/
theorem NativeMarkedEscapeChart.grade_three_le_core_of_degree_six
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    zeroSpace A 3 ≤ U := by
  intro v hv
  by_contra outside
  have early := terminal_enters_seven_of_first_degree_six13 ha ho H.seed H.first
  obtain ⟨P,J,scale,k,l,pn,pd,mode,pair⟩ := H.physical_cubic_data_of_off_core ha ho early hv outside
  obtain ⟨s,sn,mesh⟩ := H.degree_six_mesh_is_lobatto ha ho
  have roots (i : Fin 19) (ni : nodes A i≠0) (g : G.eval (nodes A i)=0) :
      lobattoValue (nodes A i)=0 := by
    rw [mesh,eval_smul,smul_eq_mul,earlyLobattoMesh_eval] at g
    exact (mul_eq_zero.mp ((mul_eq_zero.mp g).resolve_left sn)).resolve_left ni
  have rt := roots k pair.firstNonzero pair.firstMesh
  have ru := roots l pair.secondNonzero pair.secondMesh
  have one := H.head.paidRanks.lastActive.node_eq_one ha H.seed
  apply pn
  rcases mode with jz | M
  · exact cubic_profile_zero_of_lobatto_ports P pd (nodes A k) (nodes A l) 0 rt ru
      pair.distinct pair.firstLinear pair.firstQuadratic
      (by simpa only [jz,eval_zero,mul_zero,zero_mul] using pair.firstCubic)
      pair.secondQuadratic
      (by simpa only [jz,eval_zero,mul_zero,zero_mul] using pair.secondCubic)
  · exact cubic_profile_zero_of_lobatto_ports P pd (nodes A k) (nodes A l) scale rt ru
      pair.distinct pair.firstLinear pair.firstQuadratic
      (by simpa only [M.eval_eq_radauValue ha ho one] using pair.firstCubic)
      pair.secondQuadratic
      (by simpa only [M.eval_eq_radauValue ha ho one] using pair.secondCubic)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
