module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoGradeThree

import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Literal output weight and nonvanishing in the early marked pencil

The universal coprimality is a single integral identity with constant five.
The two pencil coefficients and their sum are nonzero because the mesh has
degree seven and the actual final weight is live. The known pure Lobatto
escape gives the final weight 1/42 by the same degree-zero native probe. -/

namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module MarkedAdjacent NativeLobatto
open scoped Classical BigOperators Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K} {r a : ℕ} {G : K[X]}

private theorem earlyRadauMode_degree_exact : (earlyRadauMode K).natDegree=7 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (earlyRadauMode_degree (K:=K))
  rw [earlyRadauMode,ofFn_coeff_eq_val_of_lt _ (by decide : 7<8)]
  norm_num [modeCoeffs]

private theorem early_mesh_one : (earlyLobattoMesh K).eval 1=1 := by
  rw [earlyLobattoMesh_eval]
  norm_num [lobattoValue]

private theorem early_mode_one : (earlyRadauMode K).eval 1=1 := by
  rw [earlyRadauMode_eval]
  norm_num [radauValue,radauQuotient]

private theorem early_mesh_m0 : unitMoment K 0 (earlyLobattoMesh K)=1/42 :=
  early_mesh_unit_moment (K:=K) (0 : Fin 6)

private theorem early_mode_m0 : unitMoment K 0 (earlyRadauMode K)=0 :=
  early_mode_unit_moment (K:=K) (0 : Fin 6)

private theorem early_mesh_at_origin : (earlyLobattoMesh K).eval 0=0 := by
  rw [earlyLobattoMesh_eval,zero_mul]

private theorem early_mode_at_origin : (earlyRadauMode K).eval 0=0 := by
  rw [earlyRadauMode_eval,radauValue,zero_mul]

private theorem early_mesh_endpoint (k : Fin 5) :
    endpointMoment K k.val (earlyLobattoMesh K)=0 := by
  change unitMoment K k.val (earlyLobattoMesh K) -
    unitMoment K (k.val+1) (earlyLobattoMesh K)=0
  rw [early_mesh_unit_moment (K:=K) (⟨k.val,by have := k.isLt; omega⟩ : Fin 6),
    early_mesh_unit_moment (K:=K) (⟨k.val+1,by have := k.isLt; omega⟩ : Fin 6),sub_self]

private theorem early_mode_endpoint (k : Fin 5) :
    endpointMoment K k.val (earlyRadauMode K)=0 := by
  change unitMoment K k.val (earlyRadauMode K) -
    unitMoment K (k.val+1) (earlyRadauMode K)=0
  rw [early_mode_unit_moment (K:=K) (⟨k.val,by have := k.isLt; omega⟩ : Fin 6),
    early_mode_unit_moment (K:=K) (⟨k.val+1,by have := k.isLt; omega⟩ : Fin 6),sub_zero]

/-- All six original paid mesh moments equal the measured literal-endpoint
weight times its actual mesh value. A core/head row cannot supply this mass. -/
theorem NativeMarkedEscapeChart.early_mesh_output_moments
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7) :
    ∀ k≤5, unitMoment K k G=G.eval 1*b (Fin.last 18) := by
  have aw : a=5 ∨ a=6 := H.first.width.elim Or.inr (fun h=>Or.inl h.1)
  have degreeG := H.first.degree
  obtain ⟨d,hd,repr⟩ := H.early_mesh_exact_mark ha ho early
  have hf : d∈zeroSpace A 7 := escapeHeadBand_paid_from_seven H.head 0 hd
  have d0 : probe A b 0 d=0 :=
    LinearMap.mem_ker.mp (probe_zeroSpace (j:=7) (k:=0) ho (by decide) hf)
  have one : probe A b 0 (coordinate (K:=K) (Fin.last 18))=b (Fin.last 18) := by
    change row (fun i=>b i*(nodes A i)^0) (coordinate (K:=K) (Fin.last 18))=_
    rw [row_coordinate,pow_zero,mul_one]
  have mass0 : unitMoment K 0 G=G.eval 1*b (Fin.last 18) := calc
    _ = probe A b 0 (evalNodes A G) := (probe_evalNodes ho G 0 (by omega)).symm
    _ = _ := by simp only [repr,map_add,map_smul,d0,one,zero_add,smul_eq_mul]
  intro k hk
  exact ((H.mesh_moments ha ho).2.1 k hk).trans mass0

/-- The true last Butcher weight in the first, degree-six marked branch. -/
theorem NativeMarkedEscapeChart.last_weight_of_degree_six
    (H : NativeMarkedEscapeChart A b 5 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    b (Fin.last 18)=1/42 := by
  have early := terminal_enters_seven_of_first_degree_six13 ha ho H.seed H.first
  obtain ⟨s,sn,repr⟩ := H.degree_six_mesh_is_lobatto ha ho
  have e1 : G.eval 1=s := by
    simp only [repr,eval_smul,early_mesh_one,smul_eq_mul,mul_one]
  have e0 : unitMoment K 0 G=s*(1/42) := by
    simp only [repr,map_smul,early_mesh_m0,smul_eq_mul]
  have m : s*(1/42)=s*b (Fin.last 18) := by
    simpa only [e0,e1] using H.early_mesh_output_moments ha ho early 0 (by decide)
  exact (mul_left_cancel₀ sn m).symm

/-- No terminal time is assumed in this decomposition. Strict degree seven
forces the Radau coefficient, but the other two nonvanishing facts are earned
only by the separate early endpoint theorem below. -/
theorem NativeMarkedEscapeChart.degree_seven_mesh_in_pencil
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ∃ alpha beta : K, alpha≠0 ∧ G=alpha • earlyRadauMode K + beta • earlyLobattoMesh K := by
  have gd : G.natDegree=7 := H.first.degree
  obtain ⟨alpha,low⟩ := reduction_by_next_degree (a:=6) gd.le
    (earlyRadauMode_degree_exact (K:=K))
  obtain ⟨beta,lower⟩ := reduction_by_next_degree (a:=5) low (earlyLobattoMesh_degree (K:=K))
  have mesh := H.mesh_moments ha ho
  have cut0 : ((G-alpha • earlyRadauMode K)-beta • earlyLobattoMesh K).eval 0=0 := by
    simp only [eval_sub,eval_smul,mesh.1,early_mode_at_origin,early_mesh_at_origin,
      smul_zero,sub_zero]
  have rz := NativeMoments.endpoint_moments_detect lower cut0 (fun i => by
    rw [←endpointMoment_apply]
    simp only [map_sub,map_smul,mesh.2.2 i.val i.isLt,early_mode_endpoint i,
      early_mesh_endpoint i,smul_zero,sub_zero])
  have repr : G=alpha • earlyRadauMode K + beta • earlyLobattoMesh K := by
    have e := sub_eq_zero.mp rz
    calc
      G = alpha • earlyRadauMode K+(G-alpha • earlyRadauMode K) := by abel
      _ = _ := by rw [e]
  have an : alpha≠0 := by
    intro az
    rw [az,zero_smul,sub_zero] at low
    omega
  exact ⟨alpha,beta,an,repr⟩

/-- This integral Bézout certificate is independent of node order and
works over every characteristic-zero field, not just over a finite residue. -/
theorem lobatto_radau_not_both_zero (x : K) :
    ¬(lobattoValue x=0 ∧ radauQuotient x=0) := by
  rintro ⟨hf,hj⟩
  have bezout :
      (60060*x^5-164010*x^4+163548*x^3-71925*x^2+13137*x-705)*lobattoValue x+
      (-4620*x^4+9240*x^3-6111*x^2+1491*x-100)*radauQuotient x=5 := by
    unfold lobattoValue radauQuotient
    ring
  simp only [hf,hj,mul_zero,zero_add] at bezout
  exact (by norm_num : (0:K)≠5) bezout

/-- Literal original-field pencil data including every denominator guard
needed by the later cubic and quartic gates. -/
structure NativeEarlyPencilData (b : Fin 19 → K) (G : K[X]) (alpha beta : K) : Prop where
  radauNonzero : alpha≠0
  lobattoNonzero : beta≠0
  sumNonzero : alpha+beta≠0
  chart : G=alpha • earlyRadauMode K + beta • earlyLobattoMesh K
  atOne : G.eval 1=alpha+beta
  lastWeight : b (Fin.last 18)=beta/(42*(alpha+beta))
  rootGuards : ∀ x : K, x≠0 → G.eval x=0 →
    lobattoValue x≠0 ∧ radauQuotient x≠0 ∧ radauValue x≠0

-- Keep scalar root arithmetic out of the dependent reviewed tableau proof.
private theorem pencil_eval_at (alpha beta : K)
    (shape : G=alpha • earlyRadauMode K+beta • earlyLobattoMesh K) (x : K) :
    G.eval x=x*(alpha*radauQuotient x+beta*lobattoValue x) := by
  simp only [shape,eval_add,eval_smul,earlyRadauMode_eval,earlyLobattoMesh_eval,
    radauValue,smul_eq_mul]
  ring

private theorem pencil_nonzero_at_root {alpha beta x : K}
    (an : alpha≠0) (bn : beta≠0) (xn : x≠0)
    (rel : alpha*radauQuotient x+beta*lobattoValue x=0) :
    lobattoValue x≠0 ∧ radauQuotient x≠0 ∧ radauValue x≠0 := by
  have fn : lobattoValue x≠0 := by
    intro fz
    have j : alpha*radauQuotient x=0 := by simpa only [fz,mul_zero,add_zero] using rel
    exact lobatto_radau_not_both_zero x ⟨fz,(mul_eq_zero.mp j).resolve_left an⟩
  have jn : radauQuotient x≠0 := by
    intro jz
    have f : beta*lobattoValue x=0 := by simpa only [jz,mul_zero,zero_add] using rel
    exact fn ((mul_eq_zero.mp f).resolve_left bn)
  exact ⟨fn,jn,mul_ne_zero xn jn⟩

theorem NativeMarkedEscapeChart.early_degree_seven_pencil_data
    (H : NativeMarkedEscapeChart A b 6 G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7) :
    ∃ alpha beta : K, NativeEarlyPencilData b G alpha beta := by
  obtain ⟨alpha,beta,an,repr⟩ := H.degree_seven_mesh_in_pencil ha ho
  have at1 : G.eval 1=alpha+beta := by
    simp only [repr,eval_add,eval_smul,early_mode_one,early_mesh_one,smul_eq_mul,mul_one]
  have m0 : unitMoment K 0 G=beta/42 := by
    simp only [repr,map_add,map_smul,early_mode_m0,early_mesh_m0,mul_zero,zero_add,
      smul_eq_mul,div_eq_mul_inv,one_mul]
  have m : beta/42=(alpha+beta)*b (Fin.last 18) := by
    simpa only [m0,at1] using H.early_mesh_output_moments ha ho early 0 (by decide)
  have bn : beta≠0 := by
    intro bz
    rw [bz,zero_div,add_zero] at m
    exact (mul_ne_zero an H.head.paidRanks.lastActive.live) m.symm
  have forty : (42:K)≠0 := by norm_num
  have sumN : alpha+beta≠0 := by
    intro z
    rw [z,zero_mul] at m
    exact div_ne_zero bn forty m
  have mass : b (Fin.last 18)=beta/(42*(alpha+beta)) := by
    apply (eq_div_iff (mul_ne_zero forty sumN)).mpr
    calc
      _ = (beta/42)*42 := by rw [m]; ring
      _ = beta := div_mul_cancel₀ _ forty
  refine ⟨alpha,beta,⟨an,bn,sumN,repr,at1,mass,?_⟩⟩
  intro x xn root
  have f := (pencil_eval_at alpha beta repr x).symm.trans root
  exact pencil_nonzero_at_root an bn xn ((mul_eq_zero.mp f).resolve_left xn)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
