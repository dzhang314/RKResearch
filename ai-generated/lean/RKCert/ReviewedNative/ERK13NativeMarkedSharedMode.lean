module

public import RKCert.ReviewedNative.ERK13NativeMarkedEarlyMode

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # One measured cubic leakage for every original preterminal port

Only the actual endpoint functional appears. Changing the prefix match or
factoring the same mask differently does not change its coefficient. All
clock words of degree at most two have no leakage. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse Module RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w v : Fin 19 → K} {r a : ℕ} {G P : K[X]}

/-- The portion of the native primitive transport independent of the
prefix match and of the factorization of its clock mask. -/
def initialPrimitiveColumn (A : Matrix (Fin 19) (Fin 19) K)
    (v : Fin 19 → K) (P : K[X]) : K[X] →ₗ[K] (Fin 19 → K) :=
  (evalNodes A).comp (primitive.comp (LinearMap.mulLeft K P)) -
  (mat A).comp ((evalNodes A).comp (LinearMap.mulLeft K P)) +
  (mat A).comp ((diag v).comp (evalNodes A))

theorem initialPrimitiveColumn_apply (R : K[X]) :
    initialPrimitiveColumn A v P R = evalNodes A (primitive (R*P))-
      mat A (evalNodes A (R*P))+mat A (evalNodes A R*v) := by
  change evalNodes A (primitive (P*R))-mat A (evalNodes A (P*R))+
    mat A (diag v (evalNodes A R)) = _
  have h : diag v (evalNodes A R)=evalNodes A R*v := by
    ext i
    simp [diag_apply,mul_comm]
  rw [h,mul_comm P R]

private theorem NativeMarkedEscapeChart.early_F6_last_zero
    (H : NativeMarkedEscapeChart A b a G r U w) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    {x : Fin 19 → K} (hx : x∈zeroSpace A 6) : x (Fin.last 18)=0 := by
  have f6 : zeroSpace A 6=escapeHeadBand A U w (r+1) := H.head.head.flags 1 (by decide)
  exact H.early_head_last_zero ho early (f6 ▸ hx)

private theorem initialPrimitiveColumn_low_paid (ho : HasOrder 13 A b)
    (hv : v∈zeroSpace A 3) (pd : P.natDegree≤3) {R : K[X]} (rd : R.natDegree≤2) :
    initialPrimitiveColumn A v P R∈zeroSpace A 6 := by
  have rp : (R*P).natDegree≤5 := natDegree_mul_le_of_le rd pd
  have dv := primitive_defect (q:=5) A (R*P) rp
  have hvR : evalNodes A R*v∈zeroSpace A 5 := by
    rw [mul_comm]
    exact zeroSpace_mul_treeSpace ho (m:=3) (n:=2) (by decide) hv (evalNodes_mem_treeSpace A _ rd)
  have av := mat_zeroSpace_charZero A 5 hvR
  rw [initialPrimitiveColumn_apply]
  convert (zeroSpace A 6).sub_mem av dv using 1 <;> abel

private theorem NativeMarkedEscapeChart.initialPrimitiveColumn_last_cubic
    (H : NativeMarkedEscapeChart A b a G r U w) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (pd : P.natDegree≤3) {R : K[X]} (rd : R.natDegree≤3) :
    initialPrimitiveColumn A v P R (Fin.last 18)=
      R.coeff 3 * initialPrimitiveColumn A v P (X^3) (Fin.last 18) := by
  obtain ⟨t,ht⟩ := MarkedAdjacent.reduction_by_next_degree (a:=2) rd
    (show (X^3 : K[X]).natDegree=2+1 by simp)
  have c := coeff_eq_zero_of_natDegree_lt (ht.trans_lt (by decide : 2<3))
  rw [coeff_sub,Polynomial.coeff_smul,smul_eq_mul,
    show ((X^3 : K[X]).coeff 3)=1 by simp,mul_one,sub_eq_zero] at c
  have lo := H.early_F6_last_zero ho early (initialPrimitiveColumn_low_paid ho hv pd ht)
  rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sub_eq_zero,←c] at lo
  exact lo

private theorem NativeMarkedEscapeChart.measured_cubic_port_residual
    (H : NativeMarkedEscapeChart A b a G r U w) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (pd : P.natDegree≤3) {S T : K[X]}
    (rd : (T*S).natDegree≤3) {z g : Fin 19 → K} (gu : g∈U)
    (defn : ∀ i, z i=S.eval (nodes A i)*(P.eval (nodes A i)-v i)) :
    (evalNodes A (primitive ((T*S)*P))-mat A (evalNodes A T*(z-g))) (Fin.last 18)=
      (T*S).coeff 3 * initialPrimitiveColumn A v P (X^3) (Fin.last 18) := by
  have gu' : evalNodes A T*g∈U :=
    clock_function_mem (fun t ht=>H.head.head.coreStable (Submodule.mem_map_of_mem ht)) T.eval gu
  have hLast := H.early_F6_last_zero ho early
    (mat_zeroSpace_charZero A 5 (H.head.head.coreInside gu'))
  have mask : evalNodes A T*(z-g)=
      evalNodes A ((T*S)*P)-(evalNodes A (T*S)*v+evalNodes A T*g) := by
    ext i
    simp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply,evalNodes_apply,eval_mul,defn i]
    ring
  have vector : evalNodes A (primitive ((T*S)*P))-mat A (evalNodes A T*(z-g)) =
      initialPrimitiveColumn A v P (T*S)+mat A (evalNodes A T*g) := by
    rw [mask,map_sub,map_add,initialPrimitiveColumn_apply]
    abel
  rw [vector,Pi.add_apply,hLast,add_zero,
    H.initialPrimitiveColumn_last_cubic ho early hv pd rd]

/-- Both native F7 ranks give all early cubic primitive ports with one
shared scalar. In the pure case take J=0. In the extra-mode case J is
normalized in the actual paid F7 and the scalar is the original last
value of the cubic word. -/
theorem NativeMarkedEscapeChart.early_cubic_shared_ports
    (H : NativeMarkedEscapeChart A b a G r U w)
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 13 A b)
    (early : coordinate (K:=K) (Fin.last 18)∈treeSpace A 7)
    (hv : v∈zeroSpace A 3) (pd : P.natDegree≤3) :
    ∃ J : K[X], (J=0 ∨ NativeEarlyF7Mode A U w r J) ∧ ∃ κ : K,
      ∀ (S T : K[X]) (z g : Fin 19 → K) (k : Fin 19),
      NativeMarkedPivot A b U w v z G S k g →
      (∀ i, z i=S.eval (nodes A i)*(P.eval (nodes A i)-v i)) →
      (T*S).natDegree≤3 → (primitive ((T*S)*P)).eval (nodes A k)=
        (κ*(T*S).coeff 3)*J.eval (nodes A k) := by
  rcases H.early_F7_mode ha ho early with pure | ⟨J,M⟩
  · refine ⟨0,Or.inl rfl,0,?_⟩
    intro S T z g k site defs td
    have p7 := H.primitive_prefix_paid ho (d:=3) (by decide) hv site.core defs pd T td
    rw [show 3+4=7 by decide,pure] at p7
    have tagged : evalNodes A (primitive ((T*S)*P))-mat A (evalNodes A T*(z-g))-
        (0:K) • evalNodes A (0:K[X]) ∈ markedEscapeHeadBand A b U w (r+2) := by
      simpa only [zero_smul,sub_zero] using
        (Submodule.mem_sup_left (T:=terminalMark A b) p7)
    have p := site.primitive_mode_trace ha (evalNodes A T) (R:=(T*S)*P)
      (J:=0) (factor:=0) (n:=r+2) tagged
    simpa only [zero_mul] using p
  · let κ := initialPrimitiveColumn A v P (X^3) (Fin.last 18)
    refine ⟨J,Or.inr M,κ,?_⟩
    intro S T z g k site defs td
    let q := evalNodes A (primitive ((T*S)*P))-mat A (evalNodes A T*(z-g))
    have p7 : q∈zeroSpace A 7 := H.primitive_prefix_paid ho (d:=3)
      (by decide) hv site.core defs pd T td
    have meas : q (Fin.last 18)=κ*(T*S).coeff 3 := by
      rw [mul_comm κ]
      exact H.measured_cubic_port_residual ho early hv pd td site.core defs
    have pure := M.remove_measured (fun y hy=>H.early_head_last_zero ho early hy)
      (H.head.paidRanks.lastActive.node_eq_one ha H.seed) p7
    rw [meas] at pure
    exact site.primitive_mode_trace ha (evalNodes A T) (R:=(T*S)*P) (J:=J)
      (factor:=κ*(T*S).coeff 3) (n:=r+2) (Submodule.mem_sup_left pure)

end
end RKResearch.Certified.Graded.ERK13NativeFirst
