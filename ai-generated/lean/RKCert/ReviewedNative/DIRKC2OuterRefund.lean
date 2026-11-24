module

public import RKCert.ReviewedNative.DIRKC2CoreClock
public import RKCert.ReviewedNative.DIRKCubicCleanTrace

@[expose] public section

/-! # Earliest exterior clocks, with actual paid diagonal refunds -/
namespace RKResearch.Certified.Graded.OuterHead

open RKCert.OneEscape Polynomial
open scoped Matrix Classical
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b w : Fin s → K}
variable {U : Submodule K (Fin s → K)}

/-- A chronological exterior cut and its distinct earlier clocks. -/
structure ExteriorStep (C : CoreMask A U) (m : ℕ) where
  next : Fin s
  old : Fin m → Fin s
  earlier : ∀ j, old j < next
  next_out : C.mask next=0
  old_out : ∀ j, C.mask (old j)=0
  next_nz : nodes A next≠0
  old_nz : ∀ j, nodes A (old j)≠0
  distinct : Function.Injective (nodes A ∘ old)
  fresh : ∀ j, nodes A next≠nodes A (old j)
  cover : ∀ j < next, C.mask j=0 → nodes A j≠0 → ∃ l, nodes A j=nodes A (old l)

def ClockDebuts.step {n : ℕ} {C : CoreMask A U} (D : ClockDebuts A C.mask n) (k : Fin n) :
    ExteriorStep C k.val := by
  let f := Fin.castLE (Nat.le_of_lt k.isLt)
  refine ⟨D.row k,D.row ∘ f,fun l => D.inc (show f l < k from l.isLt),D.outside k,
    fun l => D.outside (f l),D.nonzero k,fun l => D.nonzero (f l),
    D.clock_inj.comp (Fin.castLE_injective _),fun l eq => ?_,?_⟩
  · exact (ne_of_gt (show f l < k from l.isLt)) (D.clock_inj eq)
  · intro j jg ej jn
    obtain ⟨t,tk,te⟩ := D.cover k j jg ej jn
    exact ⟨⟨t.val,tk⟩,te.symm⟩

theorem ExteriorStep.scalar_prefix {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m)
    {P : K[X]} (p0 : P.eval 0=0) (roots : ∀ j, P.eval (nodes A (D.old j))=0) :
    ∀ j < D.next, C.scalar P j=0 := by
  intro j jl
  by_cases ej : C.mask j=0
  · rw [C.scalar_outside P ej]
    by_cases cj : nodes A j=0
    · rw [cj,p0]
    · obtain ⟨l,hl⟩ := D.cover j jl ej cj
      rw [hl,roots l]
  · exact C.scalar_inside P ej

noncomputable abbrev ExteriorStep.hull {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m) : K[X] :=
  Lagrange.nodal Finset.univ (nodes A ∘ D.old)

theorem ExteriorStep.hull_degree {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m) :
    D.hull.natDegree=m := by rw [Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin]

theorem ExteriorStep.hull_old {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m) (i : Fin m) :
    D.hull.eval (nodes A (D.old i))=0 :=
  Lagrange.eval_nodal_at_node (v:=nodes A ∘ D.old) (Finset.mem_univ i)

theorem ExteriorStep.hull_next {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m) :
    D.hull.eval (nodes A D.next)≠0 :=
  Lagrange.eval_nodal_not_at_node (fun i _ e => D.fresh i e)

theorem CoreMask.scalar_treeSpace (C : CoreMask A U) (P : K[X]) {j : ℕ} (deg : P.natDegree≤j)
    (paid : U≤zeroSpace A j) : C.scalar P∈treeSpace A j := by
  have h := (treeSpace A j).add_mem (zeroSpace_le_treeSpace A j (paid (C.scalar_defect P)))
    (evalNodes_mem_treeSpace A P deg)
  simpa only [sub_add_cancel] using h

theorem prefix_zero_mulVec_through (ha : A.IsLowerTriangular) {v : Fin s → K} {i : Fin s}
    (pre : ∀ j < i, v j=0) (a0 : A i i=0) {j : Fin s} (ji : j ≤ i) :
    mat A v j=0 := by
  rw [mat_apply,lowerTriangular_mulVec_pivot ha j v (fun k h => pre k (h.trans_le ji))]
  rcases lt_or_eq_of_le ji with h|rfl
  · rw [pre _ h,mul_zero]
  · rw [a0,zero_mul]

theorem exterior_pure_zero (C : CoreMask A U) {j n : ℕ}
    (flag : zeroSpace A j≤chain (diag (nodes A)) U w n)
    {v : Fin s → K} (hv : v∈zeroSpace A j) {i : Fin s} (out : C.mask i=0) (wi : w i=0) :
    v i=0 := by
  obtain ⟨r,hr,Q,_,eq⟩ := HeadFiber.exists_poly (flag hv)
  rw [eq,Pi.add_apply,C.outside_zero out hr,RKCert.Endpoint.weightedEval_apply,wi,mul_zero,add_zero]

variable [CharZero K]

/-- Actual primitive payment at the next grade with arbitrary genuine
pure modifications of the input. -/
theorem primitive_residual_native {P : K[X]} {v : Fin s → K} {j : ℕ}
    (deg : P.natDegree≤j) (pic : v-evalNodes A P∈zeroSpace A j) :
    evalNodes A (primitive P)-mat A v∈zeroSpace A (j+1) := by
  let F := zeroSpace A (j+1)
  have hv : mat A (v-evalNodes A P)∈F := mat_zeroSpace_charZero A j pic
  rw [map_sub] at hv
  have hf : mat A (evalNodes A P)-evalNodes A (primitive P) ∈ F := primitive_defect A P deg
  convert F.neg_mem (F.add_mem hv hf) using 1
  abel

/-- The first three nonzero exterior debuts cannot have zero head. A
single origin-cleared nodal polynomial and three paid local primitive
tests detect the alleged absence over a characteristic-zero field. -/
theorem early_exterior_head (ha : A.IsLowerTriangular) (ho : HasOrder A b p) (pay : 6≤p)
    {C : CoreMask A U} (inside : U≤zeroSpace A 3)
    {m : ℕ} (D : ExteriorStep C m) (small : m≤2)
    (flag5 : zeroSpace A 5≤chain (diag (nodes A)) U w 2)
    (flag6 : zeroSpace A 6≤chain (diag (nodes A)) U w 3) :
    w D.next≠0 := by
  intro w0
  let H := D.hull
  have hd : H.natDegree≤2 := D.hull_degree.trans_le small
  have mon : H.Monic := Lagrange.nodal_monic
  have deg (r : ℕ) : (X^(1+r)*H).natDegree≤3+r := by
    apply natDegree_mul_le.trans
    rw [natDegree_X_pow]; omega
  have pre (r : ℕ) : ∀ j < D.next, C.scalar (X^(1+r)*H) j=0 := by
    apply D.scalar_prefix (by simp)
    intro i
    simp [H,D.hull_old i]
  let v := C.scalar (X*H)
  have pv : ∀ j < D.next, v j=0 := by simpa [v] using pre 0
  have dg : (X*H).natDegree≤3 := by simpa using deg 0
  have nv : v D.next≠0 := by
    unfold v
    rw [C.scalar_outside _ D.next_out,eval_mul,eval_X]
    exact mul_ne_zero D.next_nz D.hull_next
  have vm := volterra_treeSpace ho 3 (by omega) (C.scalar_treeSpace _ dg inside)
  have vm' : volterra A v∈zeroSpace A 5 := vm
  have z := exterior_pure_zero C flag5 vm' D.next_out w0
  rw [volterra_pivot ha _ _ pv] at z
  have a0 : A D.next D.next=0 :=
    sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp z).resolve_right nv))
  apply mon.ne_zero (HeadFiber.detect_short_primitive_tests ho pay H hd _ D.next_nz ?_)
  intro r
  let f := X^(1+r.val)*H
  let v := C.scalar f
  have df : f.natDegree≤5 := (deg r.val).trans (by have := r.isLt; omega)
  have h : v-evalNodes A f∈zeroSpace A 5 :=
    zeroSpace_mono A (by decide : 3≤5) (inside (C.scalar_defect f))
  have obs := exterior_pure_zero C flag6 (primitive_residual_native df h) D.next_out w0
  rw [Pi.sub_apply,evalNodes_apply,prefix_zero_mulVec_through ha (pre r.val) a0 le_rfl,sub_zero] at obs
  exact obs

omit [CharZero K] in
/-- The third and fourth exterior diagonals have actually been refunded.
The origin-cleared tableau input vanishes before the new clock; m old
nonzero head values force a degree < m Volterra remainder to vanish. -/
theorem exterior_refund (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {C : CoreMask A U} {m : ℕ} (D : ExteriorStep C m) (pay : m+3≤p)
    (inside : U≤zeroSpace A (m+1))
    (flag : zeroSpace A (m+3)≤chain (diag (nodes A)) U w m)
    (dirty : ∀ j, w (D.old j)≠0) : A D.next D.next=0 := by
  let H := D.hull
  let f := X*H
  let v := C.scalar f
  have d : f.natDegree≤m+1 := by
    apply natDegree_mul_le.trans
    rw [natDegree_X,D.hull_degree,Nat.add_comm]
  have pre : ∀ j < D.next, v j=0 := D.scalar_prefix (by simp [f])
    (fun i => by simp [f,H,D.hull_old i])
  have vn : v D.next≠0 := by
    rw [show v=C.scalar f from rfl,C.scalar_outside f D.next_out,show f=X*H from rfl,eval_mul,eval_X]
    exact mul_ne_zero D.next_nz D.hull_next
  have z : volterra A v∈zeroSpace A (m+3) :=
    volterra_treeSpace ho (m+1) (by omega) (C.scalar_treeSpace _ d inside)
  obtain ⟨r,hr,Q,dq,eq⟩ := HeadFiber.exists_poly (flag z)
  have roots (j : Fin m) : Q.eval ((nodes A ∘ D.old) j)=0 := by
    have rj := congrFun eq (D.old j)
    rw [volterra_pivot ha _ _ (fun i lt => pre i (lt.trans (D.earlier j))),pre _ (D.earlier j),
      mul_zero,Pi.add_apply,C.outside_zero (D.old_out j) hr,zero_add,RKCert.Endpoint.weightedEval_apply] at rj
    exact (mul_eq_zero.mp rj.symm).resolve_right (dirty j)
  have q0 : Q=0 := eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ D.distinct.injOn
    (by simpa only [Finset.card_univ,Fintype.card_fin] using dq) (fun j _ => roots j)
  have h := congrFun eq D.next
  rw [volterra_pivot ha _ _ pre,Pi.add_apply,C.outside_zero D.next_out hr,RKCert.Endpoint.weightedEval_apply,
    q0,eval_zero,zero_mul,add_zero] at h
  exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_right vn))

end RKResearch.Certified.Graded.OuterHead
