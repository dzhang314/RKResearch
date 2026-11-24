module

public import RKCert.StagePrimitives
public import RKCert.BackwardTerminal
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Dual

@[expose] public section

/-! # Single-node annihilator rows and chronological completion -/
namespace RKCert.Paired
open Polynomial
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}

theorem rowL_surj : Function.Surjective (rowL (K:=K) (s:=s)) :=
  (dotProductEquiv K (Fin s)).surjective

theorem row_annih_test (U : Submodule K (Vec K s)) (v : Vec K s)
    (h : ∀ w ∈ annih U, row w v=0) : v ∈ U := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U v).mp
  intro f hf
  obtain ⟨w,rfl⟩ := rowL_surj f
  exact h w hf

theorem row_add_col (u w v : Vec K s) :
    row (u+w) v = row u v + row w v :=
  congrArg (fun f : Module.Dual K (Vec K s) => f v) (rowL.map_add u w)

theorem row_sub_col (u w v : Vec K s) :
    row (u-w) v = row u v - row w v :=
  congrArg (fun f : Module.Dual K (Vec K s) => f v) (rowL.map_sub u w)

theorem row_smul_col (a : K) (u v : Vec K s) :
    row (a • u) v = a * row u v :=
  congrArg (fun f : Module.Dual K (Vec K s) => f v) (rowL.map_smul a u)

/-- Every polynomial in an invariant diagonal operator preserves the subspace. -/
theorem evalDiag_mem {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    (hC : ∀ v ∈ U, diag (nodes A) v ∈ U) (P : Polynomial K)
    {v : Vec K s} (hv : v∈U) : diag (evalNodes A P) v ∈ U := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hh : diag (evalNodes A (P+Q)) v = diag (evalNodes A P) v + diag (evalNodes A Q) v := by
      ext i; simp [add_mul]
    rw [hh]; exact U.add_mem hP hQ
  | monomial k a =>
    have hx (k : ℕ) : diag (evalNodes A (X^k)) v ∈ U := by
      induction k with
      | zero =>
        have h : diag (evalNodes A (X^0 : Polynomial K)) v = v := by ext i; simp
        rwa [h]
      | succ k ih =>
        have he : diag (evalNodes A (X^(k+1))) v =
            diag (nodes A) (diag (evalNodes A (X^k)) v) := by
          ext i; simp [pow_succ',mul_assoc]
        rw [he]; exact hC _ ih
    have he : diag (evalNodes A (monomial k a)) v = a • diag (evalNodes A (X^k)) v := by
      ext i; simp [mul_assoc]
    rw [he]; exact U.smul_mem a (hx k)

noncomputable def nodeMask (A : Fin s → Fin s → K) (x : K) : Vec K s := by
  classical
  exact fun i => if nodes A i=x then 1 else 0

theorem mask_apply (A : Fin s → Fin s → K) (x : K) (i : Fin s) :
    nodeMask A x i = if nodes A i=x then 1 else 0 := by
  classical
  rfl

theorem nodeMask_mem {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    (hC : ∀ v ∈ U, diag (nodes A) v ∈ U) (x : K) {v : Vec K s} (hv : v∈U) :
    diag (nodeMask A x) v ∈ U := by
  classical
  let T : Finset K := Finset.univ.image (nodes A)
  let f : K → K := fun z => if z=x then 1 else 0
  let P := Lagrange.interpolate T id f
  have hEq : evalNodes A P = nodeMask A x := by
    ext i
    have hi : nodes A i ∈ T := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [evalNodes_apply,mask_apply]
    exact Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hi
  rw [← hEq]
  exact evalDiag_mem hC P hv

theorem nodeMask_annih {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    (hC : ∀ v ∈ U, diag (nodes A) v ∈ U) (x : K) {w : Vec K s} (hw : w∈annih U) :
    diag (nodeMask A x) w ∈ annih U := by
  apply mem_annih.mpr
  intro v hv
  rw [row_flip_diag]
  exact mem_annih.mp hw _ (nodeMask_mem hC x hv)

theorem eval_row_on_node {A : Fin s → Fin s → K} {x : K} {w : Vec K s}
    (hw : ∀ i, nodes A i≠x → w i=0) (P : Polynomial K) :
    row w (evalNodes A P) = P.eval x * row w 1 := by
  simp only [row_apply,evalNodes_apply,Pi.one_apply,mul_one,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : nodes A i=x
  · rw [h,mul_comm]
  · simp [hw i h]

/-- Every row pairing is the sum of its single-node blocks. -/
theorem row_split_nodes (A : Fin s → Fin s → K) (w v : Vec K s) :
    row w v = ∑ x ∈ (Finset.univ.image (nodes A)), row (diag (nodeMask A x) w) v := by
  classical
  let T := Finset.univ.image (nodes A)
  change row w v = ∑ x ∈ T, row (diag (nodeMask A x) w) v
  simp only [row_apply,diag_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (nodes A i)]
  · simp [mask_apply]
  · intro j _ hj; simp [mask_apply,Ne.symm hj]
  · intro h; exact False.elim (h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

/-- A represented node has a row on that node of total mass one, annihilating
the selected defects, with the supplied last nonzero chronological coordinate. -/
structure NodeCompletion (A : Fin s → Fin s → K) (U : Submodule K (Vec K s))
    (x : K) (k : Fin s) (w : Vec K s) : Prop where
  annihilates : w∈annih U
  mass : row w 1=1
  onNode : ∀ i, nodes A i ≠ x → w i=0
  lastNonzero : w k≠0
  laterZero : ∀ i, k < i → w i=0

theorem NodeCompletion.eval {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    {x : K} {k : Fin s} {w : Vec K s} (h : NodeCompletion A U x k w) (P : Polynomial K) :
    row w (evalNodes A P) = P.eval x := by rw [eval_row_on_node h.onNode,h.mass,mul_one]

theorem NodeCompletion.node_at_last {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    {x : K} {k : Fin s} {w : Vec K s} (h : NodeCompletion A U x k w) :
    nodes A k=x := by
  by_contra hn; exact h.lastNonzero (h.onNode k hn)

theorem exists_nodeCompletion {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    {x : K} {w : Vec K s} (hw : w∈annih U) (hon : ∀ i, nodes A i≠x → w i=0)
    (hM : row w 1≠0) :
    ∃ k : Fin s, NodeCompletion A U x k ((row w 1)⁻¹ • w) := by
  classical
  have hex : ∃ i, w i≠0 := by
    by_contra! h
    exact hM (by simp [row_apply,h])
  let T := Finset.univ.filter (fun i : Fin s => w i≠0)
  obtain ⟨i,hi⟩ := hex
  have hT : T.Nonempty := ⟨i,by simpa [T] using hi⟩
  let k := T.max' hT
  have hk : w k≠0 := by
    have h := T.max'_mem hT
    change k∈T at h
    simpa [T] using h
  refine ⟨k,⟨(annih U).smul_mem _ hw,?_,?_,?_,?_⟩⟩
  · rw [row_smul_col,inv_mul_cancel₀ hM]
  · intro j hj; simp [hon j hj]
  · exact mul_ne_zero (inv_ne_zero hM) hk
  · intro j hj
    have he : w j=0 := by
      by_contra h
      exact (not_le_of_gt hj) (T.le_max' j (by simpa [T] using h))
    simp [he]

/-- An annihilating row only sees represented nodes. The stronger variant
tracks the support: if every coordinate at/after k is zero, the row can
only see a representation completed strictly before k. -/
theorem row_vanish_by_completions {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    (hC : ∀ v ∈ U, diag (nodes A) v ∈ U) (P : Polynomial K) (S : Fin s → Prop)
    {w : Vec K s} (hw : w∈annih U) (hS : ∀ i, w i≠0 → S i)
    (hP : ∀ x k l, NodeCompletion A U x k l → S k → P.eval x=0) :
    row w (evalNodes A P)=0 := by
  classical
  rw [row_split_nodes A]
  apply Finset.sum_eq_zero
  intro x _
  have hon (i) (hi : nodes A i≠x) : diag (nodeMask A x) w i=0 := by simp [mask_apply,hi]
  rw [eval_row_on_node hon]
  by_cases hn : row (diag (nodeMask A x) w) 1=0
  · simp [hn]
  · obtain ⟨k,h⟩ := exists_nodeCompletion (nodeMask_annih hC x hw) hon hn
    have hk : w k≠0 := by
      intro he
      apply h.lastNonzero
      simp [he]
    rw [hP _ _ _ h (hS _ hk),zero_mul]

end RKCert.Paired
