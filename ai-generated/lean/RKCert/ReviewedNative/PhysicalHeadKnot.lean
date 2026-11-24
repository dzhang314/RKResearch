module

public import RKCert.ReviewedNative.NativeLiveCore
public import RKCert.ReviewedNative.OrderedNodalGain

@[expose] public section

/-! # The first actually omitted physical knot

An omitted row is chosen chronologically from the original matrix. Both
its cutoff and the associated mesh zero follow from the same paid
subspaces. No injectivity of the stage clocks is presumed. -/
namespace RKResearch.Certified.Graded

open Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s j m n N : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}
variable {U V : Submodule K (Fin s → K)} {w : Fin s → K} {G P : K[X]}

/-- Shift a physically supported polynomial by paid head multipliers,
then test at the first row where its evaluation escapes that support.
The same row zeros the already-paid mesh and all displayed primitives. -/
theorem physical_head_knot (ha : ∀ i t, i≤t → A i t=0)
    (stable : U.map (diag (nodes A))≤U)
    (closed : ∀ u∈U, ∀ v∈U, u*v∈U)
    (dis : ∀ i, LiveCore.live U i → w i=0)
    (repr : ∀ i, w i≠0 → w i=P.eval (nodes A i))
    (pn : P≠0) (fit : P.natDegree+m≤j)
    (core : U≤V)
    (paid : ∀ R : K[X], R.natDegree≤m → weightedEval (nodes A) w R∈V)
    (sep : ∀ R : K[X], R.natDegree≤j → evalNodes A R∈V → R=0)
    (moves : V≤(chain (diag (nodes A)) U w n).comap (mat A))
    (defects : zeroSpace A (j+1)≤chain (diag (nodes A)) U w n)
    (mesh : evalNodes A G∈chain (diag (nodes A)) U w N)
    (Q : K[X]) (qn : Q≠0) (qd : Q.natDegree≤m) :
    ∃ k : Fin s, ¬LiveCore.live U k ∧ w k=0 ∧ G.eval (nodes A k)=0 ∧
      (Q*P).eval (nodes A k)≠0 ∧
      ∀ R : K[X], R.natDegree+Q.natDegree≤m →
        (formalPrimitive (R*(Q*P))).eval (nodes A k)=0 := by
  classical
  obtain ⟨e,he,indicator⟩ := LiveCore.exists_live_indicator U closed
  let c := nodes A
  let F := Q*P
  let adjust (R : K[X]) : Fin s → K := weightedEval c w (R*Q)+weightedEval c e (R*F)
  let residual := evalNodes A F-adjust 1
  have adj (R : K[X]) (d : R.natDegree+Q.natDegree≤m) : adjust R∈V := by
    apply V.add_mem (paid _ (natDegree_mul_le.trans d))
    apply core
    have eq : weightedEval c e (R*F) = fun i => (R*F).eval (nodes A i)*e i := by
      ext i
      simp [c]
    rw [eq]
    exact clock_function_mem (fun _ h => stable (Submodule.mem_map_of_mem h))
      (fun x => (R*F).eval x) he
  have adjOne : adjust 1∈V := adj 1 (by simpa using qd)
  have residual_ne : residual≠0 := by
    intro h
    have eq : evalNodes A F=adjust 1 := sub_eq_zero.mp h
    have pd : F.natDegree≤j := natDegree_mul_le.trans (by omega)
    exact mul_ne_zero qn pn (sep F pd (eq.symm ▸ adjOne))
  let J := Finset.univ.filter (fun i => residual i≠0)
  have hJ : J.Nonempty := by
    by_contra h
    apply residual_ne
    ext i
    by_contra ne
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne⟩⟩
  let k := J.min' hJ
  have kn : residual k≠0 := (Finset.mem_filter.mp (J.min'_mem hJ)).2
  have before (i : Fin s) (hi : i<k) : residual i=0 := by
    by_contra ne
    exact (not_le_of_gt hi) (J.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne⟩))
  have dead : ¬LiveCore.live U k := by
    intro h
    apply kn
    simp [residual,adjust,indicator,h,dis k h,c]
  have wk : w k=0 := by
    by_contra h
    apply kn
    simp [residual,adjust,indicator,dead,repr k h,F,c]
  have fk : F.eval (c k)≠0 := by
    intro h
    apply kn
    simpa [residual,adjust,indicator,dead,wk,c] using h
  have cut {l : ℕ} {v : Fin s → K} (hv : v∈chain (diag c) U w l) : v k=0 := by
    obtain ⟨u,hu,H,_,rfl⟩ := HeadFiber.exists_poly hv
    simp [LiveCore.val_eq_zero_of_not_live dead hu,wk]
  refine ⟨k,dead,wk,cut mesh,fk,?_⟩
  intro R rd
  let T := R*F
  have td : T.natDegree≤j := by
    have h := natDegree_mul_le (p:=R*Q) (q:=P)
    have l := natDegree_mul_le (p:=R) (q:=Q)
    change (R*(Q*P)).natDegree≤j
    rw [←mul_assoc]
    omega
  have eq : evalNodes A T-adjust R=weightedEval c residual R := by
    ext i
    simp only [Pi.sub_apply,Pi.add_apply,weightedEval_apply,evalNodes_apply,residual,
      adjust,T,one_mul,eval_mul,c]
    ring
  have az : mat A (evalNodes A T-adjust R) k=0 := by
    rw [eq]
    apply causal_mat ha
    intro i hi
    simp [before i hi]
  have z : evalNodes A (primitive T)-mat A (evalNodes A T-adjust R) ∈
      chain (diag c) U w n := by
    rw [map_sub,show evalNodes A (primitive T)-(mat A (evalNodes A T)-mat A (adjust R)) =
      -(mat A (evalNodes A T)-evalNodes A (primitive T))+mat A (adjust R) by abel]
    exact (chain (diag c) U w n).add_mem
      ((chain (diag c) U w n).neg_mem (defects (primitive_defect A T td))) (moves (adj R rd))
  have f := cut z
  simpa only [Pi.sub_apply,evalNodes_apply,az,sub_zero,formalPrimitive_eq_native] using f


/-- A certificate that the same paid mesh has two distinct nonzero
chronological knots, each omitted from the core/head support. -/
structure PhysicalHeadKnots (A : Matrix (Fin s) (Fin s) K)
    (U : Submodule K (Fin s → K)) (w : Fin s → K) (G P : K[X]) (i t : Fin s) : Prop where
  firstOmitted : ¬LiveCore.live U i ∧ w i=0
  secondOmitted : ¬LiveCore.live U t ∧ w t=0
  firstNonzero : nodes A i≠0
  secondNonzero : nodes A t≠0
  different : nodes A t≠nodes A i
  firstHead : P.eval (nodes A i)≠0
  secondHead : P.eval (nodes A t)≠0
  firstMesh : G.eval (nodes A i)=0
  secondMesh : G.eval (nodes A t)=0
  firstTest : ∀ R : K[X], R.natDegree≤2 →
    (formalPrimitive (R*(X*P))).eval (nodes A i)=0
  secondTest : ∀ R : K[X], R.natDegree≤1 →
    (formalPrimitive (R*(X*(X-C (nodes A i))*P))).eval (nodes A t)=0

omit [CharZero K] in
/-- The filters X and X(X-u) guarantee nonzero, distinct physical clocks;
the same mesh is retained under both tests. -/
theorem physical_head_knots_three_two
    (test : ∀ Q : K[X], Q≠0 → Q.natDegree≤3 →
      ∃ k : Fin s, ¬LiveCore.live U k ∧ w k=0 ∧ G.eval (nodes A k)=0 ∧
        (Q*P).eval (nodes A k)≠0 ∧
        ∀ R : K[X], R.natDegree+Q.natDegree≤3 →
          (formalPrimitive (R*(Q*P))).eval (nodes A k)=0) :
    ∃ i t : Fin s, PhysicalHeadKnots A U w G P i t := by
  obtain ⟨i,hi,wi,gi,pi,z1⟩ := test X X_ne_zero (by rw [natDegree_X];omega)
  let u := nodes A i
  have p1 : u*P.eval u≠0 := by simpa [u] using pi
  let Q : K[X] := X*(X-C u)
  have qn : Q≠0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero u)
  have qd : Q.natDegree=2 := by
    dsimp only [Q]
    rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero u),natDegree_X,natDegree_X_sub_C]
  obtain ⟨t,ht,wt,gt,pt,z2⟩ := test Q qn (by omega)
  let v := nodes A t
  have p2 : v*(v-u)*P.eval v≠0 := by simpa [v,Q] using pt
  have uv : u≠0 := fun e => p1 (by rw [e,zero_mul])
  have vn : v≠0 := fun e => p2 (by rw [e,zero_mul,zero_mul])
  have ne : v≠u := fun e => p2 (by rw [e,sub_self,mul_zero,zero_mul])
  have nu : P.eval u≠0 := fun e => p1 (by rw [e,mul_zero])
  have nv : P.eval v≠0 := fun e => p2 (by rw [e,mul_zero])
  exact ⟨i,t,⟨⟨hi,wi⟩,⟨ht,wt⟩,uv,vn,ne,nu,nv,gi,gt,
    fun R h => z1 R (by rw [natDegree_X];omega),fun R h => z2 R (by omega)⟩⟩

omit [CharZero K] in
/-- If the mesh has the actual physical multiplier as a factor, these
same two knots lie on its complement, not on the multiplier. -/
theorem PhysicalHeadKnots.complementary_roots {i t : Fin s}
    (B : PhysicalHeadKnots A U w G P i t) {Q : K[X]} (eq : G=P*Q) :
    Q.eval (nodes A i)=0 ∧ Q.eval (nodes A t)=0 := by
  have hi := B.firstMesh
  have ht := B.secondMesh
  rw [eq,eval_mul] at hi ht
  exact ⟨(mul_eq_zero.mp hi).resolve_left B.firstHead,(mul_eq_zero.mp ht).resolve_left B.secondHead⟩

end RKResearch.Certified.Graded
