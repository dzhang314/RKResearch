module

public import RKCert.ReviewedNative.LocalLinearHiddenKernel

@[expose] public section

/-! # Paid transfer from the local hidden tree span to genuine defects

The true local reverse flag kills each hidden column. The output-weighted
column belongs to the small core, so the ordinary monomial probes vanish.
The reviewed polynomial-plus-defect decomposition and exact Cauchy payment
then remove its entire ordinary polynomial trace. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Polynomial Module RKCert.Endpoint
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p h r : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ : Fin s→K}
variable {U : Submodule K (Fin s→K)}

set_option maxRecDepth 3500
set_option maxHeartbeats 750000

theorem hiddenKernel_forward_clock_of_band (F : LocalLinearBand A b h r U τ) :
    (hiddenKernel b τ U).map (diag (nodes A))≤hiddenKernel b τ U := by
  apply hiddenKernel_clock
  rintro _ ⟨u,hu,rfl⟩
  have e : diag (nodes A) u=u-diag (reflectedClock A) u := by
    ext i
    simp only [diag_apply,Pi.sub_apply,reflectedClock,Pi.one_apply]
    ring
  rw [e]
  exact U.sub_mem hu (F.invariant (Submodule.mem_map_of_mem hu))

theorem hiddenKernel_le_paid_tree (F : LocalLinearBand A b h r U τ) (rh : r≤h)
    (full : primitiveBack A b h=annih (treeSpace A (h+1))) :
    hiddenKernel b τ U≤treeSpace A (h+1) := by
  intro v hv
  obtain ⟨ht,_,hu⟩ := mem_hiddenKernel.mp hv
  rw [←annih_annih (treeSpace A (h+1)),←full]
  apply mem_annih.mpr
  intro w hw
  rw [F.band h rh le_rfl] at hw
  obtain ⟨u,hU,Q,_,eq⟩ := HeadFiber.exists_poly hw
  have vone (z : Fin s→K) (hz : z∈U) : row v z=0 := by
    have prod := hu (Submodule.mem_map_of_mem hz : diag v z∈U.map (diag v))
    have ones : (1 : Fin s→K)∈treeSpace A (h+1) := by
      have e : evalNodes A (1 : K[X])=(1 : Fin s→K) := by ext i; simp
      rw [←e]
      exact evalNodes_mem_treeSpace A _ (by simp)
    have coreIn : U≤primitiveBack A b h := F.core.le.trans
      ((monotone_nat_of_le_succ (adjointFlag_le_succ _)) (by omega))
    have orth : row (diag v z) 1=0 := mem_annih.mp (full.le (coreIn prod)) 1 ones
    simpa only [row_apply,dotProduct,Pi.one_apply,diag_apply,mul_one] using orth
  have two : row v (weightedEval (reflectedClock A) τ Q)=0 := by
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    have e : τ i*v i=0 := congrFun ht i
    simp only [weightedEval_apply]
    rw [show v i*(Q.eval (reflectedClock A i)*τ i)=Q.eval (reflectedClock A i)*(τ i*v i) by ring,
      e,mul_zero]
  rw [eq,map_add,vone u hU,two,add_zero]

/-- At paid degree `h+1` the kernel is a subspace of genuine defects.
The application to order 17 has `h=7`; no ordered-field axiom is used here. -/
theorem hiddenKernel_le_paid_defect (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ) (rh : r≤h)
    (full : primitiveBack A b h=annih (treeSpace A (h+1))) (pay : 2*h+3≤p) :
    hiddenKernel b τ U≤zeroSpace A (h+1) := by
  intro v hv
  let q := h+1
  have charged : 2*q+1≤p := by dsimp [q]; omega
  have prod : b*v∈U := (mem_hiddenKernel.mp hv).2.1
  have inside : U≤primitiveBack A b h := F.core.le.trans
    ((monotone_nat_of_le_succ (adjointFlag_le_succ _)) (by omega))
  have probe0 (k : Fin (q+1)) : probe A b k.val v=0 := by
    have deg : (X^k.val : K[X]).natDegree≤q := by
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ k.isLt
    have paid := mem_annih.mp (full.le (inside prod)) _ (evalNodes_mem_treeSpace A _ deg)
    rw [row_apply,dotProduct] at paid
    simp only [probe,row_apply,dotProduct]
    convert paid using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply,evalNodes_apply,eval_pow,eval_X]
    ring
  have vTree : v∈treeSpace A q := hiddenKernel_le_paid_tree F rh full hv
  rw [treeSpace_coeff_sup ho (by omega : q+1≤p)] at vTree
  obtain ⟨_,⟨a,rfl⟩,w,hw,rfl⟩ := Submodule.mem_sup.mp vTree
  have tests (k : Fin (q+1)) : (∑ j : Fin (q+1),a j/((k.val+j.val+1:ℕ):K))=0 := by
    have e := probe0 k
    have w0 : probe A b k.val w=0 := probe_zeroSpace ho (by have := k.isLt; omega) hw
    rw [map_add,w0,add_zero,probe_coeffEval ho (by have := k.isLt; omega)] at e
    exact e
  have z := moments_detect ho (n:=q+1) (d:=1) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) a tests
  rw [show a=0 from funext z,map_zero,zero_add]
  exact hw

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
