module

public import RKCert.ReviewedNative.LocalLinearSevenRefund

@[expose] public section

/-! # Standalone early-core and output-trace payments at the edge

Core preservation charges `r-1`, not `r`. The b-trace also deserves its
own budget independently of the τ trace. In particular this module does
not claim the full two-trace conclusion at grade six with r=2,h=7. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] {s p h r j : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ f : Fin s→K}
variable {U : Submodule K (Fin s→K)}

set_option maxRecDepth 3500
set_option maxHeartbeats 950000

/-- Diagonal multiplication by a defect preserves the early reverse core
at the exact primitive grade of that core, including the one-grade border. -/
theorem local_core_preserved_at_paid_border (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ) (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (rh : r≤h) (pay : (r-1)+j+(h+1)+2≤p) (hf : f∈zeroSpace A j) :
    U.map (diag f)≤U := by
  let y := reflectedClock A
  let S : Finset K := Finset.univ.image y
  rintro _ ⟨v,hv,rfl⟩
  have mask := clock_mask_invariant (fun _ hv=>F.invariant (Submodule.mem_map_of_mem hv))
  have blocks (z : K) : diag f (blockMask y z v)∈U := by
    have src : blockMask y z v∈primitiveBack A b (r-1) := F.core.le (mask _ _ hv)
    have test := primitive_shifted_column_annih ho (n:=r-1) (j:=j) (g:=h+1)
      (k:=0) (by omega) src (zeroSpace_le_treeSpace A j hf)
    rw [←full] at test
    have e : (diag y^0) (blockMask y z v*f)=diag f (blockMask y z v) := by
      simp only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
      ext i; simp [mul_comm]
    change (diag y^0) (blockMask y z v*f)∈primitiveBack A b h at test
    rw [e] at test
    apply F.local_mem_core rh test (y:=z)
    intro i other
    have off : y i≠z := other
    simp [blockMask,off]
  have sum : (∑ z∈S,blockMask y z v)=v := by
    ext i
    rw [Finset.sum_apply,Finset.sum_eq_single_of_mem (y i) (Finset.mem_image_of_mem y (Finset.mem_univ i))]
    · simp [blockMask]
    · intro z _ ne; simp [blockMask,Ne.symm ne]
  rw [←sum,map_sum]
  exact U.sum_mem (fun z _=>blocks z)

private theorem weighted_local_head_annih (F : LocalLinearBand A b h r U τ) (P : K[X]) :
    weightedEval (reflectedClock A) τ P∈annih U := by
  apply mem_annih.mpr
  intro w hw
  have z := mem_annih.mp F.headOrthogonal _ (reflected_clock_weighted_core F.invariant hw P)
  rw [row_apply,dotProduct] at z ⊢
  convert z using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedEval_apply]
  ring

private theorem local_core_in_paid_reverse (F : LocalLinearBand A b h r U τ) (rh : r≤h) :
    U≤primitiveBack A b h := F.core.le.trans
      ((monotone_nat_of_le_succ (adjointFlag_le_succ _)) (by omega))

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Output-weighted trace alone, valid without the paid τ-product window. -/
theorem local_linear_weight_only_trace (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ) (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (rh : r≤h) (pay : 2*h+3≤p) (jc : j≤h+1) (hf : f∈zeroSpace A j) :
    ∃ u∈U, ∃ P : K[X], (P=0∨P.natDegree+r+1≤j) ∧
      b*f=u+weightedEval (reflectedClock A) τ P := by
  let y := reflectedClock A
  let D := diag y
  let L := primitiveBack A b h
  have inside := local_core_in_paid_reverse F rh
  have shifts (k : ℕ) (hk : k≤h+1-j) : (D^k) (b*f)∈L := by
    change (diag (reflectedClock A)^k) (b*f)∈primitiveBack A b h
    rw [full]
    exact output_shifted_defect_annih ho (by omega) hf
  have zero : b*f∈L := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using shifts 0 (by omega)
  change b*f∈primitiveBack A b h at zero
  rw [F.band h rh le_rfl] at zero
  obtain ⟨u,hu,Q,_,form⟩ := HeadFiber.exists_poly zero
  let v := weightedEval y τ Q
  have fits (k : ℕ) (hk : k≤h+1-j) :
      ∃ R : K[X], R.natDegree≤h-r ∧ weightedEval y τ R=(fun i=>y i^k*v i) := by
    have moved : (D^k) u=weightedEval y u (X^k) := by
      ext i
      simp only [D, HeadFiber.clock_power_value, weightedEval_apply,eval_pow,eval_X]
    have uSh : (D^k) u∈U := by
      rw [moved]
      exact reflected_clock_weighted_core F.invariant hu _
    have base := shifts k hk
    rw [form,map_add] at base
    have sub := (L).sub_mem base (inside uSh)
    have paid : (D^k) v∈primitiveBack A b h := by
      simpa only [add_sub_cancel_left] using sub
    have eq : (D^k) v=weightedEval y τ (X^k*Q) := by
      ext i
      simp only [D,v,HeadFiber.clock_power_value,weightedEval_apply,eval_mul,eval_pow,eval_X]
      ring
    have po : (D^k) v∈annih U := by
      rw [eq]
      exact weighted_local_head_annih F _
    rw [F.band h rh le_rfl] at paid
    obtain ⟨w,hw,R,rd,re⟩ := HeadFiber.exists_poly paid
    have test := (annih U).sub_mem po (weighted_local_head_annih F R)
    rw [re,add_sub_cancel_right] at test
    have wz := eq_zero_of_self_row_zero (mem_annih.mp test _ hw)
    have db : R.natDegree≤h-r := by
      by_cases rz : R=0
      · simp [rz]
      have d := (natDegree_lt_iff_degree_lt rz).mpr rd
      omega
    refine ⟨R,db,?_⟩
    rw [wz,zero_add] at re
    rw [←re]
    ext i
    exact HeadFiber.clock_power_value y v k i
  have many : (h-r)+1 < (weightedSites y τ).card := by
    have z : h+1-r < (weightedSites y τ).card := F.site_count
    omega
  obtain ⟨P,degree,eq⟩ := Thin.trace_degree_from_shifts (h:=h-r) (k:=h+1-j) many fits
  refine ⟨u,hu,P,?_,?_⟩
  · rcases degree with z|d
    · exact Or.inl z
    · exact Or.inr (by omega)
  · rw [eq]
    exact form

/-- Each extra same-grade ordinary power refunds one degree on the actual
output-weighted trace. At r=2,j=6 and two powers this leaves degree ≤1. -/
theorem local_linear_weight_only_power_refund (ho : HasOrder p A b)
    (F : LocalLinearBand A b h r U τ) (full : primitiveBack A b h=annih (treeSpace A (h+1)))
    (rh : r≤h) (pay : 2*h+3≤p) (jc : j≤h+1) (low : r+1≤j)
    (k : ℕ) (powers : ∀ a≤k, (diag (nodes A)^a) f∈zeroSpace A j) :
    ∃ u∈U, ∃ P : K[X], (P=0∨P.natDegree+k+r+1≤j) ∧
      b*f=u+weightedEval (reflectedClock A) τ P := by
  let y := reflectedClock A
  let C := diag (nodes A)
  let H : K[X] := 1-X
  have x (i : Fin s) : H.eval (y i)=nodes A i := by simp [H,y,reflectedClock]
  have initial : f∈zeroSpace A j := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using powers 0 (by omega)
  obtain ⟨u,hu,Q,_,form⟩ := local_linear_weight_only_trace ho F full rh pay jc initial
  let v := weightedEval y τ Q
  have fits (a : ℕ) (ha : a≤k) :
      ∃ P : K[X], P.natDegree≤j-(r+1) ∧ weightedEval y τ P=(fun i=>(H.eval (y i))^a*v i) := by
    obtain ⟨w,hw,P,pd,rep⟩ := local_linear_weight_only_trace ho F full rh pay jc (powers a ha)
    let rhs := weightedEval y τ (H^a*Q)
    let lhs := weightedEval y τ P
    have act : weightedEval y (b*f) (H^a)=b*(C^a) f := by
      ext i
      simp only [C,weightedEval_apply,eval_pow,x,Pi.mul_apply,HeadFiber.clock_power_value]
      ring
    have aa : weightedEval y (b*f) (H^a)=w+lhs := act.trans rep
    have bb : weightedEval y (b*f) (H^a)=weightedEval y u (H^a)+rhs := by
      rw [form]
      ext i
      simp only [rhs,weightedEval_apply,eval_mul,eval_pow,Pi.add_apply]
      ring
    have mismatch : lhs-rhs=weightedEval y u (H^a)-w := by
      calc
        _=(w+lhs)-w-rhs := by abel
        _=(weightedEval y u (H^a)+rhs)-w-rhs := by rw [←aa,bb]
        _=_ := by abel
    have inU : lhs-rhs∈U := mismatch.symm ▸ U.sub_mem
      (reflected_clock_weighted_core F.invariant hu _) hw
    have orth : lhs-rhs∈annih U := (annih U).sub_mem
      (weighted_local_head_annih F _) (weighted_local_head_annih F _)
    have equal := sub_eq_zero.mp (eq_zero_of_self_row_zero (mem_annih.mp orth _ inU))
    refine ⟨P,?_,?_⟩
    · rcases pd with z|d
      · simp [z]
      · omega
    · change lhs=_
      rw [equal]
      ext i
      simp only [rhs,v,weightedEval_apply,eval_mul,eval_pow]
      ring
  have many : j-(r+1)+1<(weightedSites y τ).card := by
    have z : h+1-r < (weightedSites y τ).card := F.site_count
    omega
  obtain ⟨P,degree,eq⟩ := Thin.trace_degree_from_affine_shifts H Thin.one_sub_X_natDegree many fits
  refine ⟨u,hu,P,?_,?_⟩
  · rcases degree with z|d
    · exact Or.inl z
    · exact Or.inr (by omega)
  · rw [eq]
    exact form

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
