module
public import RKCert.ChronologicalCompression
public import RKCert.BackwardMoments

@[expose] public section

/-! # Actual rooted-tree order after literal chronological class merging
A representative need only be earlier than each member it replaces. The
column and output sums use *all* of the original weights, not a
representative-weight or a clock interpolation. Matching E_q preserves
every tree through order q+1 plus every branched-root tree of order q+2.
-/
namespace RKCert.Paired
open Module
variable {K:Type*} [Field K] {s n q:ℕ}

namespace OwnerCompression

/-- Assign each original row to one earlier retained row. -/
def stencil (owner:Fin s→Fin n) (i:Fin s) (j:Fin n) : K :=
  if owner i=j then 1 else 0

def weightMerge (b:Vec K s) (owner:Fin s→Fin n) (j:Fin n) : K :=
  ∑ i,b i*stencil owner i j

theorem stencil_causal (e:Fin n→Fin s) (owner:Fin s→Fin n)
    (early : ∀ i, e (owner i) ≤ i) :
    ∀i j,i<e j→stencil (K:=K) owner i j=0 := by
  intro i j h
  have e' : owner i≠j := by intro eq;exact (not_le_of_gt h) (by simpa only [eq] using early i)
  simp [stencil,e']

theorem stencil_replay (e:Fin n→Fin s) (owner:Fin s→Fin n)
    {H:Submodule K (Vec K s)} (matched:∀v∈H,∀i,v (e (owner i))=v i) :
    ∀v∈H,∀i,∑ j,stencil (K:=K) owner i j*v (e j)=v i := by
  intro v hv i
  classical
  calc
    _ = v (e (owner i)) := by
      simp only [stencil,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    _ = _ := matched v hv i

theorem merged_output_at (b v:Vec K s) (e:Fin n→Fin s) (owner:Fin s→Fin n) :
    row (weightMerge b owner) (restrictCol e v)=∑ i,b i*v (e (owner i)) := by
  classical
  simp only [row_apply,restrictCol_apply,weightMerge,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]
  rw [←Finset.mul_sum]
  simp only [stencil,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem actual_stage_weights {A:Fin s→Fin s→K} (e:Fin n→Fin s) (owner:Fin s→Fin n)
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) {t:Tree} (ht:t.order≤q+2) :
    restrictCol e (stageWeight A t)=stageWeight (compressMat A e (stencil owner)) t :=
  restrict_stageWeight A _ e q (compress_mat_comm A e _ (stencil_replay e owner matched)) t ht

theorem actual_output_formula {A:Fin s→Fin s→K} (b:Vec K s) (e:Fin n→Fin s) (owner:Fin s→Fin n)
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) {t:Tree} (ht:t.order≤q+2) :
    weight (compressMat A e (stencil owner)) (weightMerge b owner) t=
      ∑ i,b i*stageWeight A t (e (owner i)) := by
  change row (weightMerge b owner) (stageWeight (compressMat A e (stencil owner)) t)=_
  rw [←actual_stage_weights e owner matched ht,merged_output_at]

theorem actual_output_lower {A:Fin s→Fin s→K} (b:Vec K s) (e:Fin n→Fin s) (owner:Fin s→Fin n)
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) {t:Tree} (ht:t.order≤q+1) :
    weight (compressMat A e (stencil owner)) (weightMerge b owner) t=weight A b t := by
  rw [actual_output_formula b e owner matched (by omega),weight]
  apply Finset.sum_congr rfl
  intro i _
  rw [matched (stageWeight A t) (stageWeight_mem_space _ _ ht) i]

/-- Matching all paid lower tree columns also matches every genuinely branched
root at the next order; only unary-root conditions may change. -/
theorem actual_output_branched {A:Fin s→Fin s→K} (b:Vec K s) (e:Fin n→Fin s) (owner:Fin s→Fin n)
    (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) {t u v:Tree}
    (ht:(Tree.attach t (.attach u v)).order≤q+2) :
    weight (compressMat A e (stencil owner)) (weightMerge b owner) (.attach t (.attach u v))=
      weight A b (.attach t (.attach u v)) := by
  have tp:=t.order_pos
  have up:=u.order_pos
  have vp:=v.order_pos
  change t.order+(u.order+v.order)≤q+2 at ht
  rw [actual_output_formula b e owner matched (by change t.order+(u.order+v.order)≤q+2;exact ht),weight]
  apply Finset.sum_congr rfl
  intro i _
  have a := matched (stageWeight A (.attach t .leaf))
    (stageWeight_mem_space _ _ (by change t.order+1≤q+1;omega)) i
  have c := matched (stageWeight A (.attach u v))
    (stageWeight_mem_space _ _ (by change u.order+v.order≤q+1;omega)) i
  simp only [stageWeight,mul_one] at a
  simp only [stageWeight]
  rw [a]
  simpa only [stageWeight] using congrArg (fun z:K=>b i*((∑ j,A i j*stageWeight A t j)*z)) c

theorem merged_lower_order {A:Fin s→Fin s→K} {b:Vec K s} (e:Fin n ↪o Fin s) (owner:Fin s→Fin n)
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b (q+1))
    (early : ∀ i, e (owner i) ≤ i) (matched:∀v∈treeSpace A q,∀i,v (e (owner i))=v i) :
    StrictLower (compressMat A e (stencil owner)) ∧
      HasTreeOrderAtLeast (compressMat A e (stencil owner)) (weightMerge b owner) (q+1) := by
  refine ⟨compress_strict ha e _ (stencil_causal e owner early),?_⟩
  intro t ht
  rw [actual_output_lower b e owner matched ht]
  exact ho t ht

end OwnerCompression
end RKCert.Paired
