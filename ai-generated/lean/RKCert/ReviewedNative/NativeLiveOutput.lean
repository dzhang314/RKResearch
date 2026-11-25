module

public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.PolynomialStageSeparation
public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-! # Output-live coordinates are detected in one further paid grade

Multiply a putative tree-space coordinate by the linear factor
vanishing at its original clock. Its polynomial trace must vanish
by native separation at the next grade. This is uniform in the
field and degree; no tabulated Legendre calculation is needed. -/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module Polynomial
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s p m : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

set_option maxRecDepth 3500 in
set_option maxHeartbeats 650000 in
theorem live_coordinate_out_treeSpace (ho : HasOrder p A b) (pay : 2*m+3≤p)
    (i : Fin s) (live : b i≠0) : coordinate (K:=K) i∉treeSpace A m := by
  intro e
  rw [treeSpace_coeff_sup ho (by omega : m+1≤p)] at e
  obtain ⟨u,hu,w,hw,eq⟩ := Submodule.mem_sup.mp e
  obtain ⟨a,rfl⟩ := hu
  let P : K[X] := ofFn (m+1) a
  let R : K[X] := X-C (nodes A i)
  have pd : P.natDegree≤m := by
    change (ofFn (m+1) a).natDegree≤m
    have h := ofFn_natDegree_lt (by omega : 0<m+1) a
    omega
  have rd : R.natDegree≤1 := (natDegree_X_sub_C _).le
  have ev : evalNodes A P=coeffEval A m a := by
    rw [evalNodes_eq_coeffEval A P pd]
    congr 1
    exact toFn_comp_ofFn_eq_id _ _
  have z : (coordinate (K:=K) i)*evalNodes A R=0 := by
    ext j
    change coordinate (K:=K) i j * R.eval (nodes A j)=0
    by_cases ji : j=i
    · rw [ji]
      simp [R]
    · have h : coordinate (K:=K) i j=0 := by
        unfold coordinate
        exact @Pi.single_eq_of_ne (Fin s) (fun _=>K) _ (Classical.decEq _) i j ji 1
      rw [h,zero_mul]
  have sum : evalNodes A (P*R)+w*evalNodes A R=0 := by
    calc
      _ = (evalNodes A P+w)*evalNodes A R := by
        ext j
        simp only [Pi.add_apply,Pi.mul_apply,evalNodes_apply,eval_mul]
        ring
      _ = 0 := by rw [ev,eq,z]
  have v : w*evalNodes A R∈zeroSpace A (m+1) :=
    zeroSpace_mul_treeSpace ho (by omega) hw (evalNodes_mem_treeSpace A R rd)
  have d : evalNodes A (P*R)∈zeroSpace A (m+1) := by
    have e := (eq_neg_of_add_eq_zero_left sum)
    rw [e]
    exact (zeroSpace A (m+1)).neg_mem v
  have sep := PolySeparated.of_coeff (coeff_separated ho (q:=m+1) (by omega))
  have rz := sep (P*R) (natDegree_mul_le_of_le pd rd) d
  have pz : P=0 := (mul_eq_zero.mp rz).resolve_right (X_sub_C_ne_zero _)
  have mem : coordinate (K:=K) i∈zeroSpace A m := by
    rw [←eq,←ev,pz,map_zero,zero_add]
    exact hw
  have out : probe A b 0 (coordinate (K:=K) i)=0 :=
    probe_zeroSpace ho (by omega) mem
  exact live (by simpa only [probe,pow_zero,mul_one,row_coordinate] using out)

theorem ann_detects_live_output (ho : HasOrder p A b) (pay : 2*m+3≤p)
    (i : Fin s) (live : b i≠0) : ∃ v∈annih (treeSpace A m), v i≠0 := by
  by_contra! h
  apply live_coordinate_out_treeSpace ho pay i live
  rw [←annih_annih (treeSpace A m)]
  apply mem_annih.mpr
  intro w hw
  have e : row (coordinate (K:=K) i) w = row w (coordinate (K:=K) i) := by rw [row_apply,row_apply]; exact dotProduct_comm _ _
  rw [e,row_coordinate]
  exact h w hw

end
end RKResearch.Certified.Graded.Reverse
