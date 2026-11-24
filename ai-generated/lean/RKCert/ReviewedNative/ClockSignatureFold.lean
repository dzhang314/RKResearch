module

public import RKCert.ReviewedNative.ClockHeadPaidFlow
public import RKCert.ReviewedNative.NonsingularDIRKStageFloor

@[expose] public section

/-! # Exact prefix folding of repeated (clock,head) signatures

Only donor columns are regrouped, always at their earliest matching
physical position. Row count and physical indices are unchanged. Both
applications of the tableau inside Volterra commute with the regrouping
on the paid head profile; the folded matrix is not granted any order. -/
namespace RKResearch.Certified.Graded.HeadFiber
namespace Signature

open Polynomial RKCert.Endpoint RKCert.OneEscape
open scoped Matrix Classical
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {c w : Fin s → K}

noncomputable def fiberSet (c w : Fin s → K) (i : Fin s) : Finset (Fin s) :=
  Finset.univ.filter (fun j => (c j,w j)=(c i,w i))

omit [Field K] in
theorem self_fiber (c w : Fin s → K) (i : Fin s) : i ∈ fiberSet c w i := by
  simp [fiberSet]

noncomputable def first (c w : Fin s → K) (i : Fin s) : Fin s :=
  (fiberSet c w i).min' ⟨i,self_fiber c w i⟩

omit [Field K] in
theorem first_signature (c w : Fin s → K) (i : Fin s) :
    (c (first c w i),w (first c w i))=(c i,w i) :=
  (Finset.mem_filter.mp ((fiberSet c w i).min'_mem _)).2

omit [Field K] in
theorem first_le (c w : Fin s → K) (i : Fin s) : first c w i ≤ i :=
  (fiberSet c w i).min'_le _ (self_fiber c w i)

omit [Field K] in
theorem first_congr {i j : Fin s} (eq : (c i,w i)=(c j,w j)) :
    first c w i=first c w j := by
  have e : fiberSet c w i=fiberSet c w j := by simp [fiberSet,eq]
  apply le_antisymm
  · apply (fiberSet c w i).min'_le
    rw [e]
    exact (fiberSet c w j).min'_mem _
  · apply (fiberSet c w j).min'_le
    rw [←e]
    exact (fiberSet c w i).min'_mem _

omit [Field K] in
theorem first_idempotent (c w : Fin s → K) (i : Fin s) :
    first c w (first c w i)=first c w i := first_congr (first_signature c w i)

omit [Field K] in
theorem first_of_no_earlier {i : Fin s}
    (h : ∀ j < i, (c j,w j)≠(c i,w i)) : first c w i=i := by
  rcases lt_or_eq_of_le (first_le c w i) with hh|hh
  · exact False.elim (h _ hh (first_signature c w i))
  · exact hh

/-- Sum the original row taps over one signature, preserving repeated
physical rows rather than treating their entries as distinct observations. -/
noncomputable def fold (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K) :
    Matrix (Fin s) (Fin s) K :=
  fun i j => ∑ l : Fin s with first (nodes A) w l = j, A i l

theorem fold_zero_nonfirst (i j : Fin s) (h : first (nodes A) w j≠j) : fold A w i j=0 := by
  unfold fold
  apply Finset.sum_eq_zero
  intro l hl
  have eq := (Finset.mem_filter.mp hl).2
  exact False.elim (h (eq ▸ first_idempotent (nodes A) w l))

theorem fold_lower (ha : A.IsLowerTriangular) : (fold A w).IsLowerTriangular := by
  intro i j hij
  unfold fold
  apply Finset.sum_eq_zero
  intro l hl
  have e := (Finset.mem_filter.mp hl).2
  have h := first_le (nodes A) w l
  rw [e] at h
  change i < j at hij
  apply ha
  exact hij.trans_le h

theorem fold_mat {v : Fin s → K} (constant : ∀ i, v (first (nodes A) w i)=v i) :
    mat (fold A w) v = mat A v := by
  let f := first (nodes A) w
  ext i
  rw [mat_apply,mat_apply,Matrix.mulVec_apply_eq_sum,Matrix.mulVec_apply_eq_sum]
  calc
    _ = ∑ l : Fin s, ∑ j : Fin s with f j=l, A i j * v (f j) := by
      apply Finset.sum_congr rfl
      intro l _
      change (∑ j : Fin s with f j=l,A i j)*v l = _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = ∑ j : Fin s, A i j * v (f j) := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => (Finset.mem_univ (f j)))
        (fun j : Fin s => A i j*v (f j))
    _ = _ := Finset.sum_congr rfl fun j _ => by rw [constant]

theorem fold_nodes (A : Matrix (Fin s) (Fin s) K) (w : Fin s → K) :
    nodes (fold A w)=nodes A :=
  fold_mat (w:=w) (v:=1) (fun _=>rfl)

theorem headInput_first (f q : K[X]) (i : Fin s) :
    headInput A w f q (first (nodes A) w i) = headInput A w f q i := by
  simp only [headInput_apply]
  have ec : nodes A (first (nodes A) w i)=nodes A i := congrArg Prod.fst (first_signature (nodes A) w i)
  have ew : w (first (nodes A) w i)=w i := congrArg Prod.snd (first_signature (nodes A) w i)
  rw [ec,ew]

theorem fold_mat_headInput (f q : K[X]) :
    mat (fold A w) (headInput A w f q)=mat A (headInput A w f q) :=
  fold_mat (headInput_first f q)

theorem fold_volterra_headInput [CharZero K] {k : ℕ}
    (bk : zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ w (1+k))
    (bn : zeroSpace A (3+(k+1))=chain (diag (nodes A)) ⊥ w (1+(k+1)))
    {f q : K[X]} (df : f.natDegree≤3+k) (dq : q.natDegree≤k) :
    volterra (fold A w) (headInput A w f q)=volterra A (headInput A w f q) := by
  let v := headInput A w f q
  have e : mat (fold A w) v=mat A v := fold_mat_headInput f q
  have ec : mat (fold A w) (diag (nodes A) v)=mat A (diag (nodes A) v) := by
    apply fold_mat
    intro i
    have ec : nodes A (first (nodes A) w i)=nodes A i := congrArg Prod.fst (first_signature (nodes A) w i)
    rw [diag_apply,diag_apply,ec,show v (first (nodes A) w i)=v i from headInput_first f q i]
  obtain ⟨r,_,a⟩ := headInput_mat bk bn df dq
  have ea : mat (fold A w) (mat A v)=mat A (mat A v) := by
    change mat (fold A w) (mat A (headInput A w f q)) = _
    rw [a,fold_mat_headInput]
  change diag (nodes (fold A w)) (mat (fold A w) v)-mat (fold A w) (diag (nodes (fold A w)) v)-
    mat (fold A w) (mat (fold A w) v) = diag (nodes A) (mat A v)-mat A (diag (nodes A) v)-mat A (mat A v)
  rw [fold_nodes,e,ec,ea]


/-- A first representative keeps its actual self tap. -/
theorem fold_diag_of_first (ha : A.IsLowerTriangular) (i : Fin s)
    (h : first (nodes A) w i=i) : fold A w i i=A i i := by
  unfold fold
  have hi : i ∈ Finset.univ.filter (fun l => first (nodes A) w l=i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  apply Finset.sum_eq_single_of_mem i hi
  intro j hj ne
  have eq := (Finset.mem_filter.mp hj).2
  have le := first_le (nodes A) w j
  rw [eq] at le
  apply ha
  change i < j
  exact lt_of_le_of_ne le (Ne.symm ne)

/-- A one-tap equality for a row with pointwise vanishing of all other
products. Taking the selected product zero gives the zero-tap case. -/
theorem mat_single_tap (M : Matrix (Fin s) (Fin s) K) (v : Fin s → K) (i j : Fin s)
    (other : ∀ k, k≠j → M i k*v k=0) :
    mat M v i=M i j*v j := by
  rw [mat_apply,Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun k _ ne => other k ne)

/-- View the already-defined Volterra operator as a matrix of real taps. -/
noncomputable abbrev volterraTaps (M : Matrix (Fin s) (Fin s) K) :
    Matrix (Fin s) (Fin s) K :=
  Matrix.diagonal (nodes M)*M - M*Matrix.diagonal (nodes M) - M*M

theorem taps_apply (M : Matrix (Fin s) (Fin s) K) (i j : Fin s) :
    volterraTaps M i j=(nodes M i-nodes M j)*M i j - ∑ k, M i k*M k j := by
  change (Matrix.diagonal (nodes M)*M-M*Matrix.diagonal (nodes M)-M*M) i j=_
  rw [Matrix.sub_apply,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.mul_apply]
  ring

theorem mat_taps (M : Matrix (Fin s) (Fin s) K) :
    mat (volterraTaps M)=volterra M := by
  have d : mat (Matrix.diagonal (nodes M))=diag (nodes M) := by
    apply LinearMap.ext
    intro v
    funext i
    rw [mat_apply,Matrix.mulVec_diagonal]
    rfl
  change Matrix.toLin' (volterraTaps M)=_
  simp only [volterraTaps,volterra,map_sub,Matrix.toLin'_mul,←d]
  rfl

theorem taps_lower {M : Matrix (Fin s) (Fin s) K} (ha : M.IsLowerTriangular) :
    (volterraTaps M).IsLowerTriangular := by
  intro i j h
  rw [taps_apply,ha h,mul_zero,zero_sub,neg_eq_zero]
  apply Finset.sum_eq_zero
  intro k _
  by_cases b : i < k
  · rw [ha b,zero_mul]
  · rw [ha ((le_of_not_gt b).trans_lt h),mul_zero]

theorem taps_zero_col {M : Matrix (Fin s) (Fin s) K} {j : Fin s}
    (hz : ∀ i, M i j=0) (i : Fin s) : volterraTaps M i j=0 := by
  rw [taps_apply]
  simp [hz]

theorem taps_of_zero_diags {M : Matrix (Fin s) (Fin s) K} (ha : M.IsLowerTriangular)
    {i j : Fin s} (a0 : M i i=0) (b0 : M j j=0)
    (mid : ∀ k, j < k → k < i → M i k*M k j=0) :
    volterraTaps M i j=(nodes M i-nodes M j)*M i j := by
  rw [taps_apply]
  have hz : (∑ k, M i k*M k j)=0 := by
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_trichotomy k i with h|rfl|h
    · rcases lt_trichotomy k j with g|rfl|g
      · rw [ha g,mul_zero]
      · rw [b0,mul_zero]
      · exact mid _ g h
    · rw [a0,zero_mul]
    · rw [ha h,zero_mul]
  rw [hz,sub_zero]

end Signature
end RKResearch.Certified.Graded.HeadFiber
