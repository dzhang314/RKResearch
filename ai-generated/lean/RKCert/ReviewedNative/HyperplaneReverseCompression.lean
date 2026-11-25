module

public import RKCert.ReviewedNative.HyperplaneReverseTerminal
public import RKCert.ReviewedNative.CausalMerge
public import RKCert.ReviewedNative.ReflectedMoments
public import RKCert.ReviewedNative.RowAnnihilator
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Compress three original reverse rows along the E9/E10 class hyperplane

The matrix is the strictly causal sum onto earliest representatives. It is
not asserted to have RK order. Only columns lying in the preceding paid
tree grade may replace a physical row by its representative after applying A.
-/
namespace RKResearch.Certified.Graded.HyperplaneTerminal

open RKResearch Reverse Module
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s n j k p : ℕ}

def folded (r : Fin s→Fin n) (b : Fin s→K) : Fin n→K :=
  fun h=>∑ i ∈ Finset.univ.filter (fun i=>r i=h), b i

theorem folded_pair (r : Fin s→Fin n) (b : Fin s→K) (x : Fin n→K) :
    row (folded r b) x = row b (fun i=>x (r i)) := by
  classical
  simp only [row_apply,dotProduct,folded]
  rw [← Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ) (g:=r)
    (fun i _=>Finset.mem_univ _) (fun i=>b i*x (r i))]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

private theorem folded_mat (A : Matrix (Fin s) (Fin s) K)
    (e : Fin n→Fin s) (r : Fin s→Fin n) (x : Fin n→K) (h : Fin n) :
    mat (causalMergeMatrix A e r) x h = mat A (fun i=>x (r i)) (e h) :=
  folded_pair r (A (e h)) x

private theorem folded_probe (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K)
    (r : Fin s→Fin n) (y : Fin n→K) (cy : ∀i,y (r i)=reflectedClock A i)
    (k : ℕ) (x : Fin n→K) :
    reflectedProbe A b 0 k (fun i=>x (r i)) =
      row (fun h=>y h^k*folded r b h) x := by
  calc
    _ = row b (fun i=>(fun h=>y h^k*x h) (r i)) := by
      simp only [reflectedProbe,row_apply,dotProduct,pow_zero,mul_one]
      apply Finset.sum_congr rfl
      intro i _
      rw [cy i]
      ring
    _ = row (folded r b) (fun h=>y h^k*x h) := (folded_pair r b (fun h => y h ^ k * x h)).symm
    _ = _ := by
      simp only [row_apply,dotProduct]
      apply Finset.sum_congr rfl
      intro h _
      ring

def residual (B : Matrix (Fin n) (Fin n) K) (b y : Fin n→K) (k : ℕ) : Fin n→K :=
  ((k+1 : ℕ):K) • mat B.transpose (fun h=>y h^k*b h) -
    (fun h=>y h^(k+1)*b h)

private theorem residual_pair (B : Matrix (Fin n) (Fin n) K) (b y x : Fin n→K) (k : ℕ) :
    row (residual B b y k) x =
      ((k+1:ℕ):K)*row (fun h=>y h^k*b h) (mat B x) -
        row (fun h=>y h^(k+1)*b h) x := by
  simp only [residual,row_apply,mat_apply,sub_dotProduct,smul_dotProduct,
    Matrix.mulVec_transpose,Matrix.dotProduct_mulVec,smul_eq_mul]

/-- Transfer on the actual previous tree grade only. No identity is
required on an arbitrary compressed-stage column. -/
theorem folded_residual_mem {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder p A b) (e : Fin n→Fin s) (r : Fin s→Fin n) (y : Fin n→K)
    (cy : ∀i,y (r i)=reflectedClock A i) (H : Submodule K (Fin n→K))
    (before : ∀x∈H, (fun i=>x (r i))∈treeSpace A j)
    (same : ∀v∈treeSpace A (j+1), ∀i,v (e (r i))=v i)
    (pay : j+k+2≤p) :
    residual (causalMergeMatrix A e r) (folded r b) y k ∈ annih H := by
  apply mem_annih.mpr
  intro x hx
  have pulled : (fun i=>x (r i)) ∈ treeSpace A j := before x hx
  have Ax : mat A (fun i=>x (r i)) ∈ treeSpace A (j+1) := mat_treeSpace A j pulled
  have action_eq : mat A (fun i=>x (r i)) =
      fun i=>mat (causalMergeMatrix A e r) x (r i) := by
    ext i
    exact (same _ Ax i).symm.trans (folded_mat A e r x (r i)).symm
  have paid : row (reflectedStageRow A b k) (fun i=>x (r i))=0 :=
    reflectedStageRow_treeSpace ho j k pay pulled
  rw [reflectedStageRow_pair,action_eq,folded_probe A b r y cy,folded_probe A b r y cy] at paid
  rwa [residual_pair]

variable [CharZero K]

/-- Actual order plus a one-codimensional class presentation and physical
first representatives force the obstruction. It suffices to check the
singletons bearing both output mass and reflected clock zero. -/
theorem folded_hyperplane_impossible {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (e : Fin n→Fin s) (r : Fin s→Fin n)
    (ordered : Monotone e) (earlier : ∀i,e (r i) ≤ i)
    (y : Fin n→K) (cy : ∀i,y (r i)=reflectedClock A i)
    (H : Submodule K (Fin n→K)) (rankH : finrank K H+1=n)
    (before : ∀x∈H, (fun i=>x (r i))∈treeSpace A j)
    (same : ∀v∈treeSpace A (j+1), ∀i,v (e (r i))=v i)
    (l : Fin n→K) (lin : l∈annih H) (ln : l≠0) (pay : j+4≤p)
    (mask : ∀i,folded r b i≠0 → y i≠0 ∨ l i≠0)
    (distinct : ∃i v,folded r b i≠0 ∧ folded r b v≠0 ∧ y i≠y v) : False := by
  let B := causalMergeMatrix A e r
  let f := folded r b
  have room := finrank_annih H
  rw [Fintype.card_fin] at room
  have eq : K ∙ l=annih H := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact (Submodule.span_singleton_le_iff_mem ..).mpr lin
    · rw [finrank_span_singleton ln]
      omega
  have fit (k : ℕ) (hk : k≤2) : ∃a : K, a • l=residual B f y k := by
    apply Submodule.mem_span_singleton.mp
    rw [eq]
    exact folded_residual_mem ho e r y cy H before same (by omega)
  obtain ⟨a,ra⟩:=fit 0 (by decide)
  obtain ⟨d,rd⟩:=fit 1 (by decide)
  obtain ⟨g,rg⟩:=fit 2 (by decide)
  apply three_rows_impossible Fin.revPerm (mat B.transpose)
    (causal_transpose (causalMerge_strict ha ordered earlier)) y f l a d g
    _ _ _ mask distinct
  · intro i
    have h := congrFun ra i
    simp [residual,Pi.smul_apply,smul_eq_mul] at h
    simp only [mat_apply, Matrix.mulVec_transpose]
    linear_combination -h
  · intro i
    have h := congrFun rd i
    simp [residual,Pi.smul_apply,smul_eq_mul] at h
    simp only [mat_apply, Matrix.mulVec_transpose]
    linear_combination -h
  · intro i
    have h := congrFun rg i
    simp [residual,Pi.smul_apply,smul_eq_mul] at h
    simp only [mat_apply, Matrix.mulVec_transpose]
    linear_combination -h

end
end RKResearch.Certified.Graded.HyperplaneTerminal
