module
public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Physical row annihilators in the reviewed matrix setting

This is the ordinary algebraic dual of the actual row indexed by stages.
The rank and marked-coordinate lemmas need neither characteristic zero
nor an ordered field, and do not shorten or permute a tableau.
-/
namespace RKResearch.Certified.Graded.Reverse

open Module
open scoped Matrix

variable {ι K : Type*} [Fintype ι] [Field K]
noncomputable section

def dotDual : (ι → K) ≃ₗ[K] Module.Dual K (ι → K) := by
  classical
  exact dotProductEquiv K ι

/-- Coordinate rows which vanish against every column in the given space. -/
def annih (V : Submodule K (ι → K)) : Submodule K (ι → K) :=
  V.dualAnnihilator.comap (dotDual.toLinearMap)

theorem mem_annih {V : Submodule K (ι → K)} {w : ι → K} :
    w ∈ annih V ↔ ∀ u ∈ V, row w u = 0 := by
  change dotDual w ∈ V.dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  rfl

theorem annih_antitone : Antitone (annih (ι:=ι) (K:=K)) := by
  intro U V inc w hw
  exact mem_annih.mpr (fun u hu => mem_annih.mp hw u (inc hu))

theorem finrank_annih (V : Submodule K (ι → K)) :
    finrank K V + finrank K (annih V) = Fintype.card ι := by
  have e : finrank K (annih V) = finrank K V.dualAnnihilator :=
    (LinearEquiv.ofSubmodule' dotDual V.dualAnnihilator).finrank_eq
  rw [e,Subspace.finrank_add_finrank_dualAnnihilator_eq V,Module.finrank_fintype_fun_eq_card]

theorem annih_annih (V : Submodule K (ι → K)) : annih (annih V) = V := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv
    apply mem_annih.mpr
    intro w hw
    rw [row_apply,dotProduct_comm,←row_apply]
    exact mem_annih.mp hw v hv
  · have h₁ := finrank_annih V
    have h₂ := finrank_annih (annih V)
    omega

/-- The column with a single unit at one *original* coordinate. -/
def coordinate (t : ι) : ι → K := by
  classical
  exact Pi.single t 1

@[simp] theorem row_coordinate (w : ι → K) (t : ι) :
    row w (coordinate (K:=K) t) = w t := by
  classical
  rw [row_apply,coordinate,dotProduct_single_one]

def zeroAt (V : Submodule K (ι → K)) (t : ι) : Submodule K (ι → K) :=
  V ⊓ LinearMap.ker (LinearMap.proj t)

omit [Fintype ι] in
theorem mem_zeroAt {V : Submodule K (ι → K)} {t : ι} {w : ι → K} :
    w ∈ zeroAt V t ↔ w ∈ V ∧ w t = 0 := by
  rw [zeroAt,Submodule.mem_inf,LinearMap.mem_ker]
  rfl

theorem annih_sup_coordinate (V : Submodule K (ι → K)) (t : ι) :
    annih (V ⊔ K ∙ coordinate t) = zeroAt (annih V) t := by
  ext w
  rw [mem_zeroAt]
  constructor
  · intro hw
    refine ⟨annih_antitone le_sup_left hw,?_⟩
    rw [←row_coordinate w t]
    have tmem : coordinate (K:=K) t ∈ K ∙ coordinate t := Submodule.mem_span_singleton_self _
    exact mem_annih.mp hw _ ((show K ∙ coordinate t ≤ V ⊔ K ∙ coordinate t from le_sup_right) tmem)
  · rintro ⟨hw,hzero⟩
    apply mem_annih.mpr
    intro z hz
    obtain ⟨u,hu,v,hv,rfl⟩:=Submodule.mem_sup.mp hz
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
    rw [map_add,map_smul,mem_annih.mp hw _ hu,row_coordinate,hzero,smul_zero,add_zero]

/-- A coordinate absent from the column span costs exactly one genuine
row-space dimension when it is required to vanish. -/
theorem finrank_zeroAt_annih (V : Submodule K (ι → K)) (t : ι)
    (outside : coordinate (K:=K) t ∉ V) :
    finrank K (zeroAt (annih V) t) + 1 = finrank K (annih V) := by
  have a:=finrank_annih V
  have b:=finrank_annih (V ⊔ K∙coordinate t)
  rw [annih_sup_coordinate,Submodule.finrank_sup_span_singleton outside] at b
  omega

theorem row_mat_transpose (A : Matrix ι ι K) (w v : ι → K) :
    row (mat A.transpose w) v = row w (mat A v) := by
  rw [row_apply,row_apply,mat_apply,mat_apply,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

theorem row_diag (c w v : ι → K) : row (diag c w) v = row w (diag c v) := by
  simp only [row_apply,dotProduct,diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem annih_map_transpose {V W : Submodule K (ι → K)} {A : Matrix ι ι K}
    (h : V ≤ W.comap (mat A)) : (annih W).map (mat A.transpose) ≤ annih V := by
  rintro _ ⟨w,hw,rfl⟩
  apply mem_annih.mpr
  intro v hv
  rw [row_mat_transpose]
  exact mem_annih.mp hw _ (h hv)

theorem annih_map_diag {V W : Submodule K (ι → K)} {c : ι → K}
    (h : V ≤ W.comap (diag c)) : (annih W).map (diag c) ≤ annih V := by
  rintro _ ⟨w,hw,rfl⟩
  apply mem_annih.mpr
  intro v hv
  rw [row_diag]
  exact mem_annih.mp hw _ (h hv)

end
end RKResearch.Certified.Graded.Reverse
