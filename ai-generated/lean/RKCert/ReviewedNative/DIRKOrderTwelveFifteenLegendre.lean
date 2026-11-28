module

public import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFrame
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! # The genuine degree-six scalar defect on the non-C(2) face -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen

open RKResearch Module FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K]
    {A : Matrix (Fin 15) (Fin 15) K} {b : Fin 15 → K}

def legendreCoeffs (K : Type*) [Field K] : Fin 7 → K :=
  ![1,-42,420,-1680,3150,-2772,924]

private theorem legendre_moment [CharZero K] (i : Fin 6) :
    (∑ j : Fin 7, legendreCoeffs K j / ((i.val+j.val+1:ℕ):K)) = 0 := by
  fin_cases i <;> norm_num [legendreCoeffs, Fin.sum_univ_succ]

/-- The reduced Legendre column is a genuine zero-profile grade-six vector,
not a pointwise approximation or a positivity assumption on the weights. -/
theorem legendre_in_six [CharZero K] (ho : HasOrder 12 A b)
    (H : EqualityFrame A b) (nc : monomialStageDefect A 1 ≠ 0) :
    coeffEval A 6 (legendreCoeffs K) ∈ zeroSpace A 6 := by
  classical
  let V := (coeffEval A 5).range
  let F := zeroSpace A 6
  have r6 := (H.nonC2_ranks nc).2.2.2
  have sep := coeff_defect_separated_paid (q:=5) (j:=6) ho (by decide) (by decide)
  have dis : V⊓F=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨hv,hf⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a,rfl⟩ := hv
    rw [sep a hf,map_zero]
    exact (⊥:Submodule K (Fin 15→K)).zero_mem
  have inj : Function.Injective (coeffEval A 5) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a h
    exact sep a (h ▸ F.zero_mem)
  have rV : finrank K V=6 := by
    unfold V
    rw [LinearMap.finrank_range_of_inj inj,Module.finrank_fin_fun]
  have rank := Submodule.finrank_sup_add_finrank_inf_eq V F
  rw [dis,finrank_bot,add_zero,rV,show finrank K F=6 from r6] at rank
  have inc : V⊔F≤treeSpace A 6 := by
    apply sup_le _ (zeroSpace_le_treeSpace A 6)
    rintro v ⟨a,rfl⟩
    exact treeSpace_mono A (by decide : 5≤6) (coeffEval_mem_treeSpace A _ a)
  have eq : V⊔F=treeSpace A 6 := by
    apply Submodule.eq_of_le_of_finrank_le inc
    rw [H.t6,rank]
  have e := coeffEval_mem_treeSpace A 6 (legendreCoeffs K)
  rw [←eq] at e
  obtain ⟨v,hv,f,hf,he⟩ := Submodule.mem_sup.mp e
  obtain ⟨a,rfl⟩ := hv
  have hh (i : Fin 6) : (∑ j : Fin 6, a j/((i.val+j.val+1:ℕ):K))=0 := by
    have i8 := i.isLt
    have z := congrArg (probe A b i.val) he
    have f0 : probe A b i.val f=0 := probe_zeroSpace ho (by omega) hf
    rwa [map_add,f0,add_zero,probe_coeffEval ho (by omega),probe_coeffEval ho (by omega),
      legendre_moment i] at z
  have z := moments_detect ho (n:=6) (d:=1) (by decide) (by decide)
    (fun i j=>by have := i.isLt; have := j.isLt; omega) a hh
  have az : a=0 := funext z
  rw [az,map_zero,zero_add] at he
  exact he▸hf

theorem legendre_at_clock_zero {i : Fin 15} (ni : nodes A i=0) :
    coeffEval A 6 (legendreCoeffs K) i=1 := by
  rw [coeffEval_apply]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,normTree_clockTree,ni]
  rw [Fin.sum_univ_succ]
  simp [legendreCoeffs, Fin.val_succ]

/-- An actual row that reads zero on every grade-five stage column reads
zero on every grade-six genuine defect. It need not be a literal zero row. -/
theorem grade_six_defect_zero_at_readless_row {i : Fin 15}
    (quiet : ∀ v∈treeSpace A 5, mat A v i=0) :
    ∀ f∈zeroSpace A 6, f i=0 := by
  have dead (t : FiniteRootedTree) (ht : (t.order : ℕ)≤7)
      (hnt : t ≠ .leaf) : Φ t A i=0 := by
    cases t with
    | leaf => exact (hnt rfl).elim
    | butcherProduct t u =>
      have htu : ((FiniteRootedTree.butcherProduct t u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := by
        simp only [order,PNat.add_coe]
      have tp := t.order.pos
      have q : Φ u A∈treeSpace A 5 := Φ_mem_treeSpace A _ (by omega)
      have z := quiet _ q
      simp only [Φ,Pi.mul_apply]
      rw [←mat_apply,z,mul_zero]
  show zeroSpace A 6 ≤ (LinearMap.proj i).ker
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change normTree A t i - normTree A u i = 0
  by_cases et : t = .leaf
  · have eu : u = .leaf := (coe_order_eq_one_iff_leaf u).mp (by rw [← he, et]; rfl)
    rw [et, eu, sub_self]
  · have eu : u ≠ .leaf := by
      intro hu
      exact et ((coe_order_eq_one_iff_leaf t).mp (by rw [he, hu]; rfl))
    have uh : (u.order:ℕ)≤7 := by rw [←he]; exact ht
    simp [normTree, dead t ht et, dead u uh eu]

theorem nonC2_clock_zero_row_reads_something [CharZero K] (ho : HasOrder 12 A b)
    (H : EqualityFrame A b) (nc : monomialStageDefect A 1 ≠ 0)
    {i : Fin 15} (ni : nodes A i=0) :
    ∃ v∈treeSpace A 5, mat A v i≠0 := by
  by_contra h
  push Not at h
  have fail := grade_six_defect_zero_at_readless_row h _
    (legendre_in_six ho H nc)
  rw [legendre_at_clock_zero ni] at fail
  exact one_ne_zero fail

#print axioms legendre_in_six
#print axioms grade_six_defect_zero_at_readless_row
#print axioms nonC2_clock_zero_row_reads_something

end RKResearch.Certified.Graded.OrderTwelveFifteen
