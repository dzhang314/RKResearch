module

public import RKCert.ReviewedNative.ERK19Jacobi

@[expose] public section

/-! # Remaining width-twenty-nine branches in original stage coordinates

The one-or-two point reverse branch and the zero-seed weighted pencil
are **not** assumed in this interface. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

/-- The eighth and ninth ordinary ranks, common to both adjoint cases. -/
theorem width29_eight_nine (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b) :
    finrank K (zeroSpace A 8)=9 ∧ finrank K (zeroSpace A 9)=10 := by
  have l := grade_eight_surplus_ordered_of_reviewed_order ha ho (by decide)
  have e : finrank K (zeroSpace A 9)=10 := (ordered_width29_frame ha ho).1.middleDefects
  have g := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_paid_output ha ho (j:=8) (by decide) (by decide))
  change finrank K (zeroSpace A 8)<finrank K (zeroSpace A 9) at g
  exact ⟨by omega,e⟩

/-- The marked branch carries the actual last coordinate: the quadratic
seed vanishes there and its full eight-step flag fills precisely the
terminal-zero slice of the true grade-nine annihilator. -/
theorem width29_zero_terminal (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (z : firstSeed A b=0) :
    b (Fin.last 28)≠0 ∧ nodes A (Fin.last 28)=1 ∧ quadraticSeed A b (Fin.last 28)=0 ∧
    coordinate (K:=K) (Fin.last 28) ∉ treeSpace A 9 ∧
    primitiveBack A b 8=zeroAt (annih (treeSpace A 9)) (Fin.last 28) := by
  obtain ⟨frame,active⟩ := ordered_width29_frame ha ho
  obtain ⟨t,last,one,out,ann⟩ := frame.reverse.firstZero z
  have et : t=Fin.last 28 := by
    apply le_antisymm (Fin.le_last t)
    by_contra! h
    exact active.live (last.after _ h)
  subst t
  have dz := mem_tailZero.mp (active.seed_tail ha z 1) (Fin.last 28) le_rfl
  exact ⟨active.live,one,dz,out,(frame.reverse.flagExact 8 (by decide)).2.symm.trans ann⟩

/-- No forward class has been assumed empty. In the nonzero branch
F11 has rank twelve or thirteen, and neither permits a nonzero clean row. -/
theorem nonzero_seed_eleven_frontier (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) :
    (finrank K (zeroSpace A 11)=12 ∨ finrank K (zeroSpace A 11)=13) ∧
      ∀ i : Fin 29, nodes A i≠0 → ∃ w∈zeroSpace A 11, w i≠0 := by
  have r := rank_coeff_sup_of_separated (zeroSpace A 11) (q:=8)
    (paid_origin_coeff_separation ha ho (by decide) (by decide))
  have inc : (coeffEval A 8).range ⊔ zeroSpace A 11 ≤ treeSpace A 11 := by
    apply sup_le _ (zeroSpace_le_treeSpace A 11)
    rintro _ ⟨a,rfl⟩
    exact treeSpace_mono A (by decide : 8≤11) (coeffEval_mem_treeSpace A 8 a)
  have low := Submodule.finrank_mono inc
  rw [r] at low
  change 9 + finrank K (zeroSpace A 11) ≤ finrank K (treeSpace A 11) at low
  have lim := backward_count ha ho 11 6 (by decide)
  rw [first_dim_one nz] at lim
  have f := (nonzero_seed_grade_ten ha ho nz).1
  have g := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_paid_output ha ho (j:=10) (by decide) (by decide))
  change finrank K (zeroSpace A 10)<finrank K (zeroSpace A 11) at g
  refine ⟨by omega,?_⟩
  intro i live
  by_contra! clean
  exact live (nonzero_seed_clean_eleven_clock_zero ha ho nz i clean)

end RKResearch.Certified.ERK19
