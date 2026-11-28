module

public import RKCert.ReviewedNative.DIRK12MidpointLegendreProbes
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! A true grade-six bridge image is fully paid once it has the
degree-six Legendre profile off the ghosts and terminal and silent
actual output. No value of the terminal correction is guessed. -/
namespace RKResearch.Certified.DIRK12MidpointShape

open RKResearch Graded Polynomial DIRK12MidpointRealInterval DIRK12MidpointForward
open scoped Matrix Polynomial BigOperators
variable {ι : Type*} [Fintype ι]

theorem scalar_orthogonal_profile6 (A : Matrix ι ι ℝ) (z : ι → ℝ)
    (silent : ∀ k≤6, row z ((nodes A)^k)=0) :
    row z (actualProfile A 1)=0 := by
  let c := nodes A
  have e : actualProfile A 1 =
      (-42:ℝ) • c^1 + (840:ℝ) • c^2 + (-5040:ℝ) • c^3 +
      (12600:ℝ) • c^4 + (-13860:ℝ) • c^5 + (5544:ℝ) • c^6 := by
    funext i
    simp only [actualProfile,leg,show (1:Fin 3)≠0 by decide,ite_false,ite_eq_left,
      leg6,Pi.add_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul,c]
    ring
  rw [e]
  simp only [map_add,map_smul,smul_eq_mul,c]
  rw [silent 1 (by decide),silent 2 (by decide),silent 3 (by decide),silent 4 (by decide),
    silent 5 (by decide),silent 6 (by decide)]
  norm_num

theorem actual_profile_bridge (A : Matrix ι ι ℝ) (b w : ι → ℝ)
    (B : Nat → Submodule ℝ (ι → ℝ)) (ghost : ι → Prop) (terminal : ι) (rho : ℝ)
    (quad : ∀ p : ℝ[X], p.natDegree<12 → DIRK12MidpointStar.quadr A b p=integral p)
    (nodeT : nodes A terminal=1)
    (silentB : ∀ z∈B 5, ∀ k≤6, row z ((nodes A)^k)=0)
    (bGhost : DualSupport12.zeroAt ghost b)
    (zGhost : ∀ z∈B 5, DualSupport12.zeroAt ghost z)
    (zTerminal : ∀ z∈B 5, z terminal=0)
    (off : ∀ i, ¬ghost i → i≠terminal → w i=rho*actualProfile A 1 i)
    (output : row b w=0) :
    w ∈ DualSupport12.high A b B 5 := by
  classical
  have split (z : ι → ℝ) (zg : DualSupport12.zeroAt ghost z) (zt : z terminal=0) :
      row z w=rho*row z (actualProfile A 1) := by
    rw [row_apply,row_apply,dotProduct,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases g : ghost i
    · rw [zg i g]; ring
    · by_cases t : i=terminal
      · subst i
        rw [zt]; ring
      · rw [off i g t]; ring
  apply DualSupport12.mem_high.mpr
  refine ⟨?_,?_⟩
  · intro z hz
    rw [split z (zGhost z hz) (zTerminal z hz),
      scalar_orthogonal_profile6 A z (silentB z hz),mul_zero]
  · intro j hj
    by_cases jz : j=0
    · subst j
      simpa using output
    · have zg : DualSupport12.zeroAt ghost (DualSupport12.moment A b j) := by
        intro i e
        simp [DualSupport12.moment,bGhost i e]
      have zt : DualSupport12.moment A b j terminal=0 := by
        simp [DualSupport12.moment,DualSupport12.reflected,nodeT,zero_pow jz]
      let k : Fin 7 := ⟨j,by omega⟩
      have h := profile_probe A b quad (1:Fin 3) k (by change j<6; omega)
        (by change j+1+5<12; omega)
      have kz : k≠0 := fun he => jz (congrArg Fin.val he)
      rw [ite_eq_right kz] at h
      change row (DualSupport12.moment A b j) (actualProfile A 1)=0 at h
      rw [split _ zg zt,h,mul_zero]

end RKResearch.Certified.DIRK12MidpointShape

#print axioms RKResearch.Certified.DIRK12MidpointShape.scalar_orthogonal_profile6
#print axioms RKResearch.Certified.DIRK12MidpointShape.actual_profile_bridge
