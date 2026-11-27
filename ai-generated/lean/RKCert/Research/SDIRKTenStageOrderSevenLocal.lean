module

public import RKCert.Research.SDIRKTenStageOrderSevenRing
public import RKCert.Research.SDIRKTenStageOrderSevenAltRing
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.LinearCombination

public section

/-! # Two complementary ten-stage strict SDIRK witnesses

A local ring can make at most one of the two denominators a nonunit,
once 7! is a unit. The method is chosen globally in that local ring;
there is no assertion of gluing these two constructions in an arbitrary ring.
-/

namespace RKResearch.Certified.SDIRKTenStageOrderSevenLocal
open scoped Matrix

private theorem complement_units {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsUnit (5040 : R)) :
    IsUnit (13255661380500 : R) ∨ IsUnit (2913563520 : R) := by
  have hd : IsUnit (11340 : R) := by
    have hpow := h.pow 2
    apply isUnit_of_dvd_unit _ hpow
    refine ⟨(2240 : R), ?_⟩
    norm_num
  have hsum :
      IsUnit ((196151 : R) * 13255661380500 + (-892416183 : R) * 2913563520) := by
    rw [show ((196151 : R) * 13255661380500 + (-892416183 : R) * 2913563520) = 11340 by norm_num]
    exact hd
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h₁ | h₂
  · exact Or.inl (isUnit_of_dvd_unit ⟨_, mul_comm _ _⟩ h₁)
  · exact Or.inr (isUnit_of_dvd_unit ⟨_, mul_comm _ _⟩ h₂)

/-- Every paid local ring, in particular every field admitting order seven,
has an exact seven-order strict SDIRK with ten physical stages. -/
theorem exists_exact {R : Type*} [CommRing R] [IsLocalRing R] (h : IsUnit (5040 : R)) :
    ∃ (A : Matrix (Fin 10) (Fin 10) R) (b : Fin 10 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  rcases complement_units h with hd | hd
  · obtain ⟨A,b,γ,ht,hg,hu,-,ho,hn⟩ :=
      SDIRKTenStageOrderSevenRing.exists_exact_of_stageDen_unit hd
    exact ⟨A,b,γ,ht,hg,hu,ho,hn⟩
  · obtain ⟨A,b,γ,ht,hg,hu,-,ho,hn⟩ :=
      SDIRKTenStageOrderSevenAltRing.exists_exact_of_stageDen_unit hd
    exact ⟨A,b,γ,ht,hg,hu,ho,hn⟩

theorem exists_exact_field {K : Type*} [Field K] (h : (5040 : K) ≠ 0) :
    ∃ (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b := by
  obtain ⟨A,b,γ,ht,hg,hu,ho,hn⟩ := exists_exact (isUnit_iff_ne_zero.mpr h)
  exact ⟨A,b,γ,ht,hg,hu.ne_zero,ho,hn⟩

end RKResearch.Certified.SDIRKTenStageOrderSevenLocal
