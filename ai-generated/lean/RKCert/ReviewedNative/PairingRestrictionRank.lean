module

public import Mathlib.LinearAlgebra.Dual.Lemmas
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Rank lost by restricting both slots of a pairing
Apply this to the signed output pairing on the contrast hyperplane itself.
No diagonal basis, symmetry, nondegeneracy or ordering of the field is needed. -/
namespace RKCert.ReviewedNative.PairingRestrictionRank

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Each restricted slot costs at most the codimension of the tested subspace. -/
theorem finrank_pairing_le_restrict_add_twice_codim
    (B : V →ₗ[K] Module.Dual K V) (W : Submodule K V) :
    finrank K B.range ≤
      finrank K (W.dualRestrict.comp (B.domRestrict W)).range +
        2 * finrank K (V ⧸ W) := by
  have leftKer : finrank K (B.domRestrict W).ker ≤ finrank K B.ker := by
    rw [← Submodule.finrank_map_subtype_eq W (B.domRestrict W).ker,
      LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
    exact Submodule.finrank_mono inf_le_right
  have bothKer : finrank K (W.dualRestrict.comp (B.domRestrict W)).ker ≤
      finrank K W.dualRestrict.ker + finrank K (B.domRestrict W).ker := by
    have H := (B.domRestrict W).lift_rank_comap_le W.dualRestrict.ker
    simp only [← Submodule.finrank_eq_rank, Cardinal.lift_natCast] at H
    exact_mod_cast H
  rw [Submodule.dualRestrict_ker_eq_dualAnnihilator] at bothKer
  have annihDim := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have quotDim := W.finrank_quotient_add_finrank
  have wholeDim := B.finrank_range_add_finrank_ker
  have testDim := (W.dualRestrict.comp (B.domRestrict W)).finrank_range_add_finrank_ker
  omega

end RKCert.ReviewedNative.PairingRestrictionRank
