import RKCert
import Mathlib.Data.ZMod.Defs

#print axioms RKCert.hasTreeOrderAtLeast_iff_inverse
#print axioms RKCert.Tree.density_chain
#print axioms RKCert.chain_condition
#print axioms RKCert.stageWeight_chain_eq_zero
#print axioms RKCert.weight_chain_eq_zero
#print axioms RKCert.explicit_order_le_stages
#print axioms RKCert.Tree.mem_through
#print axioms RKCert.checkTreeOrder_iff
#print axioms RKCert.ClassicalRK4.explicit
#print axioms RKCert.ClassicalRK4.order_four
#print axioms RKCert.ClassicalRK4.not_order_five
#print axioms RKCert.ChainOnly.chains_pass
#print axioms RKCert.ChainOnly.fork_weight
#print axioms RKCert.ChainOnly.not_order_three
#print axioms RKCert.RationalDIRK7.lowerTriangular
#print axioms RKCert.RationalDIRK7.row_sums
#print axioms RKCert.RationalDIRK7.variable_diagonal
#print axioms RKCert.RationalDIRK7.order_seven
#print axioms RKCert.RationalDIRK7.bush_eight_weight
#print axioms RKCert.RationalDIRK7.not_order_eight
#print axioms RKCert.Tree.density_attach_cut
#print axioms RKCert.rootCut_stage
#print axioms RKCert.treeError_sub_cut
#print axioms RKCert.rootCutPair_eq_zero_of_treeOrder
#print axioms RKCert.hasTreeOrderAtLeast_iff_rootCutTests
#print axioms RKCert.mixedResidualWeight_cons
#print axioms RKCert.mixedResidualWeight_eq_zero_of_treeOrder
#print axioms RKCert.hasTreeOrderAtLeast_iff_residualProductTests
#print axioms RKCert.MonomialOnly.explicit
#print axioms RKCert.MonomialOnly.moments
#print axioms RKCert.MonomialOnly.monomial_tests
#print axioms RKCert.MonomialOnly.quadratic_failure
#print axioms RKCert.MonomialOnly.doubleBranch_weight
#print axioms RKCert.MonomialOnly.not_order_five
#print axioms RKCert.isUnit_nat_of_moments
#print axioms RKCert.factorial_isUnit_of_treeOrder
#print axioms RKCert.factorial_isUnit_iff_treeDensities
#print axioms RKCert.treeDensity_isUnit_of_moments
#print axioms RKCert.balancedRootCut_of_treeOrder
#print axioms RKCert.hasTreeOrderAtLeast_iff_balancedRootCuts
#print axioms RKCert.scaledRootCut_stage
#print axioms RKCert.scaledRootCutPair_eq
#print axioms RKCert.scaled_normalizedCut_difference
#print axioms RKCert.hasTreeOrderAtLeast_iff_scaledRootCutTests

open RKCert RKCert.Paired RKCert.Paired.SDIRK
#print axioms commutator_injective
#print axioms probe_commutator
#print axioms stage_rank_step
#print axioms nonsingular_floor
#print axioms nonsingular_quadratic_le20
#print axioms ring_quadratic_le20
#print axioms strict_sdirk_ring_le20
#print axioms floor_table
example {K : Type*} [Field K] {A : Fin 54 → Fin 54 → K} {b : Fin 54 → K}
    (ho : HasTreeOrderAtLeast A b 20) (ha : lower A) (hd : ∀ i, A i i ≠ 0) : False := by
  have h := nonsingular_quadratic_le20 ho ha hd (by decide) (by decide)
  exact (by decide : ¬ quadraticFloor 20 ≤ 54) h
example {A : Fin 14 → Fin 14 → ZMod 121} {b : Fin 14 → ZMod 121} {γ : ZMod 121}
    (ho : HasTreeOrderAtLeast A b 10) (ha : ∀ i j, i.val<j.val → A i j=0)
    (he : ∀ i, A i i=γ) (hγ : IsUnit γ) : False := by
  let _ : Nontrivial (ZMod 121) := ⟨⟨0,1,by decide⟩⟩
  have h := strict_sdirk_ring_le20 ho ha he hγ (by decide) (by decide)
  exact (by decide : ¬ quadraticFloor 10 ≤ 14) h
example (A : Fin 6 → Fin 6 → ℚ) (b : Fin 6 → ℚ)
    (ho : HasTreeOrderAtLeast A b 6) (ha : lower A) (hd : ∀ i, A i i ≠ 0) :
    6 ≤ 6 := by
  exact nonsingular_quadratic_le20 ho ha hd (by decide) (by decide)


example : (11 : ZMod 121) ≠ 0 ∧ (11:ZMod 121)*11=0 := by decide


#print axioms RKCert.DIRKFinite.positive_stages
#print axioms RKCert.DIRKFinite.order_three_ring
#print axioms RKCert.DIRKFinite.order_four_ring
#print axioms RKCert.DIRKFinite.order_five_ring
#print axioms RKCert.Paired.mem_of_invariant_seed
#print axioms RKCert.Paired.zeroSpace_finrank
#print axioms RKCert.Paired.back_lt_succ
#print axioms RKCert.Paired.terminal_single_not_mem
#print axioms RKCert.Paired.backward_endpoint_count
#print axioms RKCert.uniform_erk_ring
#print axioms RKCert.uniform_erk_ring_through_twenty
#print axioms RKCert.zmod77_no_five_stage_order_five
#print axioms RKCert.zmod23_no_26_stage_order_nineteen
#print axioms RKCert.dirk_floor_ring
#print axioms RKCert.dirkRingFloor_le_stages
#print axioms RKCert.dirkRingFloor_through20
#print axioms RKCert.DIRKFloorRegression.order_seven_rational_minimum
#print axioms RKCert.DIRKFloorRegression.order_twenty_mod529
