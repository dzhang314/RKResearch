module
public import RKCert.ERKOrder13MarkedJacobi
public import RKCert.FactorPrimitiveScale
public import RKCert.LobattoFactorTables

@[expose] public section

/-! # Fixed marked alias moment gate
The split-prime test includes factors containing zero, endpoints belonging
to the selected factor, and all degrees up through three. It reduces only
integral monic factors, not the actual tableau or the free Jacobi pencil.
-/
namespace RKCert.Paired.FiniteMidpoint
open Polynomial RKCert.FixedFactor RKCert.OrderTwelve
universe u
variable {K:Type u} [Field K] [CharZero K]

def markAliasDigits : List ℤ := [-303595776,45999360,-2090880,39600,-330,1]
noncomputable def markAliasGrid := intHorner markAliasDigits
def markAliasKnots : List (ZMod 181) := [13,66,119,146,167]
local instance : Fact (Nat.Prime 181) := ⟨by decide +kernel⟩

private theorem degree_alias_grid : markAliasGrid.natDegree=5 := by
  apply le_antisymm (degree_horner_le markAliasDigits 5 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner markAliasDigits).coeff 5 ≠ 0
  rw [coeff_horner]
  decide

private theorem monic_alias_grid : markAliasGrid.Monic := by
  rw [Monic,leadingCoeff,degree_alias_grid,markAliasGrid,coeff_horner]
  decide

private theorem split_alias_grid :
    markAliasGrid.map (Int.castRingHom (ZMod 181))=linearProduct id markAliasKnots := by
  apply z_grid_split _ _ (by decide)
  intro i hi
  change i≤5 at hi
  interval_cases i <;> decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem marked13_alias_checked : checked 60 3 (0::markAliasKnots) markAliasKnots=true := by
  decide +kernel

private theorem alias_univariate_scale :
    (X*(dFivePoly:K[X])).scaleRoots (132:K)=
      C (132:K)*((X*markAliasGrid).map (Int.castRingHom K)) := by
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro y
  let z := y/132
  have yz : (132:K)*z=y := by dsimp [z];ring
  rw [←yz]
  have h: (X*(dFivePoly:K[X])).natDegree=6 := by
    have dn:(dFivePoly:K[X])≠0 := by
      intro e
      have d:=natDegree_dFivePoly (K:=K)
      simp [e] at d
    rw [natDegree_X_mul dn,natDegree_dFivePoly]
  rw [scaleRoots_eval_mul,h]
  norm_num [markAliasGrid,markAliasDigits,intHorner,dFivePoly]
  ring

/-- Fixed alias gate for all factors of x·D₅ of degree at most three. In
particular no division by the mandatory zero-root factor is needed before
taking the first affordable causal integral. -/
theorem marked13_alias_primitive_ne_zero
    (P:K[X]) (w:K) (pn:P≠0) (pf:P∣X*(dFivePoly:K[X]))
    (hd:P.natDegree≤3) (wn:w≠0) (root:(X*dFivePoly).eval w=0) :
    (Paired.primitive (X*P)).eval w≠0 := by
  refine native_from_scaled (X*dFivePoly) markAliasGrid 132 132 (by norm_num) (by norm_num)
    alias_univariate_scale 60 3 ?_ ?_ P w pn pf hd wn root
  · intro i hi
    interval_cases i <;> decide
  · exact fun Q v qm qd qdeg vr =>
      good_prime 181 (X*markAliasGrid) markAliasGrid
        (monic_X.mul monic_alias_grid) monic_alias_grid 60 3
        (modular_table _ _ 60 3 (0::markAliasKnots) markAliasKnots
          (splitX _ _ split_alias_grid) split_alias_grid marked13_alias_checked)
        Q v qm qd qdeg vr

end RKCert.Paired.FiniteMidpoint
