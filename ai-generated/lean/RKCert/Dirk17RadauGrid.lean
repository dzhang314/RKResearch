module
public import RKCert.DirkQuinticTools
public import RKCert.LobattoFactorTables
public import Mathlib.FieldTheory.Separable
public import RKCert.FixedKnotCases
public import RKCert.DirkLobattoQuadrature
public import Mathlib.Tactic.NormNum.Prime
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.Paired RKCert.FixedFactor RKCert.DirkQuintic
variable {K:Type*} [Field K] [CharZero K]
def raw : List ℤ :=[0,9,-360,4620,-27720,90090,-168168,180180,-102960,24310]
def scaled : List ℤ :=[0,45158262249745468747341990000000,-74304010283415004109160000000,39225344795166291762000000,-9681286251377941200000,1294289605799190000,-99383268784800,4380175800,-102960,1]
def integers : List ℤ :=[0,151797,111860,47035,144283,214201,140319,8477,164519]
def gridp : List (ZMod 293177):=[0,151797,111860,47035,144283,214201,140319,8477,164519]
instance prime293177 : Fact (Nat.Prime 293177):=⟨by norm_num⟩
theorem map_integers:gridp=integers.map (Int.castRingHom (ZMod 293177)):=by decide +kernel
noncomputable def grid (K:Type*) [CommRing K]:K[X]:=(intHorner raw).map (Int.castRingHom K)
noncomputable def scaledGrid:ℤ[X]:=intHorner scaled
theorem grid_degree:(grid K).natDegree=9:=by
  apply le_antisymm (natDegree_map_le.trans (degree_horner_le raw 9 (by decide)))
  apply le_natDegree_of_ne_zero
  change ((intHorner raw).map (Int.castRingHom K)).coeff 9≠0
  rw [coeff_map,coeff_horner];norm_num [raw,readCoeff]
theorem scaled_degree:scaledGrid.natDegree=9:=by
  apply le_antisymm (degree_horner_le scaled 9 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner scaled).coeff 9≠0;rw [coeff_horner];decide
theorem scaled_monic:scaledGrid.Monic:=by rw [Monic,leadingCoeff,scaled_degree,scaledGrid,coeff_horner];decide
theorem split_scaled:scaledGrid.map (Int.castRingHom (ZMod 293177))=linearProduct id gridp:=by
  apply z_grid_split _ _ (by decide)
  intro i hi;change i≤9 at hi
  interval_cases i <;> decide +kernel
omit [CharZero K] in
theorem scale_eqn (x:K):(scaledGrid.map (Int.castRingHom K)).eval (24310*x)=24310^8*(grid K).eval x:=by
  norm_num [scaledGrid,grid,raw,scaled,intHorner];ring
omit [CharZero K] in
theorem grid_native (x:K):(grid K).eval x=x*RKCert.Endpoint.rightWeight8 x:=by
  norm_num [grid,raw,intHorner,RKCert.Endpoint.rightWeight8];left;ring
theorem grid_separable:(grid K).Separable:=by
  let A:K[X]:=(intHorner [51561,-2362041,29777220,-161621460,443513070,-644593950,472972500,-137837700]).map (Int.castRingHom K)
  let B:K[X]:=(intHorner [140,-40361,980001,-8446020,34894860,-77387310,94444350,-59759700,15315300]).map (Int.castRingHom K)
  have h:A*grid K+B*(grid K).derivative=C (1260:K):=by
    rw [Polynomial.C_ofNat]
    norm_num [A,B,grid,raw,intHorner,derivative_add,derivative_mul];ring
  change IsCoprime (grid K) (grid K).derivative
  refine ⟨C ((1260:K)⁻¹)*A,C ((1260:K)⁻¹)*B,?_⟩
  calc
    _=C ((1260:K)⁻¹)*(A*grid K+B*(grid K).derivative):=by ring
    _=1:=by rw [h,←C_mul,inv_mul_cancel₀ (by norm_num : (1260:K)≠0),C_1]
end RKCert.RadauEight
