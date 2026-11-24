module
public import RKCert.DirkQuinticGridLists
public import RKCert.LobattoFactorTables
public import RKCert.DirkLobattoQuadrature
public import Mathlib.FieldTheory.Separable
@[expose] public section
namespace RKCert.DirkQuintic
open Polynomial RKCert.FixedFactor RKCert.Paired.Terminal
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {K:Type*} [Field K] [CharZero K]

def raw9 : List ℤ := [0,-90,4050,-59400,415800,-1621620,3783780,-5405400,4633200,-2187900,437580]
def der9 : List ℤ := [-90,3960,-55440,360360,-1261260,2522520,-2882880,1750320,-437580]
def scaled9 : List ℤ := [0,-312262358838417733759398052096,2890128783983709999829887360,-8718337206587360482141440,12552110334453213363840,-10068537701433058848,4832014528316976,-1419760982640,250295760,-24310,1]
noncomputable def integral9 : ℤ[X] := intHorner scaled9

theorem native_der9 : (shiftedLegendre 9).derivative=intHorner der9 := by
  ext k
  rw [coeff_horner]
  by_cases h:k≤8
  · interval_cases k <;> norm_num [der9,readCoeff,coeff_derivative,coeff_shiftedLegendre,Nat.choose]
  · have dd:((shiftedLegendre 9).derivative).natDegree=8:=by rw [natDegree_derivative,natDegree_shiftedLegendre]
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact (read_out der9 k (by change 9≤k;omega)).symm

omit [CharZero K] in
theorem native_grid9 : (X-1)*lobatto (K:=K) 9=(intHorner raw9).map (Int.castRingHom K) := by
  rw [lobatto,native_der9]
  norm_num [der9,raw9,intHorner]
  ring

theorem degree_grid9 : ((X-1)*lobatto (K:=K) 9).natDegree=10 := by
  rw [native_grid9]
  apply le_antisymm (natDegree_map_le.trans (degree_horner_le raw9 10 (by decide)))
  apply le_natDegree_of_ne_zero
  rw [coeff_map,coeff_horner]
  norm_num [raw9,readCoeff]

theorem sep_grid9 : ((X-1)*lobatto (K:=K) 9).Separable := by
  let A:K[X]:=(intHorner [-7129,414810,-6631020,46366320,-169279110,346846500,-401501100,245044800,-61261200]).map (Int.castRingHom K)
  let B:K[X]:=(intHorner [-14,5869,-179685,1951620,-10330320,30324294,-51921870,51591540,-27567540,6126120]).map (Int.castRingHom K)
  let D:K[X]:=(X-1)*lobatto 9
  have h:A*D+B*D.derivative=C (1260:K) := by
    dsimp only [D]
    rw [native_grid9,Polynomial.C_ofNat]
    norm_num [A,B,raw9,intHorner,derivative_add,derivative_mul]
    ring
  change IsCoprime D D.derivative
  refine ⟨C ((1260:K)⁻¹)*A,C ((1260:K)⁻¹)*B,?_⟩
  calc
    _ = C ((1260:K)⁻¹)*(A*D+B*D.derivative) := by ring
    _ = 1 := by rw [h,←C_mul,inv_mul_cancel₀ (by norm_num : (1260:K)≠0),C_1]

theorem degree_scaled9 : integral9.natDegree=10 := by
  apply le_antisymm (degree_horner_le scaled9 10 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner scaled9).coeff 10≠0
  rw [coeff_horner];decide

theorem monic_scaled9 : integral9.Monic := by
  rw [Monic,leadingCoeff,degree_scaled9,integral9,coeff_horner];decide

theorem split_scaled9 : integral9.map (Int.castRingHom (ZMod 10709))=linearProduct id grid9 := by
  apply z_grid_split _ _ (by decide)
  intro i hi
  change i≤10 at hi
  interval_cases i <;> decide +kernel

omit [CharZero K] in
theorem scale_eqn9 (x:K) : (90:K)*((integral9.map (Int.castRingHom K)).eval (4862*x)) =
    (4862:K)^9*(((X-1)*lobatto 9).eval x) := by
  rw [native_grid9]
  norm_num [integral9,raw9,scaled9,intHorner]
  ring

end RKCert.DirkQuintic
