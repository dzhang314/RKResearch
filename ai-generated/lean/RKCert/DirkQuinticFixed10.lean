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

def raw10 : List ℤ := [0,110,-6050,108900,-943800,4624620,-13873860,26426400,-32089200,24066900,-10161580,1847560]
def der10 : List ℤ := [-110,5940,-102960,840840,-3783780,10090080,-16336320,15752880,-8314020,1847560]
def scaled10 : List ℤ := [0,106378238269975486281855312068031021056,-348345028866911868629557166214676480,373315701333913648209813586083840,-192629360853412615175342407680,56196943806961289256916992,-10037558431822092627456,1138316201342960640,-82295850299520,3674796840,-92378,1]
noncomputable def integral10 : ℤ[X] := intHorner scaled10

theorem native_der10 : (shiftedLegendre 10).derivative=intHorner der10 := by
  ext k
  rw [coeff_horner]
  by_cases h:k≤9
  · interval_cases k <;> norm_num [der10,readCoeff,coeff_derivative,coeff_shiftedLegendre,Nat.choose]
  · have dd:((shiftedLegendre 10).derivative).natDegree=9:=by rw [natDegree_derivative,natDegree_shiftedLegendre]
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact (read_out der10 k (by change 10≤k;omega)).symm

omit [CharZero K] in
theorem native_grid10 : (X-1)*lobatto (K:=K) 10=(intHorner raw10).map (Int.castRingHom K) := by
  rw [lobatto,native_der10]
  norm_num [der10,raw10,intHorner]
  ring

theorem degree_grid10 : ((X-1)*lobatto (K:=K) 10).natDegree=11 := by
  rw [native_grid10]
  apply le_antisymm (natDegree_map_le.trans (degree_horner_le raw10 11 (by decide)))
  apply le_natDegree_of_ne_zero
  rw [coeff_map,coeff_horner]
  norm_num [raw10,readCoeff]

theorem sep_grid10 : ((X-1)*lobatto (K:=K) 10).Separable := by
  let A:K[X]:=(intHorner [81191,-5881810,117644670,-1042332720,4927532610,-13543662132,22327665360,-21743641920,11523231720,-2560718160]).map (Int.castRingHom K)
  let B:K[X]:=(intHorner [126,-67331,2566685,-34890570,234096720,-890155266,2045385342,-2895612720,2469847380,-1163962800,232792560]).map (Int.castRingHom K)
  let D:K[X]:=(X-1)*lobatto 10
  have h:A*D+B*D.derivative=C (13860:K) := by
    dsimp only [D]
    rw [native_grid10,Polynomial.C_ofNat]
    norm_num [A,B,raw10,intHorner,derivative_add,derivative_mul]
    ring
  change IsCoprime D D.derivative
  refine ⟨C ((13860:K)⁻¹)*A,C ((13860:K)⁻¹)*B,?_⟩
  calc
    _ = C ((13860:K)⁻¹)*(A*D+B*D.derivative) := by ring
    _ = 1 := by rw [h,←C_mul,inv_mul_cancel₀ (by norm_num : (13860:K)≠0),C_1]

theorem degree_scaled10 : integral10.natDegree=11 := by
  apply le_antisymm (degree_horner_le scaled10 11 (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner scaled10).coeff 11≠0
  rw [coeff_horner];decide

theorem monic_scaled10 : integral10.Monic := by
  rw [Monic,leadingCoeff,degree_scaled10,integral10,coeff_horner];decide

theorem split_scaled10 : integral10.map (Int.castRingHom (ZMod 15727))=linearProduct id grid10 := by
  apply z_grid_split _ _ (by decide)
  intro i hi
  change i≤11 at hi
  interval_cases i <;> decide +kernel

omit [CharZero K] in
theorem scale_eqn10 (x:K) : (110:K)*((integral10.map (Int.castRingHom K)).eval (16796*x)) =
    (16796:K)^10*(((X-1)*lobatto 10).eval x) := by
  rw [native_grid10]
  norm_num [integral10,raw10,scaled10,intHorner]
  ring
end RKCert.DirkQuintic
