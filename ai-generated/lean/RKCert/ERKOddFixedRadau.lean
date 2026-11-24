module
public import RKCert.Dirk17RadauGrid
public import RKCert.ERKFinitePackets
public import RKCert.FactorPrimitiveScale

@[expose] public section
/-! # All-characteristic-zero first moment at the fixed odd Radau mesh
Only the monic integral divisor and marked root of a fixed polynomial
are reduced. Coefficients of the RK array are never specialized. -/
namespace RKCert.RadauEight.FirstMoment
open Polynomial RKCert.FixedFactor RKCert.Paired
variable {K:Type*} [Field K] [CharZero K]
noncomputable section
def headDigits:List ℤ:=scaled.tail
def H:ℤ[X]:=intHorner headDigits
def knots:List (ZMod 293177):=gridp.tail
theorem split_zero:scaledGrid=X*H:=by
  rw [scaledGrid,scaled,intHorner]
  simp [H,headDigits,scaled]
theorem Hdegree:H.natDegree=8:=by
  apply le_antisymm (degree_horner_le _ _ (by decide))
  apply le_natDegree_of_ne_zero
  change (intHorner headDigits).coeff 8≠0
  rw [coeff_horner];decide
theorem Hmonic:H.Monic:=by
  rw [Monic,leadingCoeff,Hdegree]
  change (intHorner headDigits).coeff 8=1
  rw [coeff_horner];decide
theorem Hsplit:H.map (Int.castRingHom (ZMod 293177))=linearProduct id knots:=by
  apply z_grid_split _ _ (by decide)
  intro i hi
  change i≤8 at hi
  interval_cases i <;> decide +kernel
theorem grid_scale:(grid K).scaleRoots (24310:K)=C (24310:K)*((X*H).map (Int.castRingHom K)):=by
  rw [←split_zero]
  classical
  ext n
  rw [coeff_scaleRoots,grid_degree,coeff_C_mul]
  by_cases h:n≤9
  · rw [grid,scaledGrid,coeff_map,coeff_map,coeff_horner,coeff_horner]
    interval_cases n <;> norm_num [raw,scaled,readCoeff]
  · have z:((grid K).coeff n)=0:=coeff_eq_zero_of_natDegree_lt (by rw [grid_degree];omega)
    have w:((scaledGrid.map (Int.castRingHom K)).coeff n)=0:=
      coeff_eq_zero_of_natDegree_lt ((natDegree_map_le (p:=scaledGrid)).trans_lt (by rw [scaled_degree];omega))
    rw [z,w,zero_mul,mul_zero]

/-- Modular split-table callback can be shared without repeating the
physical or integral-scaling proof. -/
theorem native_of_check (tab:checked 420 5 gridp knots=true)
    {P:K[X]} {u:K}(div:P∣(RKCert.Paired.FiniteMidpoint.odd8:K[X])) (deg:P.natDegree≤5)
    (un:u≠0)(hit:(RKCert.Paired.FiniteMidpoint.odd8:K[X]).eval u=0):
    (primitive (X*P)).eval u≠0:=by
  let : Infinite K:=Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective
  have native:(RKCert.Paired.FiniteMidpoint.odd8:K[X])=grid K:=by
    apply Polynomial.funext
    intro x
    rw [RKCert.Paired.FiniteMidpoint.odd8_eval,grid_native]
  rw [native] at div hit
  have gn:grid K≠0:=by intro z;have h:=grid_degree (K:=K);rw [z,natDegree_zero] at h;omega
  apply native_from_scaled _ H (24310:K) (24310:K) (by norm_num) (by norm_num) grid_scale 420 5
    (by intro i hi;interval_cases i <;> decide) _ P u (ne_zero_of_dvd_ne_zero gn div) div deg un hit
  have fmon:((X:ℤ[X])*H).Monic:=by rw [←split_zero];exact scaled_monic
  have sp:((X:ℤ[X])*H).map (Int.castRingHom (ZMod 293177))=linearProduct id gridp:=by
    rw [←split_zero];exact split_scaled
  exact good_prime 293177 (X*H) H fmon Hmonic 420 5
    (modular_table _ _ 420 5 gridp knots sp Hsplit tab)
end
end RKCert.RadauEight.FirstMoment
