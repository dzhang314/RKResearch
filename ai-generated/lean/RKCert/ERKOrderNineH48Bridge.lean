module

public import RKCert.ERKGoodPrimePoly
public import RKCert.ERKOrderNineH48Kernel

@[expose] public section

namespace RKCert.GoodPrimeDense
open Polynomial RKCert.Paired

noncomputable def h48 : ℤ[X] := ofCoeffList h48Coeffs

theorem h48CoeffLength : h48Coeffs.length = 49 := by decide +kernel

def h48Lead : ℤ := h48Coeffs[48]?.getD 0

theorem h48Coeff48 : h48.coeff 48 = h48Lead := by
  simp [h48,coeff_ofCoeffList,List.getD_eq_getElem?_getD,h48Lead]

theorem h48Lead_nonzero : h48Lead ≠ 0 := by decide +kernel

theorem h48_degree : h48.natDegree = 48 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (h48Coeff48 ▸ h48Lead_nonzero)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [h48,List.getD_eq_getElem?_getD,List.getElem?_eq_none_iff.mpr
    (show h48Coeffs.length ≤ i by rw [h48CoeffLength]; omega)]

theorem h48_leadingCoeff : h48.leadingCoeff = h48Lead := by
  simpa only [leadingCoeff,h48_degree] using h48Coeff48

theorem read_rat_scale {K : Type*} [Field K] [CharZero K] (l : K) (a : ℚ) (p : List ℤ) :
    read (Rat.castHom K) l (p.map fun i : ℤ => a*(i:ℚ)) =
      (a:K)*read (Int.castRingHom K) l p := by
  induction p with
  | nil => simp [read]
  | cons b p ih =>
    simp only [List.map_cons,read]
    rw [ih,map_mul,map_intCast]
    simp only [Rat.coe_castHom,Int.coe_castRingHom]
    ring

theorem h48_zero_of_k8 {K : Type*} [Field K] [CharZero K] {h u v l : K}
    (root : RootSystem (pencilAt l ((84:K)⁻¹)) h u v)
    (k : sixOnK8 h u v l=0) : (h48.map (Int.castRingHom K)).eval l=0 := by
  let o := scalar ℚ
  let c := constant o ((84:ℚ)⁻¹)
  let s := Sound.scalar (Rat.castHom K)
  let f := read (Rat.castHom K) l
  have xl : f (generator o) = l := read_generator s l
  have xc : f c = (84:K)⁻¹ := by
    rw [show f c = Rat.castHom K ((84:ℚ)⁻¹) from read_constant s l _]
    simp
  have hz : f h48RawCoeffs=0 := by
    apply k8TowerNorm_zero (s.dense l) _ _ h u v
    · change RootSystem (pencilAt (f (generator o)) (f c)) h u v
      rw [xl,xc]
      exact root
    · change sixOnK8 h u v (f (generator o)) = 0
      rw [xl]
      exact k
  change read (Rat.castHom K) l h48RawCoeffs = 0 at hz
  have exp : h48ExpectedCoeffs = h48Coeffs.map (fun i : ℤ => h48Scale*(i:ℚ)) := rfl
  rw [h48_raw_check,exp,read_rat_scale] at hz
  have hn : (h48Scale:K) ≠ 0 := by norm_num [h48Scale]
  rw [←eval₂_eq_eval_map,h48,eval₂_ofCoeffList_read]
  exact (mul_eq_zero.mp hz).resolve_left hn

theorem h48_zero_of_distinct_pencil {K : Type*} [Field K] [CharZero K] {h u v l : K}
    (hr : (lobattoPencil l).eval h=0) (ur : (lobattoPencil l).eval u=0)
    (vr : (lobattoPencil l).eval v=0) (uh : u≠h) (vh : v≠h) (vu : v≠u)
    (k : sixOnK8 h u v l=0) : (h48.map (Int.castRingHom K)).eval l=0 := by
  apply h48_zero_of_k8 (rootSystem_of_distinct ?_ ?_ ?_ uh vh vu) k
  all_goals simpa only [pencilAt_eval] using (by assumption)

end RKCert.GoodPrimeDense
