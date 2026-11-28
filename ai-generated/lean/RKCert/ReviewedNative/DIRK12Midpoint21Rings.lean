module

public import RKCert.ReviewedNative.DIRK12Midpoint21Flags
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
import Mathlib.Tactic.Ring

@[expose] public section

/-! The compact midpoint flag is checked over the rationals. Integer
homogeneity then specializes that *literal* tableau over arbitrary
commutative rings inverting 12!, including rings with zero divisors.
The next tall-tree defect is a unit and the first two diagonals differ. -/
namespace RKResearch.Certified.DIRK12Midpoint21

open RKResearch FiniteRootedTree
open scoped Matrix

set_option maxHeartbeats 0
set_option maxRecDepth 30000

theorem matrix_lower : matrix.IsLowerTriangular := by
  intro i j h
  exact if_pos h

theorem integerA_lower : integerA.IsLowerTriangular := by
  intro i j h
  exact if_pos h

theorem cast_scaled_moment (t : FiniteRootedTree) :
    (Int.castRingHom ℚ) ((t.factorial : ℤ) * (integerB ⬝ᵥ Φ t integerA)) =
      ((weightScale : ℚ) * (stageScale : ℚ)^((t.order:Nat)-1)) *
      ((t.factorial : ℚ) * (weights ⬝ᵥ Φ t matrix)) := by
  simp only [map_mul,map_natCast,RingHom.map_dotProduct,map_Φ,integerA_Q,
    integerB_Q,Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem integer_order_twelve (t : FiniteRootedTree) (ht : (t.order:Nat) ≤ 12) :
    (t.factorial : ℤ) * (integerB ⬝ᵥ Φ t integerA) =
      weightScale * stageScale^((t.order:Nat)-1) := by
  apply (Int.cast_injective (α := ℚ))
  change (Int.castRingHom ℚ) _ = (Int.castRingHom ℚ) _
  rw [cast_scaled_moment,rational_order_twelve t ht,mul_one,map_mul,map_pow]
  rfl

def nextTree : FiniteRootedTree := tallTree 13

def integerDefect : ℤ :=
  (nextTree.factorial : ℤ) * (integerB ⬝ᵥ Φ nextTree integerA) -
    weightScale * stageScale^12

theorem integer_next_tall : (1024:ℤ) * integerDefect =
    (-231) * (weightScale * stageScale^12) := by
  unfold integerDefect nextTree
  rw [Φ_tallTree]
  change (1024:ℤ) * (Int.ofNat (Nat.factorial 13) *
    (integerB ⬝ᵥ (integerA^12 *ᵥ (1:VI))) - weightScale * stageScale^12) = _
  rw [tall_at 12 (by decide),←outputI_eq]
  exact integer_tall_defect

section Target

variable {R : Type*} [CommRing R]

def targetA (u : R) : Matrix (Fin 21) (Fin 21) R :=
  u • integerA.map (Int.castRingHom R)

def targetB (v : R) : Fin 21 → R :=
  v • (Int.castRingHom R ∘ integerB)

theorem target_lower (u : R) : (targetA u).IsLowerTriangular := by
  intro i j h
  change u * ((integerA i j : ℤ) : R) = 0
  rw [integerA_lower h]
  simp

theorem transport (u v : R) (hu : (stageScale:R)*u=1)
    (hv : (weightScale:R)*v=1) : HasOrder 12 (targetA u) (targetB v) := by
  let f := Int.castRingHom R
  have fs : f stageScale*u=1 := hu
  have fw : f weightScale*v=1 := hv
  have hA : integerA.map f = f stageScale • targetA u := by
    change integerA.map f = f stageScale • (u • integerA.map f)
    rw [smul_smul,fs,one_smul]
  have hb : f ∘ integerB = f weightScale • targetB v := by
    change f ∘ integerB = f weightScale • (v • (f ∘ integerB))
    rw [smul_smul,fw,one_smul]
  exact hasOrder_of_scaled_moments f hA hb (IsUnit.of_mul_eq_one _ fs)
    (IsUnit.of_mul_eq_one _ fw) integer_order_twelve

theorem next_tall_defect (u v : R) (hu : (stageScale:R)*u=1)
    (hv : (weightScale:R)*v=1) :
    (1024:R)*((nextTree.factorial:R)*(targetB v ⬝ᵥ Φ nextTree (targetA u))-1) =
      (-231:R) := by
  let f := Int.castRingHom R
  have fs : f stageScale*u=1 := hu
  have fw : f weightScale*v=1 := hv
  have hp : (f stageScale)^12*u^12 = 1 := by rw [←mul_pow,fs,one_pow]
  have hm : (f weightScale*(f stageScale)^12)*(v*u^12)=1 := by
    calc
      _ = (f weightScale*v)*((f stageScale)^12*u^12) := by ring
      _ = _ := by rw [fw,hp,one_mul]
  have hmap := congrArg f integer_next_tall
  unfold integerDefect at hmap
  simp only [map_mul,map_sub,map_pow,map_natCast,RingHom.map_dotProduct,map_Φ] at hmap
  have ho : (nextTree.order:Nat)-1=12 := by decide +kernel
  simp only [targetA,targetB,Φ_matrix_smul,ho,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  have hz : f (-231) = (-231:R) := by
    simp only [f,Int.coe_castRingHom,Int.cast_neg,Int.cast_ofNat]
  rw [←hz]
  calc
    _ = f 1024 * ((nextTree.factorial:R) *
          ((f ∘ integerB) ⬝ᵥ Φ nextTree (integerA.map f))*(v*u^12) -
          (f weightScale*(f stageScale)^12)*(v*u^12)) := by
      rw [hm]
      simp only [f,Int.coe_castRingHom,Int.cast_ofNat]
      ring
    _ = (f 1024 * ((nextTree.factorial:R) *
          ((f ∘ integerB) ⬝ᵥ Φ nextTree (integerA.map f)) -
          (f weightScale*(f stageScale)^12)))*(v*u^12) := by ring
    _ = f (-231) := by rw [hmap,mul_assoc,hm,mul_one]

theorem unit_next_tall_defect (u v : R) (hu : (stageScale:R)*u=1)
    (hv : (weightScale:R)*v=1) (h231 : IsUnit (231:R)) :
    IsUnit ((nextTree.factorial:R)*(targetB v ⬝ᵥ Φ nextTree (targetA u))-1) := by
  have hh : IsUnit (-231:R) := h231.neg
  rw [←next_tall_defect u v hu hv] at hh
  exact isUnit_of_dvd_unit ⟨1024,mul_comm _ _⟩ hh

theorem not_order_thirteen [Nontrivial R] (u v : R)
    (hu : (stageScale:R)*u=1) (hv : (weightScale:R)*v=1)
    (h231 : IsUnit (231:R)) : ¬HasOrder 13 (targetA u) (targetB v) := by
  intro h
  have hh := unit_next_tall_defect u v hu hv h231
  rw [h nextTree (by decide +kernel),sub_self] at hh
  exact not_isUnit_zero hh

theorem target_diagonals_distinct [Nontrivial R] (u : R) (hu : (stageScale:R)*u=1) :
    targetA u 0 0≠targetA u 1 1 := by
  have h60 : integerA 0 0=60 := by decide +kernel
  have h30 : integerA 1 1=30 := by decide +kernel
  have h120 : IsUnit (120:R) := by
    apply IsUnit.of_mul_eq_one u
    simpa only [stageScale,Int.cast_ofNat] using hu
  have hu' : IsUnit u := IsUnit.of_mul_eq_one (stageScale:R) (by rw [mul_comm]; exact hu)
  have h30unit : IsUnit (30:R) := isUnit_of_dvd_unit ⟨4,by ring⟩ h120
  have e : targetA u 0 0 - targetA u 1 1 = (30:R)*u := by
    change u*(integerA 0 0:R)-u*(integerA 1 1:R)=_
    rw [h60,h30]
    simp only [Int.cast_ofNat]
    ring
  intro h
  rw [h,sub_self] at e
  exact ((h30unit.mul hu').ne_zero) e.symm

theorem exists_exact_factorial [Nontrivial R] (h : IsUnit (Nat.factorial 12:R)) :
    ∃ (U : Matrix (Fin 21) (Fin 21) R) (w : Fin 21 → R),
      U.IsLowerTriangular ∧ U 0 0≠U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w := by
  have getUnit (d : Nat) (hd : d∣Nat.factorial 12) : IsUnit (d:R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R) hd) h
  have hs : IsUnit (stageScale:R) := by
    simpa only [stageScale,Nat.cast_ofNat,Int.cast_ofNat] using getUnit 120 (by decide +kernel)
  have hw : IsUnit (weightScale:R) := by
    simpa only [weightScale,Nat.cast_ofNat,Int.cast_ofNat] using
      getUnit 19958400 (by decide +kernel)
  have h231 : IsUnit (231:R) := by
    simpa only [Nat.cast_ofNat] using getUnit 231 (by decide +kernel)
  obtain ⟨u,hu⟩ := hs.exists_right_inv
  obtain ⟨v,hv⟩ := hw.exists_right_inv
  exact ⟨targetA u,targetB v,target_lower u,target_diagonals_distinct u hu,
    transport u v hu hv,not_order_thirteen u v hu hv h231⟩

theorem exists_exact_iff_factorial_unit [Nontrivial R] :
    (∃ (U : Matrix (Fin 21) (Fin 21) R) (w : Fin 21 → R),
      U.IsLowerTriangular ∧ U 0 0≠U 1 1 ∧ HasOrder 12 U w ∧ ¬ HasOrder 13 U w) ↔
      IsUnit (Nat.factorial 12:R) := by
  refine ⟨?_,exists_exact_factorial⟩
  rintro ⟨U,w,_,_,ho,_⟩
  apply IsUnit.of_mul_eq_one (w ⬝ᵥ Φ (tallTree 12) U)
  have h := ho (tallTree 12) (by decide +kernel)
  have hfact : ((tallTree 12).factorial : Nat) = Nat.factorial 12 := by decide +kernel
  simpa only [hfact] using h

end Target
end RKResearch.Certified.DIRK12Midpoint21

#print axioms RKResearch.Certified.DIRK12Midpoint21.unit_next_tall_defect
#print axioms RKResearch.Certified.DIRK12Midpoint21.exists_exact_factorial
#print axioms RKResearch.Certified.DIRK12Midpoint21.exists_exact_iff_factorial_unit
