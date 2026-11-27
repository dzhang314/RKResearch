module

public import RKCert.ReviewedNative.ERK10Stepanov
public import RKCert.ReviewedNative.ERK10StepanovCharElevenParameters
public import RKCert.ReviewedNative.ERK10StepanovNilpotentParameters
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Besides the real-algebraic context, the same exact tableau gives an
upper bound over any algebraically closed field paying the common
denominator, and admits concrete specializations to prime fields. -/

namespace RKResearch.Certified.ERK10Stepanov
open ERKNestedRadicalReplay

theorem exact_of_algClosed {K : Type*} [Field K] [IsAlgClosed K] (hD : (D:K) ≠ 0) :
    ∃ (U : Matrix (Fin 15) (Fin 15) K) (w : Fin 15 → K),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨x,hx⟩ := IsAlgClosed.exists_pow_nat_eq (3:K) (n:=2) (by decide)
  obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq (7:K) (n:=2) (by decide)
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (147+42*y) (n:=2) (by decide)
  have H : Roots x y z := ⟨by simpa only [pow_two] using hx,
    by simpa only [pow_two] using hy,by simpa only [pow_two] using hz⟩
  exact exact_with_roots H hD.isUnit

set_option maxHeartbeats 0

theorem exact_mod37 :
    ∃ (U : Matrix (Fin 15) (Fin 15) (ZMod 37)) (w : Fin 15 → ZMod 37),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  letI : Fact (1 < (37:ℕ)) := ⟨by decide⟩
  have H : Roots (22:ZMod 37) 28 19 := ⟨by decide,by decide,by decide⟩
  have hd : (D:ZMod 37)*30=1 := by decide +kernel
  exact exact_with_roots H (IsUnit.of_mul_eq_one _ hd)

theorem exact_mod227 :
    ∃ (U : Matrix (Fin 15) (Fin 15) (ZMod 227)) (w : Fin 15 → ZMod 227),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  letI : Fact (1 < (227:ℕ)) := ⟨by decide⟩
  have H : Roots (177:ZMod 227) 190 149 := ⟨by decide,by decide,by decide⟩
  have hd : (D:ZMod 227)*64=1 := by decide +kernel
  exact exact_with_roots H (IsUnit.of_mul_eq_one _ hd)

theorem exact_mod11_degree_four :
    ∃ (U : Matrix (Fin 15) (Fin 15) CharEleven.K2) (w : Fin 15 → CharEleven.K2),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exact_with_roots CharEleven.root_triple (IsUnit.of_mul_eq_one _ CharEleven.denominator_paid)

theorem exact_nilpotent37 {R : Type*} [CommRing R] [Nontrivial R] (h : IsNilpotent (37:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨x,y,z,hr,hu⟩ := lift_root_residues (R:=R) rootResidues37
    (by simpa only [Int.cast_ofNat] using h)
  exact exact_with_roots hr hu

theorem exact_nilpotent227 {R : Type*} [CommRing R] [Nontrivial R] (h : IsNilpotent (227:R)) :
    ∃ (U : Matrix (Fin 15) (Fin 15) R) (w : Fin 15 → R),
      ERK U ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨x,y,z,hr,hu⟩ := lift_root_residues (R:=R) rootResidues227
    (by simpa only [Int.cast_ofNat] using h)
  exact exact_with_roots hr hu

end RKResearch.Certified.ERK10Stepanov


#print axioms RKResearch.Certified.ERK10Stepanov.exact_mod37
#print axioms RKResearch.Certified.ERK10Stepanov.exact_mod227
#print axioms RKResearch.Certified.ERK10Stepanov.exact_mod11_degree_four
#print axioms RKResearch.Certified.ERK10Stepanov.exact_nilpotent37
#print axioms RKResearch.Certified.ERK10Stepanov.exact_nilpotent227
