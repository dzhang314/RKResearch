module

public import RKCert.ReviewedNative.ERK10StepanovLiterals
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

/-! A concrete finite field of size 11^4 contains this fixture's nested
roots. The two irreducibility checks only enumerate pairs over F11,
and the coefficient denominator survives characteristic eleven. -/

namespace RKResearch.Certified.ERK10Stepanov.CharEleven
open ERKNestedRadicalReplay QuadraticAlgebra

local instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩

abbrev K1 := QuadraticAlgebra (ZMod 11) 7 0
def rad : K1 := (147:K1) + 42*ω
abbrev K2 := QuadraticAlgebra K1 rad 0

private theorem no_root_one : ∀ a : ZMod 11, a^2 ≠ (7:ZMod 11) := by decide +kernel

private theorem no_root_data (a b : ZMod 11) :
    ¬ (a*a+7*(b*b) = 4 ∧ a*b+b*a = 9) :=
  (by decide +kernel : ∀ a b : ZMod 11, ¬ (a*a+7*(b*b) = 4 ∧ a*b+b*a=9)) a b

private theorem no_root_two (a : K1) : a^2 ≠ rad := by
  intro ha
  have hre := congrArg QuadraticAlgebra.re ha
  have him := congrArg QuadraticAlgebra.im ha
  have er : (rad : K1).re = (4:ZMod 11) := by decide +kernel
  have ei : (rad : K1).im = (9:ZMod 11) := by decide +kernel
  apply no_root_data a.re a.im
  constructor
  · simpa only [pow_two,QuadraticAlgebra.re_mul,er,mul_assoc] using hre
  · simpa only [pow_two,QuadraticAlgebra.im_mul,ei,zero_mul,zero_add,add_zero] using him

local instance i1 : Fact (∀ a : ZMod 11, a^2 ≠ 7+0*a) := ⟨by simpa using no_root_one⟩
instance : Field K1 := inferInstance
local instance i2 : Fact (∀ a : K1, a^2 ≠ rad+0*a) :=
  ⟨by simpa using no_root_two⟩
instance : Field K2 := inferInstance

instance : CharP K1 11 := charP_of_injective_algebraMap' (ZMod 11) 11
instance : CharP K2 11 := charP_of_injective_algebraMap' K1 11

private theorem card_quad {F : Type*} (a b : F) :
    Nat.card (QuadraticAlgebra F a b) = (Nat.card F)^2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd a b), Nat.card_prod,pow_two]

theorem cardinality : Nat.card K2 = 11^4 := by
  rw [card_quad,card_quad,Nat.card_eq_fintype_card,ZMod.card]
  decide

private def f : ZMod 11 →+* K2 :=
  (algebraMap K1 K2).comp (algebraMap (ZMod 11) K1)

theorem root_triple :
    Roots (5:K2) (algebraMap K1 K2 (ω:K1)) (ω:K2) := by
  have hx : (5:K2)*5=3 := by
    have ht := congrArg f (show (5:ZMod 11)*5=3 by decide)
    simpa only [map_mul,map_ofNat] using ht
  have hy0 : (ω:K1)*ω=7 := by
    have h := omega_mul_omega_eq_algebraMap (R := ZMod 11) (a := 7) (b := 0)
    simpa only [map_ofNat,map_zero,zero_mul,add_zero] using h
  have hy : algebraMap K1 K2 (ω:K1) * algebraMap K1 K2 (ω:K1)=7 := by
    have h := congrArg (algebraMap K1 K2) hy0
    simpa only [map_mul,map_ofNat] using h
  have hz : (ω:K2)*ω=147+42*algebraMap K1 K2 (ω:K1) := by
    calc
      (ω:K2)*ω = algebraMap K1 K2 rad + algebraMap K1 K2 (0:K1) * ω :=
        omega_mul_omega_eq_algebraMap (R := K1) (a := rad) (b := 0)
      _ = algebraMap K1 K2 rad := by simp
      _ = algebraMap K1 K2 ((147:K1)+42*ω) := rfl
      _ = 147+42*algebraMap K1 K2 (ω:K1) := by
        have h147 : algebraMap K1 K2 (147:K1) = (147:K2) := by decide +kernel
        have h42 : algebraMap K1 K2 (42:K1) = (42:K2) := by decide +kernel
        rw [map_add,map_mul,h147,h42]
  exact ⟨hx,hy,hz⟩

theorem denominator_paid : (D:K2)*2=1 := by
  have h := congrArg f (show (D:ZMod 11)*2=1 by decide +kernel)
  simpa only [map_mul,map_intCast,map_ofNat,map_one] using h

end RKResearch.Certified.ERK10Stepanov.CharEleven

#print axioms RKResearch.Certified.ERK10Stepanov.CharEleven.root_triple
#print axioms RKResearch.Certified.ERK10Stepanov.CharEleven.cardinality
