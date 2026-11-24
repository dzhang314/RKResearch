module

public import RKCert.ReviewedNative.SDIRKNineReplayP16
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.SDIRKNineReplay

open RKResearch FiniteRootedTree
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 4500000
set_option maxRecDepth 12000

theorem pay7 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree7 := by
  have hφ : Φ tree7 (numA x y) = Φ tree6 (numA x y) := by
    rw [phi7 h, phi6 h]
  have hn : (tree7.order:ℕ) = (tree6.order:ℕ) := by decide +kernel
  have hf : tree7.factorial = tree6.factorial := by decide +kernel
  change (tree7.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree7 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree7.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay6 h

theorem pay12 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree12 := by
  have hφ : Φ tree12 (numA x y) = Φ tree11 (numA x y) := by
    rw [phi12 h, phi11 h]
  have hn : (tree12.order:ℕ) = (tree11.order:ℕ) := by decide +kernel
  have hf : tree12.factorial = tree11.factorial := by decide +kernel
  change (tree12.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree12 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree12.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay11 h

theorem pay18 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree18 := by
  have hφ : Φ tree18 (numA x y) = Φ tree14 (numA x y) := by
    rw [phi18 h, phi14 h]
  have hn : (tree18.order:ℕ) = (tree14.order:ℕ) := by decide +kernel
  have hf : tree18.factorial = tree14.factorial := by decide +kernel
  change (tree18.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree18 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree18.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay14 h

theorem pay19 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree19 := by
  have hφ : Φ tree19 (numA x y) = Φ tree15 (numA x y) := by
    rw [phi19 h, phi15 h]
  have hn : (tree19.order:ℕ) = (tree15.order:ℕ) := by decide +kernel
  have hf : tree19.factorial = tree15.factorial := by decide +kernel
  change (tree19.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree19 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree19.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay15 h

theorem pay20 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree20 := by
  have hφ : Φ tree20 (numA x y) = Φ tree17 (numA x y) := by
    rw [phi20 h, phi17 h]
  have hn : (tree20.order:ℕ) = (tree17.order:ℕ) := by decide +kernel
  have hf : tree20.factorial = tree17.factorial := by decide +kernel
  change (tree20.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree20 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree20.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay17 h

theorem pay21 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree21 := by
  have hφ : Φ tree21 (numA x y) = Φ tree17 (numA x y) := by
    rw [phi21 h, phi17 h]
  have hn : (tree21.order:ℕ) = (tree17.order:ℕ) := by decide +kernel
  have hf : tree21.factorial = tree17.factorial := by decide +kernel
  change (tree21.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree21 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree21.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay17 h

theorem pay26 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree26 := by
  have hφ : Φ tree26 (numA x y) = Φ tree25 (numA x y) := by
    rw [phi26 h, phi25 h]
  have hn : (tree26.order:ℕ) = (tree25.order:ℕ) := by decide +kernel
  have hf : tree26.factorial = tree25.factorial := by decide +kernel
  change (tree26.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree26 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree26.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay25 h

theorem pay32 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree32 := by
  have hφ : Φ tree32 (numA x y) = Φ tree28 (numA x y) := by
    rw [phi32 h, phi28 h]
  have hn : (tree32.order:ℕ) = (tree28.order:ℕ) := by decide +kernel
  have hf : tree32.factorial = tree28.factorial := by decide +kernel
  change (tree32.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree32 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree32.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay28 h

theorem pay33 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree33 := by
  have hφ : Φ tree33 (numA x y) = Φ tree29 (numA x y) := by
    rw [phi33 h, phi29 h]
  have hn : (tree33.order:ℕ) = (tree29.order:ℕ) := by decide +kernel
  have hf : tree33.factorial = tree29.factorial := by decide +kernel
  change (tree33.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree33 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree33.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay29 h

theorem pay34 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree34 := by
  have hφ : Φ tree34 (numA x y) = Φ tree31 (numA x y) := by
    rw [phi34 h, phi31 h]
  have hn : (tree34.order:ℕ) = (tree31.order:ℕ) := by decide +kernel
  have hf : tree34.factorial = tree31.factorial := by decide +kernel
  change (tree34.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree34 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree34.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay31 h

theorem pay35 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree35 := by
  have hφ : Φ tree35 (numA x y) = Φ tree31 (numA x y) := by
    rw [phi35 h, phi31 h]
  have hn : (tree35.order:ℕ) = (tree31.order:ℕ) := by decide +kernel
  have hf : tree35.factorial = tree31.factorial := by decide +kernel
  change (tree35.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree35 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree35.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay31 h


end RKResearch.Certified.SDIRKNineReplay
