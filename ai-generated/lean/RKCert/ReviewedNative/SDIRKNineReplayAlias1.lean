module

public import RKCert.ReviewedNative.SDIRKNineReplayAlias0
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

theorem pay40 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree40 := by
  have hφ : Φ tree40 (numA x y) = Φ tree39 (numA x y) := by
    rw [phi40 h, phi39 h]
  have hn : (tree40.order:ℕ) = (tree39.order:ℕ) := by decide +kernel
  have hf : tree40.factorial = tree39.factorial := by decide +kernel
  change (tree40.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree40 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree40.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay39 h

theorem pay46 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree46 := by
  have hφ : Φ tree46 (numA x y) = Φ tree42 (numA x y) := by
    rw [phi46 h, phi42 h]
  have hn : (tree46.order:ℕ) = (tree42.order:ℕ) := by decide +kernel
  have hf : tree46.factorial = tree42.factorial := by decide +kernel
  change (tree46.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree46 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree46.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay42 h

theorem pay47 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree47 := by
  have hφ : Φ tree47 (numA x y) = Φ tree43 (numA x y) := by
    rw [phi47 h, phi43 h]
  have hn : (tree47.order:ℕ) = (tree43.order:ℕ) := by decide +kernel
  have hf : tree47.factorial = tree43.factorial := by decide +kernel
  change (tree47.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree47 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree47.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay43 h

theorem pay49 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree49 := by
  have hφ : Φ tree49 (numA x y) = Φ tree48 (numA x y) := by
    rw [phi49 h, phi48 h]
  have hn : (tree49.order:ℕ) = (tree48.order:ℕ) := by decide +kernel
  have hf : tree49.factorial = tree48.factorial := by decide +kernel
  change (tree49.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree49 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree49.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay48 h

theorem pay51 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree51 := by
  have hφ : Φ tree51 (numA x y) = Φ tree37 (numA x y) := by
    rw [phi51 h, phi37 h]
  have hn : (tree51.order:ℕ) = (tree37.order:ℕ) := by decide +kernel
  have hf : tree51.factorial = tree37.factorial := by decide +kernel
  change (tree51.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree51 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree51.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay37 h

theorem pay52 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree52 := by
  have hφ : Φ tree52 (numA x y) = Φ tree38 (numA x y) := by
    rw [phi52 h, phi38 h]
  have hn : (tree52.order:ℕ) = (tree38.order:ℕ) := by decide +kernel
  have hf : tree52.factorial = tree38.factorial := by decide +kernel
  change (tree52.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree52 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree52.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay38 h

theorem pay53 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree53 := by
  have hφ : Φ tree53 (numA x y) = Φ tree39 (numA x y) := by
    rw [phi53 h, phi39 h]
  have hn : (tree53.order:ℕ) = (tree39.order:ℕ) := by decide +kernel
  have hf : tree53.factorial = tree39.factorial := by decide +kernel
  change (tree53.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree53 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree53.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay39 h

theorem pay54 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree54 := by
  have hφ : Φ tree54 (numA x y) = Φ tree39 (numA x y) := by
    rw [phi54 h, phi39 h]
  have hn : (tree54.order:ℕ) = (tree39.order:ℕ) := by decide +kernel
  have hf : tree54.factorial = tree39.factorial := by decide +kernel
  change (tree54.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree54 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree54.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay39 h

theorem pay55 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree55 := by
  have hφ : Φ tree55 (numA x y) = Φ tree41 (numA x y) := by
    rw [phi55 h, phi41 h]
  have hn : (tree55.order:ℕ) = (tree41.order:ℕ) := by decide +kernel
  have hf : tree55.factorial = tree41.factorial := by decide +kernel
  change (tree55.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree55 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree55.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay41 h

theorem pay56 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree56 := by
  have hφ : Φ tree56 (numA x y) = Φ tree44 (numA x y) := by
    rw [phi56 h, phi44 h]
  have hn : (tree56.order:ℕ) = (tree44.order:ℕ) := by decide +kernel
  have hf : tree56.factorial = tree44.factorial := by decide +kernel
  change (tree56.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree56 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree56.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay44 h

theorem pay57 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree57 := by
  have hφ : Φ tree57 (numA x y) = Φ tree45 (numA x y) := by
    rw [phi57 h, phi45 h]
  have hn : (tree57.order:ℕ) = (tree45.order:ℕ) := by decide +kernel
  have hf : tree57.factorial = tree45.factorial := by decide +kernel
  change (tree57.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree57 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree57.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay45 h

theorem pay58 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree58 := by
  have hφ : Φ tree58 (numA x y) = Φ tree48 (numA x y) := by
    rw [phi58 h, phi48 h]
  have hn : (tree58.order:ℕ) = (tree48.order:ℕ) := by decide +kernel
  have hf : tree58.factorial = tree48.factorial := by decide +kernel
  change (tree58.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree58 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree58.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay48 h

theorem pay59 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree59 := by
  have hφ : Φ tree59 (numA x y) = Φ tree50 (numA x y) := by
    rw [phi59 h, phi50 h]
  have hn : (tree59.order:ℕ) = (tree50.order:ℕ) := by decide +kernel
  have hf : tree59.factorial = tree50.factorial := by decide +kernel
  change (tree59.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree59 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree59.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay50 h

theorem pay60 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree60 := by
  have hφ : Φ tree60 (numA x y) = Φ tree44 (numA x y) := by
    rw [phi60 h, phi44 h]
  have hn : (tree60.order:ℕ) = (tree44.order:ℕ) := by decide +kernel
  have hf : tree60.factorial = tree44.factorial := by decide +kernel
  change (tree60.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree60 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree60.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay44 h

theorem pay61 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree61 := by
  have hφ : Φ tree61 (numA x y) = Φ tree45 (numA x y) := by
    rw [phi61 h, phi45 h]
  have hn : (tree61.order:ℕ) = (tree45.order:ℕ) := by decide +kernel
  have hf : tree61.factorial = tree45.factorial := by decide +kernel
  change (tree61.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree61 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree61.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay45 h

theorem pay62 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree62 := by
  have hφ : Φ tree62 (numA x y) = Φ tree50 (numA x y) := by
    rw [phi62 h, phi50 h]
  have hn : (tree62.order:ℕ) = (tree50.order:ℕ) := by decide +kernel
  have hf : tree62.factorial = tree50.factorial := by decide +kernel
  change (tree62.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree62 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree62.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay50 h

theorem pay63 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree63 := by
  have hφ : Φ tree63 (numA x y) = Φ tree50 (numA x y) := by
    rw [phi63 h, phi50 h]
  have hn : (tree63.order:ℕ) = (tree50.order:ℕ) := by decide +kernel
  have hf : tree63.factorial = tree50.factorial := by decide +kernel
  change (tree63.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree63 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree63.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay50 h

theorem pay68 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree68 := by
  have hφ : Φ tree68 (numA x y) = Φ tree67 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree26 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree25 (numA x y)))
    rw [phi26 h, phi25 h, act19 h]
    all_goals ac_rfl
  have hn : (tree68.order:ℕ) = (tree67.order:ℕ) := by decide +kernel
  have hf : tree68.factorial = tree67.factorial := by decide +kernel
  change (tree68.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree68 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree68.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay67 h

theorem pay74 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree74 := by
  have hφ : Φ tree74 (numA x y) = Φ tree70 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree32 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree28 (numA x y)))
    rw [phi32 h, phi28 h, act21 h]
    all_goals ac_rfl
  have hn : (tree74.order:ℕ) = (tree70.order:ℕ) := by decide +kernel
  have hf : tree74.factorial = tree70.factorial := by decide +kernel
  change (tree74.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree74 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree74.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay70 h

theorem pay75 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree75 := by
  have hφ : Φ tree75 (numA x y) = Φ tree71 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree33 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree29 (numA x y)))
    rw [phi33 h, phi29 h, act22 h]
    all_goals ac_rfl
  have hn : (tree75.order:ℕ) = (tree71.order:ℕ) := by decide +kernel
  have hf : tree75.factorial = tree71.factorial := by decide +kernel
  change (tree75.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree75 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree75.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay71 h

theorem pay76 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree76 := by
  have hφ : Φ tree76 (numA x y) = Φ tree73 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree34 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree31 (numA x y)))
    rw [phi34 h, phi31 h, act24 h]
    all_goals ac_rfl
  have hn : (tree76.order:ℕ) = (tree73.order:ℕ) := by decide +kernel
  have hf : tree76.factorial = tree73.factorial := by decide +kernel
  change (tree76.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree76 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree76.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay73 h

theorem pay77 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree77 := by
  have hφ : Φ tree77 (numA x y) = Φ tree73 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree35 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree31 (numA x y)))
    rw [phi35 h, phi31 h, act24 h]
    all_goals ac_rfl
  have hn : (tree77.order:ℕ) = (tree73.order:ℕ) := by decide +kernel
  have hf : tree77.factorial = tree73.factorial := by decide +kernel
  change (tree77.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree77 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree77.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay73 h


end RKResearch.Certified.SDIRKNineReplay
