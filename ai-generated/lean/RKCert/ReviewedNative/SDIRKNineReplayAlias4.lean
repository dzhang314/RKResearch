module

public import RKCert.ReviewedNative.SDIRKNineReplayAlias3
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

theorem pay160 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree160 := by
  have hφ : Φ tree160 (numA x y) = Φ tree112 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree14 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree14 (numA x y)))
    rw [phi14 h, phi0 h, act12 h, act0 h]
    all_goals ac_rfl
  have hn : (tree160.order:ℕ) = (tree112.order:ℕ) := by decide +kernel
  have hf : tree160.factorial = tree112.factorial := by decide +kernel
  change (tree160.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree160 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree160.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay112 h

theorem pay161 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree161 := by
  have hφ : Φ tree161 (numA x y) = Φ tree113 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree15 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree15 (numA x y)))
    rw [phi15 h, phi0 h, act13 h, act0 h]
    all_goals ac_rfl
  have hn : (tree161.order:ℕ) = (tree113.order:ℕ) := by decide +kernel
  have hf : tree161.factorial = tree113.factorial := by decide +kernel
  change (tree161.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree161 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree161.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay113 h

theorem pay162 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree162 := by
  have hφ : Φ tree162 (numA x y) = Φ tree114 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree16 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree16 (numA x y)))
    rw [phi16 h, phi0 h, act14 h, act0 h]
    all_goals ac_rfl
  have hn : (tree162.order:ℕ) = (tree114.order:ℕ) := by decide +kernel
  have hf : tree162.factorial = tree114.factorial := by decide +kernel
  change (tree162.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree162 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree162.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay114 h

theorem pay163 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree163 := by
  have hφ : Φ tree163 (numA x y) = Φ tree115 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree17 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree17 (numA x y)))
    rw [phi17 h, phi0 h, act15 h, act0 h]
    all_goals ac_rfl
  have hn : (tree163.order:ℕ) = (tree115.order:ℕ) := by decide +kernel
  have hf : tree163.factorial = tree115.factorial := by decide +kernel
  change (tree163.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree163 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree163.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay115 h

theorem pay164 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree164 := by
  have hφ : Φ tree164 (numA x y) = Φ tree112 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree18 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree14 (numA x y)))
    rw [phi18 h, phi0 h, phi14 h, act12 h, act0 h]
    all_goals ac_rfl
  have hn : (tree164.order:ℕ) = (tree112.order:ℕ) := by decide +kernel
  have hf : tree164.factorial = tree112.factorial := by decide +kernel
  change (tree164.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree164 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree164.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay112 h

theorem pay165 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree165 := by
  have hφ : Φ tree165 (numA x y) = Φ tree113 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree19 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree15 (numA x y)))
    rw [phi19 h, phi0 h, phi15 h, act13 h, act0 h]
    all_goals ac_rfl
  have hn : (tree165.order:ℕ) = (tree113.order:ℕ) := by decide +kernel
  have hf : tree165.factorial = tree113.factorial := by decide +kernel
  change (tree165.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree165 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree165.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay113 h

theorem pay166 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree166 := by
  have hφ : Φ tree166 (numA x y) = Φ tree115 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree20 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree17 (numA x y)))
    rw [phi20 h, phi0 h, phi17 h, act15 h, act0 h]
    all_goals ac_rfl
  have hn : (tree166.order:ℕ) = (tree115.order:ℕ) := by decide +kernel
  have hf : tree166.factorial = tree115.factorial := by decide +kernel
  change (tree166.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree166 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree166.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay115 h

theorem pay167 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree167 := by
  have hφ : Φ tree167 (numA x y) = Φ tree115 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree21 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree17 (numA x y)))
    rw [phi21 h, phi0 h, phi17 h, act15 h, act0 h]
    all_goals ac_rfl
  have hn : (tree167.order:ℕ) = (tree115.order:ℕ) := by decide +kernel
  have hf : tree167.factorial = tree115.factorial := by decide +kernel
  change (tree167.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree167 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree167.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay115 h

theorem pay168 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree168 := by
  have hφ : Φ tree168 (numA x y) = Φ tree120 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree22 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree22 (numA x y)))
    rw [phi22 h, phi0 h, act16 h, act0 h]
    all_goals ac_rfl
  have hn : (tree168.order:ℕ) = (tree120.order:ℕ) := by decide +kernel
  have hf : tree168.factorial = tree120.factorial := by decide +kernel
  change (tree168.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree168 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree168.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay120 h

theorem pay169 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree169 := by
  have hφ : Φ tree169 (numA x y) = Φ tree126 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree4 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree4 (numA x y)))
    rw [phi0 h, phi4 h, act0 h, act4 h]
    all_goals ac_rfl
  have hn : (tree169.order:ℕ) = (tree126.order:ℕ) := by decide +kernel
  have hf : tree169.factorial = tree126.factorial := by decide +kernel
  change (tree169.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree169 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree169.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay126 h

theorem pay170 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree170 := by
  have hφ : Φ tree170 (numA x y) = Φ tree127 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree5 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree5 (numA x y)))
    rw [phi0 h, phi5 h, act0 h, act5 h]
    all_goals ac_rfl
  have hn : (tree170.order:ℕ) = (tree127.order:ℕ) := by decide +kernel
  have hf : tree170.factorial = tree127.factorial := by decide +kernel
  change (tree170.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree170 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree170.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay127 h

theorem pay171 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree171 := by
  have hφ : Φ tree171 (numA x y) = Φ tree128 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi0 h, phi6 h, act0 h, act6 h]
    all_goals ac_rfl
  have hn : (tree171.order:ℕ) = (tree128.order:ℕ) := by decide +kernel
  have hf : tree171.factorial = tree128.factorial := by decide +kernel
  change (tree171.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree171 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree171.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay128 h

theorem pay172 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree172 := by
  have hφ : Φ tree172 (numA x y) = Φ tree128 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree7 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi0 h, phi7 h, phi6 h, act0 h, act6 h]
    all_goals ac_rfl
  have hn : (tree172.order:ℕ) = (tree128.order:ℕ) := by decide +kernel
  have hf : tree172.factorial = tree128.factorial := by decide +kernel
  change (tree172.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree172 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree172.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay128 h

theorem pay173 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree173 := by
  have hφ : Φ tree173 (numA x y) = Φ tree130 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree8 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree8 (numA x y)))
    rw [phi0 h, phi8 h, act0 h, act7 h]
    all_goals ac_rfl
  have hn : (tree173.order:ℕ) = (tree130.order:ℕ) := by decide +kernel
  have hf : tree173.factorial = tree130.factorial := by decide +kernel
  change (tree173.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree173 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree173.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay130 h

theorem pay174 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree174 := by
  have hφ : Φ tree174 (numA x y) = Φ tree135 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi1 h, phi2 h, phi0 h, act1 h, act2 h, act0 h]
    all_goals ac_rfl
  have hn : (tree174.order:ℕ) = (tree135.order:ℕ) := by decide +kernel
  have hf : tree174.factorial = tree135.factorial := by decide +kernel
  change (tree174.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree174 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree174.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay135 h

theorem pay175 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree175 := by
  have hφ : Φ tree175 (numA x y) = Φ tree136 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi1 h, phi3 h, phi0 h, act1 h, act3 h, act0 h]
    all_goals ac_rfl
  have hn : (tree175.order:ℕ) = (tree136.order:ℕ) := by decide +kernel
  have hf : tree175.factorial = tree136.factorial := by decide +kernel
  change (tree175.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree175 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree175.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay136 h

theorem pay176 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree176 := by
  have hφ : Φ tree176 (numA x y) = Φ tree139 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi0 h, phi2 h, act0 h, act2 h]
    all_goals ac_rfl
  have hn : (tree176.order:ℕ) = (tree139.order:ℕ) := by decide +kernel
  have hf : tree176.factorial = tree139.factorial := by decide +kernel
  change (tree176.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree176 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree176.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay139 h

theorem pay177 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree177 := by
  have hφ : Φ tree177 (numA x y) = Φ tree140 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi0 h, phi3 h, act0 h, act3 h]
    all_goals ac_rfl
  have hn : (tree177.order:ℕ) = (tree140.order:ℕ) := by decide +kernel
  have hf : tree177.factorial = tree140.factorial := by decide +kernel
  change (tree177.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree177 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree177.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay140 h

theorem pay178 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree178 := by
  have hφ : Φ tree178 (numA x y) = Φ tree135 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi2 h, phi1 h, phi0 h, act2 h, act1 h, act0 h]
    all_goals ac_rfl
  have hn : (tree178.order:ℕ) = (tree135.order:ℕ) := by decide +kernel
  have hf : tree178.factorial = tree135.factorial := by decide +kernel
  change (tree178.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree178 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree178.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay135 h

theorem pay179 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree179 := by
  have hφ : Φ tree179 (numA x y) = Φ tree136 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi3 h, phi1 h, phi0 h, act3 h, act1 h, act0 h]
    all_goals ac_rfl
  have hn : (tree179.order:ℕ) = (tree136.order:ℕ) := by decide +kernel
  have hf : tree179.factorial = tree136.factorial := by decide +kernel
  change (tree179.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree179 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree179.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay136 h

theorem pay180 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree180 := by
  have hφ : Φ tree180 (numA x y) = Φ tree149 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi0 h, phi1 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree180.order:ℕ) = (tree149.order:ℕ) := by decide +kernel
  have hf : tree180.factorial = tree149.factorial := by decide +kernel
  change (tree180.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree180 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree180.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay149 h

theorem pay181 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree181 := by
  have hφ : Φ tree181 (numA x y) = Φ tree149 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi1 h, phi0 h, act1 h, act0 h]
    all_goals ac_rfl
  have hn : (tree181.order:ℕ) = (tree149.order:ℕ) := by decide +kernel
  have hf : tree181.factorial = tree149.factorial := by decide +kernel
  change (tree181.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree181 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree181.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay149 h

theorem pay182 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree182 := by
  have hφ : Φ tree182 (numA x y) = Φ tree154 (numA x y) := by
    change ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi0 h, phi1 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree182.order:ℕ) = (tree154.order:ℕ) := by decide +kernel
  have hf : tree182.factorial = tree154.factorial := by decide +kernel
  change (tree182.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree182 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree182.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay154 h

theorem pay183 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree183 := by
  have hφ : Φ tree183 (numA x y) = Φ tree126 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree4 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree4 (numA x y)))
    rw [phi4 h, phi0 h, act4 h, act0 h]
    all_goals ac_rfl
  have hn : (tree183.order:ℕ) = (tree126.order:ℕ) := by decide +kernel
  have hf : tree183.factorial = tree126.factorial := by decide +kernel
  change (tree183.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree183 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree183.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay126 h

theorem pay184 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree184 := by
  have hφ : Φ tree184 (numA x y) = Φ tree127 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree5 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree5 (numA x y)))
    rw [phi5 h, phi0 h, act5 h, act0 h]
    all_goals ac_rfl
  have hn : (tree184.order:ℕ) = (tree127.order:ℕ) := by decide +kernel
  have hf : tree184.factorial = tree127.factorial := by decide +kernel
  change (tree184.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree184 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree184.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay127 h

theorem pay185 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree185 := by
  have hφ : Φ tree185 (numA x y) = Φ tree128 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree6 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi6 h, phi0 h, act6 h, act0 h]
    all_goals ac_rfl
  have hn : (tree185.order:ℕ) = (tree128.order:ℕ) := by decide +kernel
  have hf : tree185.factorial = tree128.factorial := by decide +kernel
  change (tree185.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree185 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree185.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay128 h

theorem pay186 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree186 := by
  have hφ : Φ tree186 (numA x y) = Φ tree128 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree7 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi7 h, phi0 h, phi6 h, act6 h, act0 h]
    all_goals ac_rfl
  have hn : (tree186.order:ℕ) = (tree128.order:ℕ) := by decide +kernel
  have hf : tree186.factorial = tree128.factorial := by decide +kernel
  change (tree186.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree186 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree186.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay128 h

theorem pay187 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree187 := by
  have hφ : Φ tree187 (numA x y) = Φ tree130 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree8 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree8 (numA x y)))
    rw [phi8 h, phi0 h, act7 h, act0 h]
    all_goals ac_rfl
  have hn : (tree187.order:ℕ) = (tree130.order:ℕ) := by decide +kernel
  have hf : tree187.factorial = tree130.factorial := by decide +kernel
  change (tree187.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree187 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree187.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay130 h

theorem pay188 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree188 := by
  have hφ : Φ tree188 (numA x y) = Φ tree139 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi0 h, phi2 h, act0 h, act2 h]
    all_goals ac_rfl
  have hn : (tree188.order:ℕ) = (tree139.order:ℕ) := by decide +kernel
  have hf : tree188.factorial = tree139.factorial := by decide +kernel
  change (tree188.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree188 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree188.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay139 h

theorem pay189 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree189 := by
  have hφ : Φ tree189 (numA x y) = Φ tree140 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi0 h, phi3 h, act0 h, act3 h]
    all_goals ac_rfl
  have hn : (tree189.order:ℕ) = (tree140.order:ℕ) := by decide +kernel
  have hf : tree189.factorial = tree140.factorial := by decide +kernel
  change (tree189.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree189 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree189.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay140 h

theorem pay190 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree190 := by
  have hφ : Φ tree190 (numA x y) = Φ tree149 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi1 h, phi0 h, act1 h, act0 h]
    all_goals ac_rfl
  have hn : (tree190.order:ℕ) = (tree149.order:ℕ) := by decide +kernel
  have hf : tree190.factorial = tree149.factorial := by decide +kernel
  change (tree190.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree190 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree190.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay149 h

theorem pay191 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree191 := by
  have hφ : Φ tree191 (numA x y) = Φ tree154 (numA x y) := by
    change ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi0 h, phi1 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree191.order:ℕ) = (tree154.order:ℕ) := by decide +kernel
  have hf : tree191.factorial = tree154.factorial := by decide +kernel
  change (tree191.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree191 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree191.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay154 h

theorem pay192 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree192 := by
  have hφ : Φ tree192 (numA x y) = Φ tree139 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi2 h, phi0 h, act2 h, act0 h]
    all_goals ac_rfl
  have hn : (tree192.order:ℕ) = (tree139.order:ℕ) := by decide +kernel
  have hf : tree192.factorial = tree139.factorial := by decide +kernel
  change (tree192.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree192 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree192.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay139 h

theorem pay193 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree193 := by
  have hφ : Φ tree193 (numA x y) = Φ tree140 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi3 h, phi0 h, act3 h, act0 h]
    all_goals ac_rfl
  have hn : (tree193.order:ℕ) = (tree140.order:ℕ) := by decide +kernel
  have hf : tree193.factorial = tree140.factorial := by decide +kernel
  change (tree193.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree193 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree193.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay140 h

theorem pay194 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree194 := by
  have hφ : Φ tree194 (numA x y) = Φ tree154 (numA x y) := by
    change ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi0 h, phi1 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree194.order:ℕ) = (tree154.order:ℕ) := by decide +kernel
  have hf : tree194.factorial = tree154.factorial := by decide +kernel
  change (tree194.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree194 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree194.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay154 h

theorem pay195 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree195 := by
  have hφ : Φ tree195 (numA x y) = Φ tree154 (numA x y) := by
    change ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi1 h, phi0 h, act1 h, act0 h]
    all_goals ac_rfl
  have hn : (tree195.order:ℕ) = (tree154.order:ℕ) := by decide +kernel
  have hf : tree195.factorial = tree154.factorial := by decide +kernel
  change (tree195.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree195 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree195.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay154 h


end RKResearch.Certified.SDIRKNineReplay
