module

public import RKCert.ReviewedNative.SDIRKNineReplayAlias2
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

theorem pay124 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree124 := by
  have hφ : Φ tree124 (numA x y) = Φ tree123 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree7 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi1 h, phi7 h, phi6 h, act1 h, act6 h]
    all_goals ac_rfl
  have hn : (tree124.order:ℕ) = (tree123.order:ℕ) := by decide +kernel
  have hf : tree124.factorial = tree123.factorial := by decide +kernel
  change (tree124.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree124 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree124.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay123 h

theorem pay129 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree129 := by
  have hφ : Φ tree129 (numA x y) = Φ tree128 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree7 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi0 h, phi7 h, phi6 h, act0 h, act6 h]
    all_goals ac_rfl
  have hn : (tree129.order:ℕ) = (tree128.order:ℕ) := by decide +kernel
  have hf : tree129.factorial = tree128.factorial := by decide +kernel
  change (tree129.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree129 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree129.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay128 h

theorem pay133 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree133 := by
  have hφ : Φ tree133 (numA x y) = Φ tree132 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi3 h, phi2 h, act3 h, act2 h]
    all_goals ac_rfl
  have hn : (tree133.order:ℕ) = (tree132.order:ℕ) := by decide +kernel
  have hf : tree133.factorial = tree132.factorial := by decide +kernel
  change (tree133.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree133 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree133.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay132 h

theorem pay137 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree137 := by
  have hφ : Φ tree137 (numA x y) = Φ tree135 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi1 h, phi0 h, phi2 h, act1 h, act0 h, act2 h]
    all_goals ac_rfl
  have hn : (tree137.order:ℕ) = (tree135.order:ℕ) := by decide +kernel
  have hf : tree137.factorial = tree135.factorial := by decide +kernel
  change (tree137.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree137 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree137.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay135 h

theorem pay138 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree138 := by
  have hφ : Φ tree138 (numA x y) = Φ tree136 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi1 h, phi0 h, phi3 h, act1 h, act0 h, act3 h]
    all_goals ac_rfl
  have hn : (tree138.order:ℕ) = (tree136.order:ℕ) := by decide +kernel
  have hf : tree138.factorial = tree136.factorial := by decide +kernel
  change (tree138.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree138 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree138.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay136 h

theorem pay141 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree141 := by
  have hφ : Φ tree141 (numA x y) = Φ tree121 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree4 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree4 (numA x y)))
    rw [phi4 h, phi1 h, act4 h, act1 h]
    all_goals ac_rfl
  have hn : (tree141.order:ℕ) = (tree121.order:ℕ) := by decide +kernel
  have hf : tree141.factorial = tree121.factorial := by decide +kernel
  change (tree141.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree141 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree141.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay121 h

theorem pay142 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree142 := by
  have hφ : Φ tree142 (numA x y) = Φ tree122 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree5 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree5 (numA x y)))
    rw [phi5 h, phi1 h, act5 h, act1 h]
    all_goals ac_rfl
  have hn : (tree142.order:ℕ) = (tree122.order:ℕ) := by decide +kernel
  have hf : tree142.factorial = tree122.factorial := by decide +kernel
  change (tree142.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree142 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree142.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay122 h

theorem pay143 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree143 := by
  have hφ : Φ tree143 (numA x y) = Φ tree123 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree6 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi6 h, phi1 h, act6 h, act1 h]
    all_goals ac_rfl
  have hn : (tree143.order:ℕ) = (tree123.order:ℕ) := by decide +kernel
  have hf : tree143.factorial = tree123.factorial := by decide +kernel
  change (tree143.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree143 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree143.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay123 h

theorem pay144 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree144 := by
  have hφ : Φ tree144 (numA x y) = Φ tree123 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree7 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
    rw [phi7 h, phi1 h, phi6 h, act6 h, act1 h]
    all_goals ac_rfl
  have hn : (tree144.order:ℕ) = (tree123.order:ℕ) := by decide +kernel
  have hf : tree144.factorial = tree123.factorial := by decide +kernel
  change (tree144.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree144 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree144.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay123 h

theorem pay145 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree145 := by
  have hφ : Φ tree145 (numA x y) = Φ tree125 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree8 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree8 (numA x y)))
    rw [phi8 h, phi1 h, act7 h, act1 h]
    all_goals ac_rfl
  have hn : (tree145.order:ℕ) = (tree125.order:ℕ) := by decide +kernel
  have hf : tree145.factorial = tree125.factorial := by decide +kernel
  change (tree145.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree145 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree145.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay125 h

theorem pay146 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree146 := by
  have hφ : Φ tree146 (numA x y) = Φ tree135 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi0 h, phi2 h, phi1 h, act0 h, act2 h, act1 h]
    all_goals ac_rfl
  have hn : (tree146.order:ℕ) = (tree135.order:ℕ) := by decide +kernel
  have hf : tree146.factorial = tree135.factorial := by decide +kernel
  change (tree146.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree146 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree146.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay135 h

theorem pay147 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree147 := by
  have hφ : Φ tree147 (numA x y) = Φ tree136 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi0 h, phi3 h, phi1 h, act0 h, act3 h, act1 h]
    all_goals ac_rfl
  have hn : (tree147.order:ℕ) = (tree136.order:ℕ) := by decide +kernel
  have hf : tree147.factorial = tree136.factorial := by decide +kernel
  change (tree147.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree147 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree147.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay136 h

theorem pay150 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree150 := by
  have hφ : Φ tree150 (numA x y) = Φ tree135 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
    rw [phi2 h, phi0 h, phi1 h, act2 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree150.order:ℕ) = (tree135.order:ℕ) := by decide +kernel
  have hf : tree150.factorial = tree135.factorial := by decide +kernel
  change (tree150.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree150 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree150.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay135 h

theorem pay151 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree151 := by
  have hφ : Φ tree151 (numA x y) = Φ tree136 (numA x y) := by
    change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
    rw [phi3 h, phi0 h, phi1 h, act3 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree151.order:ℕ) = (tree136.order:ℕ) := by decide +kernel
  have hf : tree151.factorial = tree136.factorial := by decide +kernel
  change (tree151.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree151 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree151.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay136 h

theorem pay152 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree152 := by
  have hφ : Φ tree152 (numA x y) = Φ tree149 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi0 h, phi1 h, act0 h, act1 h]
    all_goals ac_rfl
  have hn : (tree152.order:ℕ) = (tree149.order:ℕ) := by decide +kernel
  have hf : tree152.factorial = tree149.factorial := by decide +kernel
  change (tree152.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree152 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree152.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay149 h

theorem pay153 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree153 := by
  have hφ : Φ tree153 (numA x y) = Φ tree149 (numA x y) := by
    change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
    rw [phi1 h, phi0 h, act1 h, act0 h]
    all_goals ac_rfl
  have hn : (tree153.order:ℕ) = (tree149.order:ℕ) := by decide +kernel
  have hf : tree153.factorial = tree149.factorial := by decide +kernel
  change (tree153.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree153 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree153.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay149 h

theorem pay155 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree155 := by
  have hφ : Φ tree155 (numA x y) = Φ tree107 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree9 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree9 (numA x y)))
    rw [phi9 h, phi0 h, act8 h, act0 h]
    all_goals ac_rfl
  have hn : (tree155.order:ℕ) = (tree107.order:ℕ) := by decide +kernel
  have hf : tree155.factorial = tree107.factorial := by decide +kernel
  change (tree155.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree155 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree155.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay107 h

theorem pay156 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree156 := by
  have hφ : Φ tree156 (numA x y) = Φ tree108 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree10 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree10 (numA x y)))
    rw [phi10 h, phi0 h, act9 h, act0 h]
    all_goals ac_rfl
  have hn : (tree156.order:ℕ) = (tree108.order:ℕ) := by decide +kernel
  have hf : tree156.factorial = tree108.factorial := by decide +kernel
  change (tree156.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree156 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree156.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay108 h

theorem pay157 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree157 := by
  have hφ : Φ tree157 (numA x y) = Φ tree109 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree11 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree11 (numA x y)))
    rw [phi11 h, phi0 h, act10 h, act0 h]
    all_goals ac_rfl
  have hn : (tree157.order:ℕ) = (tree109.order:ℕ) := by decide +kernel
  have hf : tree157.factorial = tree109.factorial := by decide +kernel
  change (tree157.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree157 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree157.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay109 h

theorem pay158 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree158 := by
  have hφ : Φ tree158 (numA x y) = Φ tree109 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree12 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree11 (numA x y)))
    rw [phi12 h, phi0 h, phi11 h, act10 h, act0 h]
    all_goals ac_rfl
  have hn : (tree158.order:ℕ) = (tree109.order:ℕ) := by decide +kernel
  have hf : tree158.factorial = tree109.factorial := by decide +kernel
  change (tree158.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree158 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree158.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay109 h

theorem pay159 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree159 := by
  have hφ : Φ tree159 (numA x y) = Φ tree111 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree13 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree13 (numA x y)))
    rw [phi13 h, phi0 h, act11 h, act0 h]
    all_goals ac_rfl
  have hn : (tree159.order:ℕ) = (tree111.order:ℕ) := by decide +kernel
  have hf : tree159.factorial = tree111.factorial := by decide +kernel
  change (tree159.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree159 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree159.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay111 h


end RKResearch.Certified.SDIRKNineReplay
