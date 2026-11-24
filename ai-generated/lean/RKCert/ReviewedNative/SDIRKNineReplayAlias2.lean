module

public import RKCert.ReviewedNative.SDIRKNineReplayAlias1
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

theorem pay82 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree82 := by
  have hφ : Φ tree82 (numA x y) = Φ tree81 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree40 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree39 (numA x y)))
    rw [phi40 h, phi39 h, act28 h]
    all_goals ac_rfl
  have hn : (tree82.order:ℕ) = (tree81.order:ℕ) := by decide +kernel
  have hf : tree82.factorial = tree81.factorial := by decide +kernel
  change (tree82.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree82 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree82.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay81 h

theorem pay88 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree88 := by
  have hφ : Φ tree88 (numA x y) = Φ tree84 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree46 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree42 (numA x y)))
    rw [phi46 h, phi42 h, act30 h]
    all_goals ac_rfl
  have hn : (tree88.order:ℕ) = (tree84.order:ℕ) := by decide +kernel
  have hf : tree88.factorial = tree84.factorial := by decide +kernel
  change (tree88.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree88 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree88.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay84 h

theorem pay89 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree89 := by
  have hφ : Φ tree89 (numA x y) = Φ tree85 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree47 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree43 (numA x y)))
    rw [phi47 h, phi43 h, act31 h]
    all_goals ac_rfl
  have hn : (tree89.order:ℕ) = (tree85.order:ℕ) := by decide +kernel
  have hf : tree89.factorial = tree85.factorial := by decide +kernel
  change (tree89.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree89 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree89.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay85 h

theorem pay91 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree91 := by
  have hφ : Φ tree91 (numA x y) = Φ tree90 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree49 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree48 (numA x y)))
    rw [phi49 h, phi48 h, act34 h]
    all_goals ac_rfl
  have hn : (tree91.order:ℕ) = (tree90.order:ℕ) := by decide +kernel
  have hf : tree91.factorial = tree90.factorial := by decide +kernel
  change (tree91.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree91 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree91.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay90 h

theorem pay93 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree93 := by
  have hφ : Φ tree93 (numA x y) = Φ tree79 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree51 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree37 (numA x y)))
    rw [phi51 h, phi37 h, act26 h]
    all_goals ac_rfl
  have hn : (tree93.order:ℕ) = (tree79.order:ℕ) := by decide +kernel
  have hf : tree93.factorial = tree79.factorial := by decide +kernel
  change (tree93.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree93 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree93.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay79 h

theorem pay94 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree94 := by
  have hφ : Φ tree94 (numA x y) = Φ tree80 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree52 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree38 (numA x y)))
    rw [phi52 h, phi38 h, act27 h]
    all_goals ac_rfl
  have hn : (tree94.order:ℕ) = (tree80.order:ℕ) := by decide +kernel
  have hf : tree94.factorial = tree80.factorial := by decide +kernel
  change (tree94.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree94 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree94.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay80 h

theorem pay95 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree95 := by
  have hφ : Φ tree95 (numA x y) = Φ tree81 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree53 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree39 (numA x y)))
    rw [phi53 h, phi39 h, act28 h]
    all_goals ac_rfl
  have hn : (tree95.order:ℕ) = (tree81.order:ℕ) := by decide +kernel
  have hf : tree95.factorial = tree81.factorial := by decide +kernel
  change (tree95.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree95 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree95.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay81 h

theorem pay96 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree96 := by
  have hφ : Φ tree96 (numA x y) = Φ tree81 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree54 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree39 (numA x y)))
    rw [phi54 h, phi39 h, act28 h]
    all_goals ac_rfl
  have hn : (tree96.order:ℕ) = (tree81.order:ℕ) := by decide +kernel
  have hf : tree96.factorial = tree81.factorial := by decide +kernel
  change (tree96.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree96 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree96.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay81 h

theorem pay97 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree97 := by
  have hφ : Φ tree97 (numA x y) = Φ tree83 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree55 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree41 (numA x y)))
    rw [phi55 h, phi41 h, act29 h]
    all_goals ac_rfl
  have hn : (tree97.order:ℕ) = (tree83.order:ℕ) := by decide +kernel
  have hf : tree97.factorial = tree83.factorial := by decide +kernel
  change (tree97.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree97 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree97.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay83 h

theorem pay98 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree98 := by
  have hφ : Φ tree98 (numA x y) = Φ tree86 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree56 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree44 (numA x y)))
    rw [phi56 h, phi44 h, act32 h]
    all_goals ac_rfl
  have hn : (tree98.order:ℕ) = (tree86.order:ℕ) := by decide +kernel
  have hf : tree98.factorial = tree86.factorial := by decide +kernel
  change (tree98.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree98 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree98.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay86 h

theorem pay99 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree99 := by
  have hφ : Φ tree99 (numA x y) = Φ tree87 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree57 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree45 (numA x y)))
    rw [phi57 h, phi45 h, act33 h]
    all_goals ac_rfl
  have hn : (tree99.order:ℕ) = (tree87.order:ℕ) := by decide +kernel
  have hf : tree99.factorial = tree87.factorial := by decide +kernel
  change (tree99.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree99 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree99.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay87 h

theorem pay100 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree100 := by
  have hφ : Φ tree100 (numA x y) = Φ tree90 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree58 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree48 (numA x y)))
    rw [phi58 h, phi48 h, act34 h]
    all_goals ac_rfl
  have hn : (tree100.order:ℕ) = (tree90.order:ℕ) := by decide +kernel
  have hf : tree100.factorial = tree90.factorial := by decide +kernel
  change (tree100.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree100 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree100.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay90 h

theorem pay101 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree101 := by
  have hφ : Φ tree101 (numA x y) = Φ tree92 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree59 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree50 (numA x y)))
    rw [phi59 h, phi50 h, act35 h]
    all_goals ac_rfl
  have hn : (tree101.order:ℕ) = (tree92.order:ℕ) := by decide +kernel
  have hf : tree101.factorial = tree92.factorial := by decide +kernel
  change (tree101.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree101 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree101.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay92 h

theorem pay102 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree102 := by
  have hφ : Φ tree102 (numA x y) = Φ tree86 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree60 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree44 (numA x y)))
    rw [phi60 h, phi44 h, act32 h]
    all_goals ac_rfl
  have hn : (tree102.order:ℕ) = (tree86.order:ℕ) := by decide +kernel
  have hf : tree102.factorial = tree86.factorial := by decide +kernel
  change (tree102.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree102 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree102.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay86 h

theorem pay103 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree103 := by
  have hφ : Φ tree103 (numA x y) = Φ tree87 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree61 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree45 (numA x y)))
    rw [phi61 h, phi45 h, act33 h]
    all_goals ac_rfl
  have hn : (tree103.order:ℕ) = (tree87.order:ℕ) := by decide +kernel
  have hf : tree103.factorial = tree87.factorial := by decide +kernel
  change (tree103.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree103 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree103.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay87 h

theorem pay104 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree104 := by
  have hφ : Φ tree104 (numA x y) = Φ tree92 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree62 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree50 (numA x y)))
    rw [phi62 h, phi50 h, act35 h]
    all_goals ac_rfl
  have hn : (tree104.order:ℕ) = (tree92.order:ℕ) := by decide +kernel
  have hf : tree104.factorial = tree92.factorial := by decide +kernel
  change (tree104.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree104 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree104.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay92 h

theorem pay105 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree105 := by
  have hφ : Φ tree105 (numA x y) = Φ tree92 (numA x y) := by
    change ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree63 (numA x y))) = ((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree50 (numA x y)))
    rw [phi63 h, phi50 h, act35 h]
    all_goals ac_rfl
  have hn : (tree105.order:ℕ) = (tree92.order:ℕ) := by decide +kernel
  have hf : tree105.factorial = tree92.factorial := by decide +kernel
  change (tree105.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree105 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree105.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay92 h

theorem pay110 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree110 := by
  have hφ : Φ tree110 (numA x y) = Φ tree109 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree12 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree11 (numA x y)))
    rw [phi0 h, phi12 h, phi11 h, act0 h, act10 h]
    all_goals ac_rfl
  have hn : (tree110.order:ℕ) = (tree109.order:ℕ) := by decide +kernel
  have hf : tree110.factorial = tree109.factorial := by decide +kernel
  change (tree110.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree110 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree110.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay109 h

theorem pay116 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree116 := by
  have hφ : Φ tree116 (numA x y) = Φ tree112 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree18 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree14 (numA x y)))
    rw [phi0 h, phi18 h, phi14 h, act0 h, act12 h]
    all_goals ac_rfl
  have hn : (tree116.order:ℕ) = (tree112.order:ℕ) := by decide +kernel
  have hf : tree116.factorial = tree112.factorial := by decide +kernel
  change (tree116.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree116 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree116.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay112 h

theorem pay117 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree117 := by
  have hφ : Φ tree117 (numA x y) = Φ tree113 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree19 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree15 (numA x y)))
    rw [phi0 h, phi19 h, phi15 h, act0 h, act13 h]
    all_goals ac_rfl
  have hn : (tree117.order:ℕ) = (tree113.order:ℕ) := by decide +kernel
  have hf : tree117.factorial = tree113.factorial := by decide +kernel
  change (tree117.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree117 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree117.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay113 h

theorem pay118 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree118 := by
  have hφ : Φ tree118 (numA x y) = Φ tree115 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree20 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree17 (numA x y)))
    rw [phi0 h, phi20 h, phi17 h, act0 h, act15 h]
    all_goals ac_rfl
  have hn : (tree118.order:ℕ) = (tree115.order:ℕ) := by decide +kernel
  have hf : tree118.factorial = tree115.factorial := by decide +kernel
  change (tree118.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree118 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree118.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay115 h

theorem pay119 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree119 := by
  have hφ : Φ tree119 (numA x y) = Φ tree115 (numA x y) := by
    change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree21 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree17 (numA x y)))
    rw [phi0 h, phi21 h, phi17 h, act0 h, act15 h]
    all_goals ac_rfl
  have hn : (tree119.order:ℕ) = (tree115.order:ℕ) := by decide +kernel
  have hf : tree119.factorial = tree115.factorial := by decide +kernel
  change (tree119.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ tree119 (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((tree119.order:ℕ)-1)
  rw [hφ, hf, hn]
  exact pay115 h


end RKResearch.Certified.SDIRKNineReplay
