module

public import RKCert.ReviewedNative.CoordinateRootedTreeGram
public import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Quadratic coordinate controls

The coordinate order is real/second coefficient of stage 1, then the
two coefficients of stage 2, then the added rational grade coordinate.
The decoded multiplication is multiplication in the algebra with root
squaring to q. No ordering on that algebra is used in the verifier.
-/
namespace RKResearch.Certified.CoordinateRootedTreeGram.Controls

open FiniteRootedTree
open scoped Matrix BigOperators

abbrev K (q : ℤ) := QuadraticAlgebra ℚ (q : ℚ) 0

def quadTensor (q : ℤ) (a i j : Fin 5) : ℤ :=
  if a = 4 then
    if i = 4 ∧ j = 4 then 1 else 0
  else if i.val / 2 = a.val / 2 ∧ j.val / 2 = a.val / 2 then
    match a.val % 2, i.val % 2, j.val % 2 with
    | 0, 0, 0 => 1
    | 0, 1, 1 => q
    | 1, 0, 1 | 1, 1, 0 => 1
    | _, _, _ => 0
  else 0

def quadMachine (q : ℤ) (N I : Matrix (Fin 2) (Fin 2) ℤ) (d : ℤ) :
    Machine (Fin 5) where
  tensor := quadTensor q
  leaf := ![1,0,1,0,1]
  branch k :=
    !![(k:ℤ)*N 0 0,(k:ℤ)*q*I 0 0,(k:ℤ)*N 0 1,(k:ℤ)*q*I 0 1,0;
       (k:ℤ)*I 0 0,(k:ℤ)*N 0 0,(k:ℤ)*I 0 1,(k:ℤ)*N 0 1,0;
       (k:ℤ)*N 1 0,(k:ℤ)*q*I 1 0,(k:ℤ)*N 1 1,(k:ℤ)*q*I 1 1,0;
       (k:ℤ)*I 1 0,(k:ℤ)*N 1 0,(k:ℤ)*I 1 1,(k:ℤ)*N 1 1,0;
       0,0,0,0,d]

def quadOutput (q : ℤ) (u w : Fin 2 → ℤ) (e : ℤ) (n : ℕ) :
    Matrix (Fin 2) (Fin 5) ℤ :=
  !![(n:ℤ)*u 0,(n:ℤ)*q*w 0,(n:ℤ)*u 1,(n:ℤ)*q*w 1,-e;
     (n:ℤ)*w 0,(n:ℤ)*u 0,(n:ℤ)*w 1,(n:ℤ)*u 1,0]

def coeffMatrix (q : ℤ) (N I : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (K q) :=
  fun i j => ⟨(N i j : ℚ),(I i j : ℚ)⟩

def coeffWeights (q : ℤ) (u w : Fin 2 → ℤ) : Fin 2 → K q :=
  fun j => ⟨(u j : ℚ),(w j : ℚ)⟩

def quadVal (q : ℤ) : (Fin 2 → ℤ) →+ K q where
  toFun x := ⟨(x 0 : ℚ),(x 1 : ℚ)⟩
  map_zero' := by ext <;> rfl
  map_add' x y := by ext <;> simp [Pi.add_apply]

def quadRead (q : ℤ) : (Fin 5 → ℤ) →+ StagePair 2 (K q) where
  toFun x := (![⟨(x 0 : ℚ),(x 1 : ℚ)⟩,⟨(x 2 : ℚ),(x 3 : ℚ)⟩],⟨(x 4 : ℚ),0⟩)
  map_zero' := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_add' x y := by
    apply Prod.ext
    · funext i
      fin_cases i <;> apply QuadraticAlgebra.ext <;> simp [Pi.add_apply]
    · apply QuadraticAlgebra.ext <;> simp [Pi.add_apply]

theorem quadVal_inj (q : ℤ) : Function.Injective (quadVal q) := by
  intro x y h
  funext i
  fin_cases i
  · exact Int.cast_injective (congrArg QuadraticAlgebra.re h)
  · exact Int.cast_injective (congrArg QuadraticAlgebra.im h)

set_option maxHeartbeats 3000000 in
def quadModel (q : ℤ) (N I : Matrix (Fin 2) (Fin 2) ℤ)
    (u w : Fin 2 → ℤ) (d e : ℤ) :
    Model (κ := Fin 2) (quadMachine q N I d) (coeffMatrix q N I) (coeffWeights q u w) d e where
  read := quadRead q
  value := quadVal q
  value_injective := quadVal_inj q
  output := quadOutput q u w e
  map_leaf := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_mul v z := by
    apply Prod.ext
    · funext i
      fin_cases i <;> apply QuadraticAlgebra.ext <;>
        simp [quadRead,featureMul,quadMachine,quadTensor,Fin.sum_univ_succ]
    · apply QuadraticAlgebra.ext <;>
        simp [quadRead,featureMul,quadMachine,quadTensor,Fin.sum_univ_succ]
  map_branch k v := by
    apply Prod.ext
    · funext i
      fin_cases i <;> apply QuadraticAlgebra.ext <;>
        simp [quadRead,quadMachine,coeffMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
    · apply QuadraticAlgebra.ext <;>
        simp [quadRead,quadMachine,dotProduct,Fin.sum_univ_succ]
  map_output n v := by
    apply QuadraticAlgebra.ext <;>
      simp [quadRead,quadOutput,quadVal,coeffWeights,dotProduct,Fin.sum_univ_succ] <;> ring


namespace Gauss

def N : Matrix (Fin 2) (Fin 2) ℤ := !![3,3;3,3]
def I : Matrix (Fin 2) (Fin 2) ℤ := !![0,-2;2,0]
def u : Fin 2 → ℤ := ![6,6]
def w : Fin 2 → ℤ := ![0,0]
def X : Machine (Fin 5) := quadMachine 3 N I 12
def P : Model (κ := Fin 2) X (coeffMatrix 3 N I) (coeffWeights 3 u w) 12 12 :=
  quadModel 3 N I u w 12 12

def covData : Array (Cov (Fin 5)) := #[
  !![1,0,1,0,1;
      0,0,0,0,0;
      1,0,1,0,1;
      0,0,0,0,0;
      1,0,1,0,1],
  !![36,-12,36,12,72;
      -12,4,-12,-4,-24;
      36,-12,36,12,72;
      12,-4,12,4,24;
      72,-24,72,24,144],
  !![11520,-5760,11520,5760,34560;
      -5760,2880,-5760,-2880,-17280;
      11520,-5760,11520,5760,34560;
      5760,-2880,5760,2880,17280;
      34560,-17280,34560,17280,103680],
  !![11010816,-6220800,11010816,6220800,44043264;
      -6220800,3525120,-6220800,-3525120,-24883200;
      11010816,-6220800,11010816,6220800,44043264;
      6220800,-3525120,6220800,3525120,24883200;
      44043264,-24883200,44043264,24883200,176173056],
  !![21164654592,-12409749504,21164654592,12409749504,107137105920;
      -12409749504,7321632768,-12409749504,-7321632768,-62705664000;
      21164654592,-12409749504,21164654592,12409749504,107137105920;
      12409749504,-7321632768,12409749504,7321632768,62705664000;
      107137105920,-62705664000,107137105920,62705664000,543066882048]]
def C (n : ℕ) : Cov (Fin 5) := covData[n]!

theorem base : C 0 = outer X.leaf := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_checked (n : Fin 4) : C (n.val+1) = step X C n.val := by
  rw [step_eq_sparse]
  fin_cases n <;> decide +kernel

def trace : Trace X 5 where
  cov := C
  base := base
  next n hn := step_checked ⟨n, by omega⟩

theorem energies (n : Fin 5) :
    energy (trace.cov n.val) (P.output (n.val+1)) =
      (![0,0,0,0,116955021312] : Fin 5 → ℤ) n := by
  fin_cases n <;> decide +kernel

end Gauss

namespace Imaginary

def N : Matrix (Fin 2) (Fin 2) ℤ := !![0,0;20,0]
def I : Matrix (Fin 2) (Fin 2) ℤ := !![0,0;10,0]
def u : Fin 2 → ℤ := ![12,18]
def w : Fin 2 → ℤ := ![9,-9]
def X : Machine (Fin 5) := quadMachine (-1) N I 30
def P : Model (κ := Fin 2) X (coeffMatrix (-1) N I) (coeffWeights (-1) u w) 30 30 :=
  quadModel (-1) N I u w 30 30

def covData : Array (Cov (Fin 5)) := #[
  !![1,0,1,0,1;
      0,0,0,0,0;
      1,0,1,0,1;
      0,0,0,0,0;
      1,0,1,0,1],
  !![0,0,0,0,0;
      0,0,0,0,0;
      0,0,400,200,600;
      0,0,200,100,300;
      0,0,600,300,900],
  !![0,0,0,0,0;
      0,0,0,0,0;
      0,0,360000,480000,1080000;
      0,0,480000,640000,1440000;
      0,0,1080000,1440000,4050000]]
def C (n : ℕ) : Cov (Fin 5) := covData[n]!

theorem base : C 0 = outer X.leaf := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_checked (n : Fin 2) : C (n.val+1) = step X C n.val := by
  rw [step_eq_sparse]
  fin_cases n <;> decide +kernel

def trace : Trace X 3 where
  cov := C
  base := base
  next n hn := step_checked ⟨n, by omega⟩

theorem energies (n : Fin 3) :
    energy (trace.cov n.val) (P.output (n.val+1)) =
      (![0,0,1458000000] : Fin 3 → ℤ) n := by
  fin_cases n <;> decide +kernel

end Imaginary

theorem unitScale {q d : ℤ} (hd : d ≠ 0) : IsUnit (d : K q) := by
  have hq : IsUnit (d : ℚ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hd)
  simpa only [map_intCast] using hq.map (algebraMap ℚ (K q))

namespace Gauss

/-- Two-stage Gauss, in the two integer-independent coordinates of Q(√3). -/
def A : Matrix (Fin 2) (Fin 2) (K 3) :=
  !![⟨1/4,0⟩,⟨1/4,-1/6⟩; ⟨1/4,1/6⟩,⟨1/4,0⟩]
def b : Fin 2 → K 3 := ![⟨1/2,0⟩,⟨1/2,0⟩]

theorem scaleA : coeffMatrix 3 N I = ((12 : ℤ) : K 3) • A := by decide +kernel
theorem scaleB : coeffWeights 3 u w = ((12 : ℤ) : K 3) • b := by decide +kernel

private def trace4 : Trace X 4 where
  cov := C
  base := base
  next n hn := trace.next n (by omega)

theorem order_four : HasOrder 4 A b := by
  have hd := unitScale (q := 3) (d := 12) (by decide)
  apply (trace4.hasOrder_iff P scaleA scaleB hd hd).mpr
  intro n hn
  exact (by decide +kernel : ∀ i : Fin 4, energy (C i.val) (P.output (i.val+1)) = 0) ⟨n,hn⟩

theorem not_order_five : ¬ HasOrder 5 A b := by
  intro h
  have hd := unitScale (q := 3) (d := 12) (by decide)
  have hz := (trace.hasOrder_iff P scaleA scaleB hd hd).mp h 4 (by decide)
  have he : energy (trace.cov 4) (P.output 5) = 116955021312 := energies 4
  exact (by decide +kernel : (116955021312 : ℤ) ≠ 0) (he.symm.trans hz)

end Gauss

namespace Imaginary

/-- An explicit tableau over the coefficient algebra Q(i). -/
def A : Matrix (Fin 2) (Fin 2) (K (-1)) :=
  !![0,0; ⟨2/3,1/3⟩,0]
def b : Fin 2 → K (-1) := ![⟨2/5,3/10⟩,⟨3/5,-3/10⟩]

theorem scaleA : coeffMatrix (-1) N I = ((30 : ℤ) : K (-1)) • A := by decide +kernel
theorem scaleB : coeffWeights (-1) u w = ((30 : ℤ) : K (-1)) • b := by decide +kernel

private def trace2 : Trace X 2 where
  cov := C
  base := base
  next n hn := trace.next n (by omega)

theorem order_two : HasOrder 2 A b := by
  have hd := unitScale (q := -1) (d := 30) (by decide)
  apply (trace2.hasOrder_iff P scaleA scaleB hd hd).mpr
  intro n hn
  exact (by decide +kernel : ∀ i : Fin 2, energy (C i.val) (P.output (i.val+1)) = 0) ⟨n,hn⟩

theorem not_order_three : ¬ HasOrder 3 A b := by
  intro h
  have hd := unitScale (q := -1) (d := 30) (by decide)
  have hz := (trace.hasOrder_iff P scaleA scaleB hd hd).mp h 2 (by decide)
  have he : energy (trace.cov 2) (P.output 3) = 1458000000 := energies 2
  exact (by decide +kernel : (1458000000 : ℤ) ≠ 0) (he.symm.trans hz)

/-- A direct sum of squares of the two unnormalized errors would give
the wrong answer: the errors are nonzero, but their squares cancel in Q(i). -/
theorem field_squares_cancel :
    let r := b ⬝ᵥ Φ (tallTree 3) A - (⟨1/6,0⟩ : K (-1))
    let s := b ⬝ᵥ Φ (bushyTree 3) A - (⟨1/3,0⟩ : K (-1))
    r ≠ 0 ∧ s ≠ 0 ∧ r^2 + s^2 = 0 := by
  decide +kernel

end Imaginary

end RKResearch.Certified.CoordinateRootedTreeGram.Controls
