module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The order-eight singleton-zero scalar gate

The native theorem starts with a genuinely supported grade-three packet and
a paid grade-four clean read at its support. The sibling saturation
module establishes those premises for a ten-stage nonsingular DIRK tableau with
exactly one zero of the quadratic stage residual. No ordering or root
existence is used by this module.
-/

namespace RKResearch.Certified.Graded.OrderEightSingletonZero

open FiniteRootedTree Module
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The monic shifted fourth Legendre polynomial, evaluated at its argument. -/
def legendreFour (a : K) : K :=
  a^4 - 2*a^3 + (9/7)*a^2 - (2/7)*a + 1/70

def cardinalCoeffs (a : K) : Fin 4 → K :=
  ![a^3-2*a^2+(9/7)*a-2/7, a^2-2*a+9/7, a-2, 1]

def evaluate (r : Fin 4 → K) (x : K) : K :=
  ∑ j : Fin 4, r j * x^j.val

def primitive (r : Fin 4 → K) (x : K) : K :=
  ∑ j : Fin 4, (r j / (((j.val+1 : ℕ)) : K)) * x^(j.val+1)

/-- Half the Gauss cardinal mass at the supported clock. -/
def halfMass (a : K) : K := (4+35*a*(1-a))/72

/-- Four ordinary moments isolate the exact cubic scalar profile. These
integer row operations are the inverse of the 4-by-4 rational Hilbert
matrix, applied to the coefficients of (X - a) r(X). -/
theorem scalar_shape (a : K) (r : Fin 4 → K)
    (h : ∀ k : Fin 4,
      (∑ j : Fin 4, r j / (((k.val+j.val+2 : ℕ)) : K)) -
        a*(∑ j : Fin 4, r j / (((k.val+j.val+1 : ℕ)) : K)) = 0) :
    (∀ j, r j = r 3 * cardinalCoeffs a j) ∧ r 3 * legendreFour a = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3
  have e0 : -a*r 0 - r 3/70 = 0 := by
    linear_combination 16*h0 - 120*h1 + 240*h2 - 140*h3
  have e1 : r 0 - a*r 1 + (2/7)*r 3 = 0 := by
    linear_combination -120*h0 + 1200*h1 - 2700*h2 + 1680*h3
  have e2 : r 1 - a*r 2 - (9/7)*r 3 = 0 := by
    linear_combination 240*h0 - 2700*h1 + 6480*h2 - 4200*h3
  have e3 : r 2 - a*r 3 + 2*r 3 = 0 := by
    linear_combination -140*h0 + 1680*h1 - 4200*h2 + 2800*h3
  constructor
  · intro j
    fin_cases j <;> norm_num [cardinalCoeffs]
    · linear_combination e1 + a*e2 + a^2*e3
    · linear_combination e2 + a*e3
    · linear_combination e3
  · unfold legendreFour
    linear_combination -e0 - a*e1 - a^2*e2 - a^3*e3

theorem primitive_halfMass_of_shape {a : K} {r : Fin 4 → K}
    (ha : legendreFour a = 0) (hr : ∀ j, r j = r 3 * cardinalCoeffs a j) :
    primitive r a = halfMass a * evaluate r a ∧ primitive r 1 = 2 * primitive r a := by
  have sa : primitive r a = r 3 * primitive (cardinalCoeffs a) a := by
    unfold primitive
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hr j]
    ring
  have sb : primitive r 1 = r 3 * primitive (cardinalCoeffs a) 1 := by
    unfold primitive
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hr j]
    ring
  have se : evaluate r a = r 3 * evaluate (cardinalCoeffs a) a := by
    unfold evaluate
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hr j]
    ring
  have pp : primitive (cardinalCoeffs a) a =
      halfMass a * evaluate (cardinalCoeffs a) a := by
    norm_num [primitive,evaluate,halfMass,cardinalCoeffs,Fin.sum_univ_succ]
    unfold legendreFour at ha
    linear_combination (35*a/18 + 10/9)*ha
  have pd : primitive (cardinalCoeffs a) 1 = 2 * primitive (cardinalCoeffs a) a := by
    norm_num [primitive,cardinalCoeffs,Fin.sum_univ_succ]
    unfold legendreFour at ha
    linear_combination -(25/6)*ha
  constructor
  · rw [sa,se,pp]
    ring
  · rw [sb,sa,pd]
    ring

theorem halfMass_quadratic {a : K} (ha : legendreFour a = 0) :
    (144 * halfMass a - 18)^2 = 30 := by
  unfold halfMass
  unfold legendreFour at ha
  linear_combination 4900*ha

section ActualTableau

variable {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

omit [CharZero K] in
private theorem coeffEval_at (r : Fin 4 → K) (i : Fin s) :
    coeffEval A 3 r i = evaluate r (nodes A i) := by
  simp only [coeffEval_apply,evaluate,normTree_clockTree,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul]

private theorem primitive_mod_defect (r : Fin 4 → K) :
    mat A (coeffEval A 3 r) - (fun i => primitive r (nodes A i)) ∈
      zeroSpace A 4 := by
  have col (j : Fin 4) : (fun i : Fin s => (r j / (((j.val+1 : ℕ)) : K)) *
      ((j.val+1 : ℕ) * mat A (fun l => (nodes A l)^j.val) i - (nodes A i)^(j.val+1)))
      ∈ zeroSpace A 4 := by
    have hj : j.val+1 ≤ 4 := j.isLt
    have h := zeroSpace_mono A hj (monomialStageDefect_mem A j.val)
    exact (zeroSpace A 4).smul_mem (r j / (((j.val+1 : ℕ)) : K)) h
  have e : mat A (coeffEval A 3 r) - (fun i => primitive r (nodes A i)) =
      ∑ j : Fin 4, (fun i : Fin s => (r j / (((j.val+1 : ℕ)) : K)) *
        ((j.val+1 : ℕ) * mat A (fun l => (nodes A l)^j.val) i -
          (nodes A i)^(j.val+1))) := by
    ext i
    simp only [coeffEval_apply,normTree_clockTree,map_sum,map_smul,Finset.sum_apply,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,primitive,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hn : (((j.val+1 : ℕ)) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn]
  rw [e]
  exact (zeroSpace A 4).sum_mem (fun j _ => col j)

omit [CharZero K] in
private theorem probe_supported (i : Fin s) (v : Fin s → K)
    (hv : ∀ j, j ≠ i → v j = 0) (k : ℕ) :
    probe A b k v = b i * (nodes A i)^k * v i := by
  change ∑ j, (b j * (nodes A j)^k) * v j = _
  rw [Finset.sum_eq_single i]
  · intro j _ h
    rw [hv j h,mul_zero]
  · simp

omit [CharZero K] in
private theorem packet_probe (ho : HasOrder 8 A b)
    (i : Fin s) (r : Fin 4 → K) (d : Fin s → K) (hd : d ∈ zeroSpace A 3)
    (support : ∀ j, j ≠ i → (coeffEval A 3 r + d) j = 0)
    (k : ℕ) (hk : k ≤ 4) :
    (∑ j : Fin 4, r j / (((k+j.val+1 : ℕ)) : K)) =
       b i * (nodes A i)^k * (coeffEval A 3 r+d) i := by
  let v := coeffEval A 3 r+d
  have h := probe_supported (A:=A) (b:=b) i v support k
  change probe A b k (coeffEval A 3 r+d) = _ at h
  rw [map_add,show probe A b k d = 0 from probe_zeroSpace ho (by omega) hd,
    add_zero,probe_coeffEval ho (by omega)] at h
  exact h

/-- The exact zero-support trace test, using actual rooted-tree probes. -/
theorem shape_of_supported_packet (ho : HasOrder 8 A b)
    (i : Fin s) (r : Fin 4 → K) (d : Fin s → K) (hd : d ∈ zeroSpace A 3)
    (support : ∀ j, j ≠ i → (coeffEval A 3 r + d) j = 0) :
    (∀ j, r j = r 3 * cardinalCoeffs (nodes A i) j) ∧
    r 3 * legendreFour (nodes A i) = 0 := by
  let a := nodes A i
  apply scalar_shape a r
  intro k
  have hk := k.isLt
  have h0 := packet_probe ho i r d hd support k.val (by omega)
  have h1 := packet_probe ho i r d hd support (k.val+1) (by omega)
  have idx : (∑ j : Fin 4, r j / (((k.val+j.val+2 : ℕ)) : K)) =
    (∑ j : Fin 4, r j / (((k.val+1+j.val+1 : ℕ)) : K)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show k.val+j.val+2 = k.val+1+j.val+1 by omega]
  rw [idx,h0,h1,pow_succ]
  ring

/-- A supported actual stage packet of grade three, with clean read at
its unique support through grade four, forces the literal diagonal and
output coefficient. The sibling saturation module derives both premises
by the sharp parity dimension census; they are explicit here. -/
theorem stage_pin_from_supported_packet (ho : HasOrder 8 A b)
    (i : Fin s) (r : Fin 4 → K) (d : Fin s → K)
    (hd : d ∈ zeroSpace A 3)
    (clean : ∀ v ∈ zeroSpace A 4, v i = 0)
    (support : ∀ j, j ≠ i → (coeffEval A 3 r + d) j = 0)
    (nonzero : (coeffEval A 3 r+d) i ≠ 0) :
    legendreFour (nodes A i) = 0 ∧
    A i i = halfMass (nodes A i) ∧
    b i = 2 * A i i ∧
    (144 * A i i - 18)^2 = 30 := by
  let a := nodes A i
  let v := coeffEval A 3 r+d
  have hr := shape_of_supported_packet ho i r d hd support
  have read : v i = evaluate r a := by
    change coeffEval A 3 r i + d i = _
    rw [coeffEval_at, clean d (zeroSpace_mono A (by decide : 3≤4) hd), add_zero]
  have rn : r 3 ≠ 0 := by
    intro z
    have zr : r=0 := by ext j; rw [hr.1 j,z,zero_mul]; rfl
    apply nonzero
    change v i = 0
    rw [read,zr]
    simp [evaluate]
  have ha : legendreFour a = 0 := (mul_eq_zero.mp hr.2).resolve_left rn
  have hprim := primitive_halfMass_of_shape ha hr.1
  have def4 : mat A (coeffEval A 3 r) - (fun j => primitive r (nodes A j)) ∈
      zeroSpace A 4 := primitive_mod_defect r
  have readA : mat A v i = primitive r a := by
    have hm := clean (mat A d) (mat_zeroSpace_charZero A 3 hd)
    have hs := clean _ def4
    change mat A (coeffEval A 3 r) i - primitive r a = 0 at hs
    change mat A (coeffEval A 3 r+d) i = _
    rw [map_add]
    change mat A (coeffEval A 3 r) i + mat A d i = _
    rw [hm,add_zero,sub_eq_zero.mp hs]
  have diag : A i i * v i = primitive r a := by
    rw [←readA]
    change _ = ∑ j, A i j * v j
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [show v j = 0 from support j hj,mul_zero]
    · simp
  have diagEq : A i i = halfMass a := by
    apply mul_right_cancel₀ nonzero
    change A i i * v i = halfMass a * v i
    rw [diag,hprim.1,read]
  have out : b i * v i = primitive r 1 := by
    have h := packet_probe ho i r d hd support 0 (by decide)
    simp only [pow_zero,mul_one,Nat.zero_add] at h
    simpa only [primitive,pow_one,one_pow,mul_one] using h.symm
  have hb : b i = 2*A i i := by
    apply mul_right_cancel₀ nonzero
    change b i * v i = (2*A i i)*v i
    rw [out,hprim.2,←diag,mul_assoc]
  refine ⟨ha,diagEq,hb,?_⟩
  rw [diagEq]
  exact halfMass_quadratic ha

end ActualTableau

end RKResearch.Certified.Graded.OrderEightSingletonZero
