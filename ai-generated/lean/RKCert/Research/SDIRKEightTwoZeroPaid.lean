module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The two actual F997 row-five rejection receipts -/

namespace RKResearch.Certified.SDIRKEightTwoZeroPaid

open scoped BigOperators Matrix

abbrev K := ZMod 997

def xA : Fin 5 → K := ![591,470,349,562,89]
def gA : Fin 5 → K := ![664,97,603,835,0]
def coefA : Fin 6 → K := ![492,746,665,771,659,0]
def rowA : Fin 5 → K := ![0,0,0,0,1]

def xB : Fin 5 → K := ![591,470,349,562,922]
def gB : Fin 5 → K := ![664,97,603,835,672]
def coefB : Fin 6 → K := ![83,981,98,355,328,0]
def rowB : Fin 5 → K := ![739,0,2,505,1]

def trace (u : Fin 6 → K) (x g : K) : K :=
  u 0+u 1*x+u 2*x^2+u 3*x^3+u 4*g+u 5*x*g

def primitive (u : Fin 6 → K) (x : K) : K :=
  u 0*x+499*u 1*x^2+665*u 2*x^3+748*u 3*x^4

def four (x g : Fin 5 → K) (j : Fin 4) (i : Fin 5) : K :=
  g i * (![1,x i,(x i)^2,g i] : Fin 4 → K) j

def rhs (u : Fin 6 → K) (x : Fin 5 → K) (i : Fin 5) : K :=
  (if i=4 then 591 else 0)-primitive u (x i)

def dot {R : Type*} [CommSemiring R] (l y : Fin 5 → R) : R := ∑ i,l i*y i

theorem reject {R : Type*} [CommSemiring R]
    {l t : Fin 5 → R} {B : Fin 4 → Fin 5 → R}
    (hn : dot l t ≠ 0) (hB : ∀ j,dot l (B j)=0)
    (q : Fin 4 → R) (hq : ∀ i,t i=∑ j,q j*B j i) : False := by
  apply hn
  calc
    dot l t = ∑ i,∑ j,q j*(l i*B j i) := by
      unfold dot
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hq, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      ac_rfl
    _ = ∑ j,q j*dot l (B j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [dot,Finset.mul_sum]
    _ = 0 := by simp [hB]

theorem representative_A :
    ∀ i : Fin 5, trace coefA (xA i) (gA i)=(if i=4 then 1 else 0) := by decide +kernel

theorem representative_B :
    ∀ i : Fin 5, trace coefB (xB i) (gB i)=(if i=4 then 1 else 0) := by decide +kernel

theorem row_A :
    (∀ j : Fin 4,dot rowA (four xA gA j)=0) ∧ dot rowA (rhs coefA xA)=166 := by
  decide +kernel

theorem row_B :
    (∀ j : Fin 4,dot rowB (four xB gB j)=0) ∧ dot rowB (rhs coefB xB)=650 := by
  decide +kernel

theorem no_prefix_A (q : Fin 4 → K) :
    ¬ (∀ i,rhs coefA xA i = ∑ j,q j*four xA gA j i) := by
  exact reject (by rw [row_A.2]; decide +kernel) row_A.1 q

theorem no_prefix_B (q : Fin 4 → K) :
    ¬ (∀ i,rhs coefB xB i = ∑ j,q j*four xB gB j i) := by
  exact reject (by rw [row_B.2]; decide +kernel) row_B.1 q

theorem moment_mass_guard {R : Type*} [CommRing R]
    {M₀ M₁ M₂ M₃ a₀ a₁ a₂ a₃ : R} (h₀ : a₀*M₀ ≠ 0)
    (h₁ : M₁=0) (h₂ : M₂=0) (h₃ : M₃=0) :
    a₀*M₀+a₁*M₁+a₂*M₂+a₃*M₃ ≠ 0 := by
  simpa [h₁,h₂,h₃] using h₀

end RKResearch.Certified.SDIRKEightTwoZeroPaid
