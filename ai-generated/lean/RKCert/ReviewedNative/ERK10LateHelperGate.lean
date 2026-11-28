module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Algebraic receipts for the ERK10 late-helper chart

A weightless donor can change the fourth reverse residual independently.
Before use of any Runge–Kutta order conditions, the cubic moment on the
four fixed weighted donors also reduces to smaller paid reads. These are
algebraic lemmas, not a sixteen-stage existence or exclusion theorem. -/

namespace RKResearch.Certified.ERK10LateHelperGate

open scoped BigOperators

variable {R : Type*} [CommRing R]

def dot {ι : Type*} [Fintype ι] (r v : ι → R) : R :=
  ∑ i, r i * v i

def fourClock (p q : R) : Fin 4 → R := ![0,1,p,q]

def moment (p q : R) (w : Fin 4 → R) (n : ℕ) : Fin 4 → R :=
  fun i => w i * fourClock p q i ^ n

def zeroClockDefect (u : R) : Fin 4 → R := ![0,u,0,0]

/-- The exceptional donor at reverse clock 1 has the sole second-read
defect. On the other three donors, a reduced cubic vanishes pointwise. -/
theorem four_donor_cubic (p q : R) (w : Fin 4 → R) (u : R)
    (h : 2*u + w 1 = 0) (i : Fin 4) :
    moment p q w 3 i = (p+q) * moment p q w 2 i - p*q * moment p q w 1 i
      - 2*(1-p)*(1-q) * zeroClockDefect u i := by
  fin_cases i
  · simp [moment,fourClock,zeroClockDefect]
  · simp [moment,fourClock,zeroClockDefect] at *
    linear_combination (1-p)*(1-q)*h
  · simp [moment,fourClock,zeroClockDefect]
    ring
  · simp [moment,fourClock,zeroClockDefect]
    ring

theorem four_donor_cubic_read (p q : R) (w r : Fin 4 → R) (u : R)
    (h : 2*u + w 1 = 0) :
    dot r (moment p q w 3) =
      (p+q) * dot r (moment p q w 2) - p*q * dot r (moment p q w 1)
        - 2*(1-p)*(1-q) * dot r (zeroClockDefect u) := by
  unfold dot
  calc
    (∑ i, r i * moment p q w 3 i) =
        ∑ i, ((p+q)*(r i * moment p q w 2 i) -
          p*q*(r i * moment p q w 1 i) -
            2*(1-p)*(1-q)*(r i * zeroClockDefect u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [four_donor_cubic p q w u h i]
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- A tap into an otherwise silent donor changes only the read that sees
that donor. This accounts for the later independent cofactor correction. -/
theorem helper_move {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r v : ι → R) (a : R) (j : ι) :
    dot (fun i => r i + if i = j then a else 0) v = dot r v + a*v j := by
  unfold dot
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ h
    simp [h]
  · simp

/-- The two nodal moment equations recover the sum and product of an
unlabelled pair without dividing, so the scalar gate is valid over any
commutative ring. -/
theorem pair_moments (m₀ m₁ m₂ m₃ s p : R)
    (h₀ : m₂ - s*m₁ + p*m₀ = 0) (h₁ : m₃ - s*m₂ + p*m₁ = 0) :
    (m₀*m₂-m₁^2)*s = m₀*m₃-m₁*m₂ ∧
    (m₀*m₂-m₁^2)*p = m₁*m₃-m₂^2 := by
  constructor
  · linear_combination m₁*h₀ - m₀*h₁
  · linear_combination m₂*h₀ - m₁*h₁

theorem pair_terminal_gate (m₀ m₁ m₂ m₃ s p C₀ C₁ C₂ : R)
    (h₀ : m₂ - s*m₁ + p*m₀ = 0) (h₁ : m₃ - s*m₂ + p*m₁ = 0)
    (ht : C₀+C₁*s+C₂*p = 0) :
    C₀*(m₀*m₂-m₁^2) + C₁*(m₀*m₃-m₁*m₂) + C₂*(m₁*m₃-m₂^2) = 0 := by
  obtain ⟨hs,hp⟩ := pair_moments m₀ m₁ m₂ m₃ s p h₀ h₁
  linear_combination (m₀*m₂-m₁^2)*ht - C₁*hs - C₂*hp

/-- An early zero-weight row shown only the origin, zero-clock donor and
one further weighted donor has this forced mixed scalar. -/
theorem after_one_weighted_relation (p t u w a G H : R)
    (hm : t*u + a*w*p = 0)
    (hg : G = t*u + a*w*p^2)
    (hh : 2*H + t*u = 0) : G + 2*(1-p)*H = 0 := by
  linear_combination hg + (1-p)*hh + p*hm

/-- In the one-dimensional cofactor compression, that early relation
contradicts the actual first nonzero weighted donor. -/
theorem no_early_helper (p w Va Vh g h : R)
    (hV : IsUnit Vh) (hw : w*p^3 ≠ 0)
    (hg : 6*g*Va = w*p^2*(3-2*p))
    (hh : 4*h*Va = -w*p^2)
    (he : (g+2*(1-p)*h)*Vh = 0) : False := by
  have he' : Vh*(g+2*(1-p)*h) = 0 := by rw [mul_comm,he]
  have hz := hV.mul_right_eq_zero.mp he'
  apply hw
  linear_combination 6*Va*hz - hg - 3*(1-p)*hh

end RKResearch.Certified.ERK10LateHelperGate

#print axioms RKResearch.Certified.ERK10LateHelperGate.four_donor_cubic_read
#print axioms RKResearch.Certified.ERK10LateHelperGate.helper_move
#print axioms RKResearch.Certified.ERK10LateHelperGate.pair_terminal_gate

#print axioms RKResearch.Certified.ERK10LateHelperGate.no_early_helper
