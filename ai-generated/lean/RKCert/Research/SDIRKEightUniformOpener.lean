module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Grade-zero departure and singular terminal scale at the SDIRK8 floor -/

namespace RKResearch.Certified.SDIRKEightUniformOpener

theorem departure_clock {K : Type*} [Field K] {x g h : K}
    (hd : g ≠ h) (ha : g-h=x*(g-h)) : x=1 := by
  have hb : (x-1)*(g-h)=0 := by linear_combination -ha
  exact sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right (sub_ne_zero.mpr hd))

theorem quartic_capacity {K : Type*} [Field K] {p : Polynomial K}
    (hp : p ≠ 0) (hd : p.natDegree ≤ 4) {f : Fin 5 → K}
    (hi : Function.Injective f) (he : ∀ i,p.eval (f i)=0) : False := by
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hi he
  rw [Fintype.card_fin]
  exact lt_of_le_of_lt hd (by decide)

theorem departure_by_fifth {K : Type*} [Field K] {p : Polynomial K}
    {x g : Fin 10 → K} {h : K}
    (hp : p ≠ 0) (hd : p.natDegree ≤ 4)
    (hi : Function.Injective (fun i => (x i,g i)))
    (he : ∀ i,g i=h → p.eval (x i)=0)
    (h₀ : g 0=h) (h₁ : g 1=h) (h₂ : g 2=h)
    (h₃ : g 3-h=x 3*(g 3-h))
    (h₄ : g 3=h → g 4-h=x 4*(g 4-h)) :
    (x 3=1 ∧ g 3≠h) ∨ (g 3=h ∧ x 4=1 ∧ g 4≠h) := by
  by_cases hz : g 3=h
  · have hy : g 4 ≠ h := by
      intro hlast
      let up : Fin 5 → Fin 10 := Fin.castLE (by decide)
      have hf : ∀ i,g (up i)=h := by
        intro i
        fin_cases i
        · exact h₀
        · exact h₁
        · exact h₂
        · exact hz
        · exact hlast
      refine quartic_capacity hp hd (f := x ∘ up) ?_ (fun i => he (up i) (hf i))
      intro i j hij
      have eqs : (x (up i),g (up i))=(x (up j),g (up j)) := by
        apply Prod.ext hij
        exact (hf i).trans (hf j).symm
      have hov := congrArg (fun k : Fin 10 => k.val) (hi eqs)
      exact Fin.ext hov
    exact Or.inr ⟨hz,departure_clock hy (h₄ hz),hy⟩
  · exact Or.inl ⟨departure_clock hz h₃,hz⟩

theorem singular_terminal_quadratic {R : Type*} [CommRing R]
    {H J h y s j₀ j₁ : R}
    (hT : y*H=s*H^2+J*(H-h)) (hJ : J=j₀+j₁*H) :
    (s+j₁)*H^2+(j₀-h*j₁-y)*H-h*j₀=0 := by
  linear_combination -hT-(H-h)*hJ

end RKResearch.Certified.SDIRKEightUniformOpener
