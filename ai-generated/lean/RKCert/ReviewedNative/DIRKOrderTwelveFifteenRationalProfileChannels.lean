module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Algebraic leaf lemmas for the three exact paid cubic channels. -/

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.RationalProfileChannels

variable {K : Type*} [Field K]

/-- Normalization at a shared derivative root does not invert the
possibly zero leading denominator factor V. -/
theorem normalizeAtShared {u v m1 m2 m3 : K} (hu : u ≠ 0)
    (h12 : u*m1 = v*m2) (h23 : u*m2 = v*m3) :
    ∃ n : K, m1 = n*v^2 ∧ m2 = n*(u*v) ∧ m3 = n*u^2 := by
  have d : u^2 ≠ 0 := pow_ne_zero _ hu
  have e1 : m1*u^2 = m3*v^2 := by
    linear_combination u*h12 + v*h23
  have e2 : m2*u^2 = m3*(u*v) := by
    linear_combination u*h23
  refine ⟨m3/u^2, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    exact (eq_div_iff d).mpr e1
  · rw [div_mul_eq_mul_div]
    exact (eq_div_iff d).mpr e2
  · exact (div_mul_cancel₀ _ d).symm

/-- If the remaining denominator factor also vanishes, only the third
channel can carry any signal at that shared root. -/
theorem repeatedRootChannels {u m1 m2 m3 : K} (hu : u ≠ 0)
    (h12 : u*m1 = (0:K)*m2) (h23 : u*m2 = (0:K)*m3) :
    m1 = 0 ∧ m2 = 0 := by
  obtain ⟨n,h1,h2,_⟩ := normalizeAtShared hu h12 h23
  simp [h1,h2]

/-- The two exact Vandermonde conditions for at most two shared sites. -/
theorem separateTwoFibers {a b s t : K} (ab : a ≠ b)
    (h0 : s+t = 0) (h1 : a*s+b*t = 0) : s=0 ∧ t=0 := by
  have nz : b-a ≠ 0 := sub_ne_zero.mpr ab.symm
  have z : (b-a)*t=0 := by linear_combination h1 - a*h0
  have tz : t=0 := (mul_eq_zero.mp z).resolve_left nz
  simpa [tz] using h0

/-- Two live nonzero amplitudes with both paid correction moments zero
have one common amplitude and zero aggregate correction. -/
theorem twoNonzeroCorrections {h1 h2 d1 d2 : K} (hh1 : h1 ≠ 0)
    (hh2 : h2 ≠ 0) (hd2 : d2 ≠ 0)
    (p1 : d1*h1 + d2*h2 = 0) (p2 : d1*h1^2 + d2*h2^2 = 0) :
    h1=h2 ∧ d1+d2=0 := by
  have z : (d2*h2)*(h2-h1) = 0 := by
    linear_combination p2-h1*p1
  have e : h2=h1 := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (mul_ne_zero hd2 hh2))
  refine ⟨e.symm, ?_⟩
  have z' : (d1+d2)*h1=0 := by
    rw [add_mul]
    simpa only [e] using p1
  exact (mul_eq_zero.mp z').resolve_right hh1

#print axioms normalizeAtShared
#print axioms repeatedRootChannels
#print axioms separateTwoFibers
#print axioms twoNonzeroCorrections

end RKResearch.Certified.Graded.OrderTwelveFifteen.RationalProfileChannels
