module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveGaussHole

open scoped BigOperators

/-- When the actual reverse read at the physical hole vanishes,
the actual cubic defect vanishes there. Its Gaussian mass is recovered
from the first signed defect moment alone. -/
theorem holeMassFromFirstMoment {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b h w p multiplier : ι → K) (r : ι) (d m : K)
    (hd : d ≠ 0) (hb : b r ≠ 0) (hp : p r ≠ 0)
    (hNodal : d*w r=0) (hReverse : b r*h r=multiplier r*w r)
    (hOther : ∀ i, i ≠ r → h i=p i)
    (hFirst : ∑ i, b i*h i=0) (hIntegral : ∑ i, b i*p i=m) :
    w r=0 ∧ h r=0 ∧ b r=m/p r := by
  have hw := (mul_eq_zero.mp hNodal).resolve_left hd
  have hz : h r=0 := by
    rw [hw,mul_zero] at hReverse
    exact (mul_eq_zero.mp hReverse).resolve_left hb
  have hpivot : (∑ i, (b i*p i-b i*h i))=b r*p r := by
    rw [Finset.sum_eq_single r]
    · simp [hz]
    · intro i _ hir
      rw [hOther i hir,sub_self]
    · simp
  rw [Finset.sum_sub_distrib,hIntegral,hFirst,sub_zero] at hpivot
  exact ⟨hw,hz,(eq_div_iff hp).2 hpivot.symm⟩

/-- Away from the shared root the deflated reverse nodal numerator is
constant; a physical Gauss hole is not counted as a silent stage. -/
theorem deflatedReverseNumerator {K : Type*} [Field K]
    (x r dFull dRest w τ : K) (hxr : x ≠ r)
    (hd : dFull=(x-r)*dRest) (hNodal : dFull*w=τ*(x-r)) :
    dRest*w=τ := by
  have h : (x-r)*(dRest*w-τ)=0 := by
    linear_combination hNodal-w*hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxr))

#print axioms holeMassFromFirstMoment
#print axioms deflatedReverseNumerator

end RKCert.ReviewedNative.SDIRK8EightActiveGaussHole
