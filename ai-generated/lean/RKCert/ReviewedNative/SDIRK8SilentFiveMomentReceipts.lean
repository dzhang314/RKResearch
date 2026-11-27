module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SilentFiveMomentReceipts

open scoped BigOperators Matrix

/-- Isolate one of the three actual silent coordinates without requiring the
other two clocks to differ. Useful when one physical silent clock repeats
a front clock. -/
theorem threeSilentRead {K : Type*} [Field K]
    (a b z A B S : K) (hab : a ≠ b) (haz : a ≠ z)
    (h0 : A+B+S=0) (h1 : a*A+b*B+z*S=0)
    (h2 : a^2*A+b^2*B+z^2*S=0) : A=0 := by
  have f : A*(a-b)*(a-z)=0 := by
    linear_combination h2-(b+z)*h1+b*z*h0
  exact ((mul_eq_zero.mp f).resolve_right (sub_ne_zero.mpr haz) |> mul_eq_zero.mp).resolve_right
    (sub_ne_zero.mpr hab)

/-- Zero moments at n distinct active clocks and one optional silent clock
force every active coefficient away from the silent clock to vanish. The
silent clock may coincide with an active one, and no positivity is used. -/
theorem oneSilentClockSupport {K : Type*} [Field K] {n : ℕ}
    (c w : Fin n → K) (z wz : K) (hc : Function.Injective c)
    (hm : ∀ k ≤ n, (∑ i, w i * c i^k) + wz*z^k = 0) :
    ∀ i, c i ≠ z → w i=0 := by
  let V := (Matrix.vandermonde c)ᵀ
  let v := fun i => w i*(c i-z)
  have hu : IsUnit V.det := by
    change IsUnit ((Matrix.vandermonde c)ᵀ).det
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hc)
  have hx : V *ᵥ v = 0 := by
    ext k
    simp only [V, v, Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply,
      Matrix.vandermonde_apply, Pi.zero_apply]
    have e : (∑ i, c i^k.val * (w i*(c i-z))) =
        (∑ i, w i*c i^(k.val+1))-z*(∑ i,w i*c i^k.val) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      ext i
      rw [pow_succ]
      ring
    rw [e]
    have h₀ := hm k.val k.isLt.le
    have h₁ := hm (k.val+1) k.isLt
    rw [pow_succ] at h₁
    linear_combination h₁-z*h₀
  have hz : v = 0 := by
    calc
      v = (V⁻¹ * V) *ᵥ v := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  intro i hi
  exact (mul_eq_zero.mp (congrFun hz i)).resolve_right (sub_ne_zero.mpr hi)

/-- The reverse penultimate coordinate kills the actual quadratic factor.
A nonzero invisible coordinate then pins the common diagonal to the
physical terminal clock. -/
theorem silentHalf {K : Type*} [Field K]
    (γ x b₉ k wl nl : K) (hg : γ≠0) (hb : b₉≠0) (hw : wl≠0)
    (hx : x=1-γ) (h9 : -γ^2*b₉*k=0)
    (hl : (γ-x)*wl= -k*nl) : 2*γ=1 := by
  have k0 := (mul_eq_zero.mp h9).resolve_left
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hg)) hb)
  have x0 : γ-x=0 := (mul_eq_zero.mp (by simpa [k0] using hl)).resolve_right hw
  linear_combination x0+hx

#print axioms threeSilentRead
#print axioms oneSilentClockSupport
#print axioms silentHalf

end RKCert.ReviewedNative.SDIRK8SilentFiveMomentReceipts
