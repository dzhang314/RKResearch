module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8RepeatedClockScalarReceipts

/-- The two scalar equations determining the unpegged quadratic factor
in the six-clock branch, before division by the Hankel determinant. -/
theorem twoNodalCoefficients {R : Type*} [CommRing R] (m0 m1 m2 m3 u v : R)
    (h0 : m2+u*m1+v*m0=0) (h1 : m3+u*m2+v*m1=0) :
    (m0*m2-m1^2)*u=m1*m2-m0*m3 ∧
      (m0*m2-m1^2)*v=m1*m3-m2^2 := by
  constructor
  · linear_combination m0*h1-m1*h0
  · linear_combination m2*h0-m1*h1

/-- A quadratic norm certifies nonvanishing at *either* actual clock root,
including when a specialization gives a repeated root. -/
theorem quadraticRootRead {R : Type*} [CommRing R] (a b u v x : R)
    (h : x^2+a*x+b=0) (hh : u^2-a*u*v+b*v^2≠0) :
    u+v*x≠0 := by
  intro hz
  apply hh
  calc
    u^2-a*u*v+b*v^2 = (u+v*x)*(u-a*v-v*x)+v^2*(x^2+a*x+b) := by ring
    _ = 0 := by rw [hz,h]; ring

end RKCert.ReviewedNative.SDIRK8RepeatedClockScalarReceipts
