module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticAffineTail

/-- Arithmetic eighth evaluates the already pinned affine tail gauge
without reconstructing either physically silent stage. -/
theorem arithmeticThirdAffineRead {R : Type*} [CommRing R]
    (a b x y d γ A B : R)
    (hx : a+b*x=γ*B) (hy : a+b*y=γ*A) (hd : d=2*y-x) :
    a+b*d=γ*(2*A-B) := by
  linear_combination 2*hy-hx+b*hd

/-- The cleared arithmetic eighth condition cancels only the genuine
nonzero diagonal, reverse factor and terminal profile numerator. -/
theorem normalizedArithmeticTail {K : Type*} [Field K]
    (H T γ k x c d z Lx Ld A B qx qd : K)
    (hne : γ*k*Lx ≠ 0)
    (hB : B=k*(c-z)*Lx)
    (hX : qx=γ*B) (hD : qd=γ*(2*A-B))
    (h : H*(x-z)*Ld*qx+k*T*(d-z)*Lx*qd=0) :
    H*(x-z)*Ld*(c-z)+T*(d-z)*(2*A-B)=0 := by
  have hr :
      (H*(x-z)*Ld*(c-z)+T*(d-z)*(2*A-B))*(γ*k*Lx)=0 := by
    linear_combination h-H*(x-z)*Ld*hX-k*T*(d-z)*Lx*hD-γ*H*(x-z)*Ld*hB
  exact (mul_eq_zero.mp hr).resolve_right hne

#print axioms arithmeticThirdAffineRead
#print axioms normalizedArithmeticTail

end RKCert.ReviewedNative.SDIRK8ArithmeticAffineTail
