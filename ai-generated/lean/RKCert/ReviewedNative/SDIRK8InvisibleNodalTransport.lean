module

public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8InvisibleNodalTransport

open Polynomial

/-- Pointwise denominator-free transport. A shared root of p and q,
including a physically used root, is not removed from the identity. -/
theorem scalarTransport {R : Type*} [CommRing R]
    (c g p q b h d w r t : R)
    (hp : p=q*h) (hr : b*h=r*(c-g)*w) (ht : d*w=t*q) :
    p*(b*d)=r*t*(c-g)*q^2 := by
  calc
    p*(b*d) = q*d*(b*h) := by rw [hp]; ring
    _ = r*(c-g)*q*(d*w) := by rw [hr]; ring
    _ = r*t*(c-g)*q^2 := by rw [ht]; ring

/-- Low-degree nodal identity from all distinct actual clock reads.
The caller supplies the degree bound for the Cauchy-transform residual. -/
theorem nodalTransport {K ι : Type*} [Field K] [Fintype ι]
    (c b h w d : ι → K) (g r t : K) (p q W E D : K[X])
    (hc : Function.Injective c) (hD : ∀ i, D.eval (c i)=0)
    (hW : ∀ i, W.eval (c i)=b i*d i)
    (hp : ∀ i, p.eval (c i)=q.eval (c i)*h i)
    (hr : ∀ i, b i*h i=r*(c i-g)*w i)
    (ht : ∀ i, d i*w i=t*q.eval (c i))
    (hdeg : max (p*W-E*D).natDegree
      (C (r*t)*(X-C g)*q^2).natDegree < Fintype.card ι) :
    p*W-E*D=C (r*t)*(X-C g)*q^2 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hc _ hdeg
  intro i
  simp only [eval_sub,eval_mul,eval_C,eval_X,eval_pow,hD,hW,mul_zero,sub_zero]
  exact scalarTransport _ _ _ _ _ _ _ _ _ _ (hp i) (hr i) (ht i)

#print axioms scalarTransport
#print axioms nodalTransport

end RKCert.ReviewedNative.SDIRK8InvisibleNodalTransport
