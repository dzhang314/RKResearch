module

public import RKCert.ReviewedNative.ERK8FourOffPaidChartValues
public import Mathlib.Algebra.CharP.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Nonvanishing outside the finite set of exceptional primes
Each reduction is an integer polynomial identity after multiplying
by a power of the paid primes. There are no point-search assumptions. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff.PaidProof
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

variable {K : Type*} [Field K]

structure ExceptionalPrimeGuard (K : Type*) [Field K] : Prop where
  p11 : (11:K)≠0
  p17 : (17:K)≠0
  p37 : (37:K)≠0
  p41 : (41:K)≠0
  p43 : (43:K)≠0
  p79 : (79:K)≠0

theorem nonzero_of_affine_norm {u a b : K} (hq : 7*u^2-7*u+1=0)
    (ne : 7*a^2+7*a*b+b^2≠0) : a+b*u≠0 := by
  intro h
  apply ne
  linear_combination 7*(a+b*(1-u))*h+b^2*hq

theorem scaled_ne_of_rhs_ne {s f v : K} (eq : s*f=v) (ne : v≠0) : f≠0 := by
  intro e
  exact ne (by simpa [e] using eq.symm)

theorem generic_chart_tests [EightUnits K] {u : K}
    (hq : 7*u^2-7*u+1=0) (guards : ExceptionalPrimeGuard K) (o : CleanOrientation) :
    QuadraticChartTests o u := by
  cases o
  · refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · apply scaled_ne_of_rhs_ne (chartValue1p0 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(3:K)^2+7*(3:K)*(21:K)+(21:K)^2)=(3:K)^3*(5:K)*(7:K) by ring]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 (show (3:K)≠0 from paidCastNe 3 (by decide))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue1a hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(-5:K)^2+7*(-5:K)*(16:K)+(16:K)^2)=-((3:K)*(43:K)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero ((show (3:K)≠0 from paidCastNe 3 (by decide))) (guards.p43))
    · apply scaled_ne_of_rhs_ne (chartValue1b hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(52:K)^2+7*(52:K)*(-56:K)+(-56:K)^2)=(2:K)^4*(3:K)*(5:K)*(7:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue1d hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(7:K)^2+7*(7:K)*(-14:K)+(-14:K)^2)=-((3:K)*(7:K)^2) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero ((show (3:K)≠0 from paidCastNe 3 (by decide))) (pow_ne_zero 2 (show (7:K)≠0 from paidCastNe 7 (by decide))))
    · apply scaled_ne_of_rhs_ne (chartValue1p2 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(154:K)^2+7*(154:K)*(-56:K)+(-56:K)^2)=(2:K)^2*(3:K)*(5:K)*(7:K)^2*(37:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) (pow_ne_zero 2 (show (7:K)≠0 from paidCastNe 7 (by decide)))) (guards.p37)
    · apply scaled_ne_of_rhs_ne (chartValue1f4 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(576:K)^2+7*(576:K)*(-1224:K)+(-1224:K)^2)=-((2:K)^6*(3:K)^4*(5:K)*(43:K)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 4 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) (guards.p43))
    · apply scaled_ne_of_rhs_ne (chartValue1f5a hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(93960:K)^2+7*(93960:K)*(-77760:K)+(-77760:K)^2)=(2:K)^6*(3:K)^8*(5:K)^2*(37:K)*(43:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 8 (show (3:K)≠0 from paidCastNe 3 (by decide)))) (pow_ne_zero 2 (show (5:K)≠0 from paidCastNe 5 (by decide)))) (guards.p37)) (guards.p43)
    · apply scaled_ne_of_rhs_ne (chartValue1f5b hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(77760:K)^2+7*(77760:K)*(-81648:K)+(-81648:K)^2)=(2:K)^8*(3:K)^10*(7:K)*(43:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 8 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 10 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))) (guards.p43)
  · refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · apply scaled_ne_of_rhs_ne (chartValue2p0 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(15:K)^2+7*(15:K)*(-21:K)+(-21:K)^2)=-((3:K)^3*(7:K)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 (show (3:K)≠0 from paidCastNe 3 (by decide))) ((show (7:K)≠0 from paidCastNe 7 (by decide))))
    · apply scaled_ne_of_rhs_ne (chartValue2a hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(-7:K)^2+7*(-7:K)*(14:K)+(14:K)^2)=-((3:K)*(7:K)^2) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero ((show (3:K)≠0 from paidCastNe 3 (by decide))) (pow_ne_zero 2 (show (7:K)≠0 from paidCastNe 7 (by decide))))
    · apply scaled_ne_of_rhs_ne (chartValue2b hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(20:K)^2+7*(20:K)*(-28:K)+(-28:K)^2)=-((2:K)^4*(3:K)*(7:K)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide))))
    · apply scaled_ne_of_rhs_ne (chartValue2d hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(-13:K)^2+7*(-13:K)*(14:K)+(14:K)^2)=(3:K)*(5:K)*(7:K) by ring]
      exact mul_ne_zero (mul_ne_zero ((show (3:K)≠0 from paidCastNe 3 (by decide))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue2p2 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(182:K)^2+7*(182:K)*(-196:K)+(-196:K)^2)=(2:K)^2*(3:K)*(5:K)*(7:K)^3 by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) (pow_ne_zero 3 (show (7:K)≠0 from paidCastNe 7 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue2f4 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(1728:K)^2+7*(1728:K)*(-2016:K)+(-2016:K)^2)=(2:K)^10*(3:K)^4*(7:K) by ring]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 10 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 4 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue2f5a hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(-25272:K)^2+7*(-25272:K)*(30456:K)+(30456:K)^2)=(2:K)^6*(3:K)^8*(5:K)^2 by ring]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 6 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 8 (show (3:K)≠0 from paidCastNe 3 (by decide)))) (pow_ne_zero 2 (show (5:K)≠0 from paidCastNe 5 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue2f5b hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(46656:K)^2+7*(46656:K)*(-54432:K)+(-54432:K)^2)=(2:K)^10*(3:K)^10*(7:K) by ring]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 10 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 10 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))
  · refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · apply scaled_ne_of_rhs_ne (chartValue3p0 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(84:K)^2+7*(84:K)*(84:K)+(84:K)^2)=(2:K)^4*(3:K)^3*(5:K)*(7:K)^2 by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 3 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) (pow_ne_zero 2 (show (7:K)≠0 from paidCastNe 7 (by decide)))
    · apply scaled_ne_of_rhs_ne (chartValue3a hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(-44:K)^2+7*(-44:K)*(154:K)+(154:K)^2)=-((2:K)^2*(3:K)*(7:K)*(11:K)^2) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))) (pow_ne_zero 2 guards.p11))
    · apply scaled_ne_of_rhs_ne (chartValue3b hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(682:K)^2+7*(682:K)*(-770:K)+(-770:K)^2)=(2:K)^2*(3:K)*(7:K)*(11:K)^2*(17:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))) (pow_ne_zero 2 guards.p11)) (guards.p17)
    · apply scaled_ne_of_rhs_ne (chartValue3d hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(91:K)^2+7*(91:K)*(-140:K)+(-140:K)^2)=-((3:K)*(7:K)^2*(79:K)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ((show (3:K)≠0 from paidCastNe 3 (by decide))) (pow_ne_zero 2 (show (7:K)≠0 from paidCastNe 7 (by decide)))) (guards.p79))
    · apply scaled_ne_of_rhs_ne (chartValue3p2 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(2128:K)^2+7*(2128:K)*(-1568:K)+(-1568:K)^2)=(2:K)^8*(3:K)*(7:K)^3*(41:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 8 (show (2:K)≠0 from paidCastNe 2 (by decide))) ((show (3:K)≠0 from paidCastNe 3 (by decide)))) (pow_ne_zero 3 (show (7:K)≠0 from paidCastNe 7 (by decide)))) (guards.p41)
    · apply scaled_ne_of_rhs_ne (chartValue3f4 hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(42768:K)^2+7*(42768:K)*(-60984:K)+(-60984:K)^2)=-((2:K)^6*(3:K)^4*(5:K)*(7:K)*(11:K)^2*(79:K)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 4 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (5:K)≠0 from paidCastNe 5 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))) (pow_ne_zero 2 guards.p11)) (guards.p79))
    · apply scaled_ne_of_rhs_ne (chartValue3f5a hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(271605312:K)^2+7*(271605312:K)*(-311122944:K)+(-311122944:K)^2)=(2:K)^12*(3:K)^8*(11:K)^4*(17:K)*(41:K)*(79:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 8 (show (3:K)≠0 from paidCastNe 3 (by decide)))) (pow_ne_zero 4 guards.p11)) (guards.p17)) (guards.p41)) (guards.p79)
    · apply scaled_ne_of_rhs_ne (chartValue3f5b hq)
      apply nonzero_of_affine_norm hq
      rw [show ((7:K)*(5816448:K)^2+7*(5816448:K)*(-4790016:K)+(-4790016:K)^2)=(2:K)^14*(3:K)^10*(7:K)*(11:K)^2*(79:K) by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 14 (show (2:K)≠0 from paidCastNe 2 (by decide))) (pow_ne_zero 10 (show (3:K)≠0 from paidCastNe 3 (by decide)))) ((show (7:K)≠0 from paidCastNe 7 (by decide)))) (pow_ne_zero 2 guards.p11)) (guards.p79)

end RKResearch.Certified.Graded.FourOffNewton
