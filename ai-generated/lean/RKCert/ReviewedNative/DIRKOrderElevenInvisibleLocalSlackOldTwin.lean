import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackOldTwin

/-- Exact matched quartic across the first distinct ordinary pivot.
This determinant safety test uses no division by either weighted head
or the pivot diagonal. -/
theorem fourth_repeat_hinge {R : Type*} [CommRing R]
    {d z V P P0 w k S I0 IV q : R}
    (hm : (V-z)*(k-P)=q*P0)
    (hw : I0-k*w=d*P0)
    (hn : k*(S+q*w)=IV+q*I0) :
    (I0-d*P0)*(S-(V-z)*d)-w*(IV-(V-z)*P*d)=0 := by
  have hh : k*(S-(V-z)*d)=IV-(V-z)*P*d := by
    linear_combination hn + q*hw - d*hm
  linear_combination w*hh + (S-(V-z)*d)*hw

/-- A mark which coincides with an old ordinary receiver separates
the barycentric companion coefficient without dividing by that
receiver's cubic. -/
theorem same_clock_zero_companion {K : Type*} [Field K]
    {Gs Gw Hw Q theta : K} (hs : Gs≠0) (hh : Hw≠0)
    (a : Gs*Q=0) (b : Gw*Q+theta*Hw=0) :
    Q=0 ∧ theta=0 := by
  have hq := (mul_eq_zero.mp a).resolve_left hs
  have ht : theta*Hw=0 := by simpa [hq] using b
  exact ⟨hq,(mul_eq_zero.mp ht).resolve_right hh⟩

/-- The undivided fifth gate after the zero diagonal branch. -/
theorem fifth_quintic_pair {R : Type*} [CommRing R]
    {k u v L J : R} (h1 : k*v=u) (h2 : k*L=J) :
    u*L-v*J=0 := by
  rw [← h1, ← h2]
  ring

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackOldTwin

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackOldTwin
#print axioms fourth_repeat_hinge
#print axioms same_clock_zero_companion
#print axioms fifth_quintic_pair
