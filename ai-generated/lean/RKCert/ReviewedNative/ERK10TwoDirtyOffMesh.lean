module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKResearch.Certified.ERK10TwoDirtyOffMesh

variable {K : Type*} [Field K]

/-- Resolve one donor axis of a tilted pair after the paid mark. -/
theorem project_axis (a b k u v : K)
    (h : (a-k)*u + (b-k)*v = 0) :
    (b-a)*u = (b-k)*(u+v) := by
  linear_combination -h

/-- The paid mark and degree-five hull make the first dirty functional
miss precisely the other dirty site's mesh cardinal. The values Hp,Hq
are the degree-four cardinal (before multiplying by X−b). -/
theorem missing_cardinal (a b p q up uq vp vq Hp Hq : K) (hab : b ≠ a)
    (hp : (a-p)*up + (b-p)*vp = 0)
    (hq : (a-q)*uq + (b-q)*vq = 0)
    (hh : (up+vp)*(p-b)*Hp + (uq+vq)*(q-b)*Hq = 0) :
    up*Hp + uq*Hq = 0 := by
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hab)
  show (b-a)*(up*Hp+uq*Hq) = 0
  linear_combination -hh - Hp*hp - Hq*hq

/-- Rearrange one literal early-null pressure read by separating the
two dirty actual values from the clean model values. -/
theorem xp_pressure (w a x y H K0 r : K)
    (h : w - x*H + y*(a*K0-r) = 0) :
    w = x*H + y*r - y*a*K0 := by
  linear_combination h

end RKResearch.Certified.ERK10TwoDirtyOffMesh
