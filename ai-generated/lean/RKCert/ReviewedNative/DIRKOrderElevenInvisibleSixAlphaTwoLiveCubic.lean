import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Undivided scalar receipts for the alpha-two live cubic clock chart.
These do not independently formalize the rooted tableau ingress or the exact
arithmetic rank certificates. -/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoLiveCubic

variable {K : Type*} [CommRing K]

def wedge (a b : K × K) : K := a.1*b.2-a.2*b.1

/-- Relative powers of the live quadratic leader in a quintic determinant.
Here q,m stand for the two cleared degree-two remainders and r for the
degree-three remainder cleared by an additional leader factor. -/
theorem homogeneous_quintic
    (q m r : K × K) (w j p ell t : K) :
    wedge (w*j*q.1+(p+t*ell)*r.1, w*j*q.2+(p+t*ell)*r.2)
        (w*m.1+t*r.1, w*m.2+t*r.2) =
      w*(j*w*wedge q m+(p+t*ell)*wedge r m+t*j*wedge q r) := by
  unfold wedge
  ring

/-- Eliminate the carrier parameter without assuming the quartic coefficient
or the coefficient from the quintic is nonzero. -/
theorem eliminate_parameter
    {qv lv j w a b c pv mv t : K}
    (quartic : qv+t*lv=0)
    (quintic : j*w*a+(pv+t*mv)*c+t*j*b=0) :
    lv*(j*w*a+pv*c)-qv*(j*b+mv*c)=0 := by
  linear_combination lv*quintic-(j*b+mv*c)*quartic

theorem cleared_carrier {qv lv t : K} (h : qv+t*lv=0) (m r : K) :
    lv*m-qv*r=lv*(m+t*r) := by
  linear_combination -r*h

theorem cleared_cubic_leader [IsDomain K] {qv lv t : K}
    (h : qv+t*lv=0) (hl : lv≠0) (ht : t≠0) : -qv≠0 := by
  intro hn
  have hz : qv=0 := neg_eq_zero.mp hn
  have hp : t*lv=0 := by simpa [hz] using h
  exact mul_ne_zero ht hl hp

/-- A zero quartic coefficient is a contact with one of the two distinct
early ghost roots, not a lost carrier pivot. -/
theorem exceptional_contact [IsDomain K] {l j u w wlead v z1 z2 : K}
    (hl : l=0) (hj : j≠0) (hw : wlead≠0)
    (hq : l*u=j*w) (hf : w=wlead*((v-z1)*(v-z2))) :
    v=z1 ∨ v=z2 := by
  have he : j*w=0 := by simpa [hl] using hq.symm
  have hs : w=0 := (mul_eq_zero.mp he).resolve_left hj
  have hp : (v-z1)*(v-z2)=0 := by
    rw [hf] at hs
    exact (mul_eq_zero.mp hs).resolve_left hw
  rcases mul_eq_zero.mp hp with h|h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem contact_sample (prim g q h theta : K)
    (hq : q=0) (h1 : prim=g*q+theta*h) : prim=theta*h := by
  simpa [hq] using h1

def affineNumerator (a b ha hb fa fb x : K) : K :=
  fa*hb*(x-b)-fb*ha*(x-a)

theorem affine_numerator_at_a (a b ha hb fa fb : K) :
    ha*affineNumerator a b ha hb fa fb a =
      ha*hb*(a-b)*fa := by
  unfold affineNumerator
  ring

theorem affine_numerator_at_b (a b ha hb fa fb : K) :
    hb*affineNumerator a b ha hb fa fb b =
      ha*hb*(a-b)*fb := by
  unfold affineNumerator
  ring

def det3 (u v w : K × K × K) : K :=
  u.1*(v.2.1*w.2.2-v.2.2*w.2.1)-u.2.1*(v.1*w.2.2-v.2.2*w.1)+
  u.2.2*(v.1*w.2.1-v.2.1*w.1)

/-- Finite coefficient reduction for the affine quotient test. This is valid
also when either affine coefficient, or either generating column, vanishes. -/
theorem affine_rem_determinant (u v w : K × K × K) (a b : K)
    (h0 : w.1=a*u.1+b*v.1)
    (h1 : w.2.1=a*u.2.1+b*v.2.1)
    (h2 : w.2.2=a*u.2.2+b*v.2.2) :
    det3 u v w=0 := by
  unfold det3
  rw [h0,h1,h2]
  ring

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoLiveCubic
