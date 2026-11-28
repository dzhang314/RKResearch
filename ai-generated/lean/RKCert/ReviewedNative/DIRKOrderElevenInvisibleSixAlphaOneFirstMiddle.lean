import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneFirstMiddle

variable {K : Type*} [CommRing K]

/-- The divided first-middle gate. Neither the marked tap nor the quartic
signal at the middle ghost is cancelled. -/
theorem divided_first_middle [IsDomain K]
    {x z v dx dv tap r k p p1 p0 ell rho1 rho kapa
      w F rStar kStar Q qStar : K}
    (hxz : x≠z) (he : ell=dx+tap+r*(k-p))
    (hm : rho1=x*dx+z*tap+r*(v*k-p1))
    (hp : p1=v*p-kapa*p0)
    (hfit : rho1=x*ell-rho-kapa*w)
    (hR : p0*r= -w)
    (hK : p0*kStar=(v-z)*(k-p))
    (hw : w=(x-z)*F) (hρ : rho=(x-z)*rStar)
    (hC : (x-v-dv-dx)*w+Q=0) (hQ : Q=(x-z)*qStar) :
    F*(x-v-dv-ell+rStar-F*kStar)+qStar=0 := by
  have hraw : (x-z)*dx+r*((v-z)*(k-p)+kapa*p0)=rho1-z*ell := by
    rw [hm,he,hp]
    ring
  have hr : r*((v-z)*(k-p)+kapa*p0)= -w*(kStar+kapa) := by
    rw [← hK]
    calc
      r*(p0*kStar+kapa*p0)=(p0*r)*(kStar+kapa) := by ring
      _ = -w*(kStar+kapa) := by rw [hR]
  have hh : (x-z)*(dx-ell+rStar-F*kStar)=0 := by
    rw [hr,hfit,hρ,hw] at hraw
    linear_combination hraw
  have hq : (x-z)*(F*(x-v-dv-dx)+qStar)=0 := by
    rw [hw,hQ] at hC
    linear_combination hC
  have hx : x-z≠0 := sub_ne_zero.mpr hxz
  have hd := (mul_eq_zero.mp hh).resolve_left hx
  have hc := (mul_eq_zero.mp hq).resolve_left hx
  linear_combination hc+F*hd

/-- Common-root resultant for two quadratics, without any assumption on
which leaders are live. -/
theorem quadratic_common_root {a b c d e f x : K}
    (hf : a*x^2+b*x+c=0) (hg : d*x^2+e*x+f=0) :
    (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e)=0 := by
  have h1 : a*f-c*d=-(a*e-b*d)*x := by
    linear_combination a*hg-d*hf
  have h2 : b*f-c*e=(a*e-b*d)*x^2 := by
    linear_combination b*hg-e*hf
  rw [h1,h2]
  ring

/-- If the quartic signal is zero at the first physical middle ghost,
the literal tap and the commutator signal there are both zero. -/
theorem zero_signal [IsDomain K] {tap B p W G D Q : K}
    (hB : B≠0) (hp : p≠0) (hG : G≠0)
    (hw : W=0) (h0 : tap*B*p= -G*W)
    (hC : D*tap*B*p=G*Q) :
    tap=0 ∧ Q=0 := by
  have hh : tap*(B*p)=0 := by
    simpa [hw, mul_assoc] using h0
  have ht := (mul_eq_zero.mp hh).resolve_right (mul_ne_zero hB hp)
  have he : G*Q=0 := by simpa [ht] using hC.symm
  exact ⟨ht,(mul_eq_zero.mp he).resolve_left hG⟩

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneFirstMiddle
