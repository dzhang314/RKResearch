import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Undivided receipts for the live reciprocity mixed read and the literal
three-late quintic. The finite old-field replays are separate. -/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLiveFinite

variable {K : Type*} [CommRing K]

theorem adjacent_mixed
    {u k n h ell e rho f d cv p0 j j2 z v p q tap : K}
    (hk : u*k=n*h) (he : n*ell=e) (hf : n*rho=f)
    (hd : u*d=cv)
    (ht : tap=ell*k-j+d*(p0-k))
    (hm : (z-v)*tap=j2-rho*k)
    (hz : q*z=p) :
    (p-v*q)*((e*h-j*u)*u+cv*(p0*u-n*h))-
       q*(j2*u-f*h)*u=0 := by
  have ht' : u^2*tap=(e*h-j*u)*u+cv*(p0*u-n*h) := by
    calc
      u^2*tap = u*(ell*(u*k)-j*u)+(u*d)*(p0*u-u*k) := by
        rw [ht]
        ring
      _ = (e*h-j*u)*u+cv*(p0*u-n*h) := by
        rw [hk,hd,← he]
        ring
  have hm' : (z-v)*((e*h-j*u)*u+cv*(p0*u-n*h))=(j2*u-f*h)*u := by
    calc
      (z-v)*((e*h-j*u)*u+cv*(p0*u-n*h)) = u^2*((z-v)*tap) := by
        rw [← ht']
        ring
      _ = (j2*u-f*h)*u := by
        rw [hm,← hf]
        calc
          u^2*(j2-rho*k) = (j2*u-rho*(u*k))*u := by ring
          _ = (j2*u-n*rho*h)*u := by rw [hk]; ring
  linear_combination q*hm'-((e*h-j*u)*u+cv*(p0*u-n*h))*hz

/-- The reconstructed quintic is affine because the two top parameter
columns are both multiples of the same old cubic. -/
theorem affine_cross (u uz b bz r rz ell t : K) :
    (uz+t*rz)*(b+t*ell*r)-(bz+t*ell*rz)*(u+t*r) =
      uz*b-bz*u+t*(rz*b+uz*ell*r-bz*r-ell*rz*u) := by
  ring

theorem affine_factor {a b V : K} (h : a+b*V=0) (y : K) :
    a+b*y=b*(y-V) := by
  linear_combination h

/-- In the three-late case a cubic with vanishing cubic leader must
vanish identically; numerical contacts with unrelated rows do not enter. -/
theorem degree_drop_three_roots [IsDomain K]
    {a b c x y z : K} (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hx : a+b*x+c*x^2=0) (hy : a+b*y+c*y^2=0) (hz : a+b*z+c*z^2=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  have h1 : (x-y)*(b+c*(x+y))=0 := by linear_combination hx-hy
  have h2 : (x-z)*(b+c*(x+z))=0 := by linear_combination hx-hz
  have h3 := (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hxy)
  have h4 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hxz)
  have hh : c*(y-z)=0 := by linear_combination h3-h4
  have hc := (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hyz)
  have hb : b=0 := by simpa [hc] using h3
  have ha : a=0 := by simpa [hb,hc] using hx
  exact ⟨ha,hb,hc⟩

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLiveFinite
