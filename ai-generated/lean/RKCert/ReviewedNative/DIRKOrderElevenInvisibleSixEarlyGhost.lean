import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Native scalar transfer for the true early reverse ghost. The rooted
spaces and chronology that supply the hypotheses are separate. -/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixEarlyGhost

variable {K : Type*} [CommRing K]

/-- Two exact masks on the same five forward ghosts. -/
theorem common_hull_affine (U J K0 R q2 q3 η L : K)
    (h5 : J + U*q2 = η*R) (h6 : K0 + U*q3 = R*L) :
    η*K0 - J*L = U*(q2*L-η*q3) := by
  linear_combination η*h6 - L*h5

/-- The sole other ghost can be retained without dividing by a
putative grade-seven leading coefficient. -/
theorem common_hull_last_root (U J K0 R q2 q4 η f L : K)
    (h5 : J+U*q2=η*R) (h7 : K0+U*q4=R*f*L) :
    η*K0-J*f*L=U*(q2*f*L-η*q4) := by
  linear_combination η*h7-f*L*h5

/-- The quartic fit with only one old-pole factor has an exact
quadratic representative after subtracting its cubic leader. -/
theorem pole_removed_remainder (p0 p1 p2 c0 c1 c2 z y : K) :
    (y-z)*(p0+p1*y+p2*y^2) - p2*(y^3+c2*y^2+c1*y+c0) =
      (-z*p0-p2*c0) + (p0-z*p1-p2*c1)*y +
        (p1-z*p2-p2*c2)*y^2 := by ring

theorem pole_removed_at_root (p0 p1 p2 c0 c1 c2 z : K) :
    (-z*p0-p2*c0) + (p0-z*p1-p2*c1)*z +
        (p1-z*p2-p2*c2)*z^2 = -p2*(z^3+c2*z^2+c1*z+c0) := by ring

theorem quartic_coeff_zero [IsDomain K] {p0 p1 p2 c0 c1 c2 z : K}
    (hR : z^3+c2*z^2+c1*z+c0≠0)
    (h0 : (-z*p0-p2*c0)+(p0-z*p1-p2*c1)*z+
          (p1-z*p2-p2*c2)*z^2=0) :
    p2=0 := by
  rw [pole_removed_at_root] at h0
  by_contra hp
  exact (mul_ne_zero (neg_ne_zero.mpr hp) hR) h0

/-- The first genuine ghost diagonal is zero even if the affine
slope is -1, or the numerical ghost clock is zero. -/
theorem first_literal_diagonal_zero [IsDomain K]
    {z r1 l t w0 s δ κ d : K}
    (hw : w0=0) (h0 : d=l) (h1 : r1=z*l)
    (h2 : r1=z*l-t-κ*w0) (h3 : (1+s)*t=l^2+δ*w0) :
    d=0 := by
  have ht : t=0 := by
    linear_combination h2 - h1 - κ*hw
  have hl : l^2=0 := by
    linear_combination (1+s)*ht - h3 - δ*hw
  by_contra hd
  exact (pow_ne_zero 2 (h0 ▸ hd)) hl

/-- The second literal gap ghost has live diagonal and tap when the
old affine slope is nonzero, without a positivity hypothesis. -/
theorem second_literal_taps [IsDomain K]
    {z w s d e l t : K}
    (hzw : w≠z) (hl : l=s*(w-z)) (h0 : d+e=l)
    (h1 : z*e+w*d=w*l-t) (h2 : (1+s)*t=l^2) :
    (1+s)*d=l ∧ (1+s)*e=s^2*(w-z) := by
  have hh : (w-z)*((1+s)*d-l)=0 := by
    linear_combination (1+s)*(h1-z*h0) - h2 - l*hl
  have hd := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hzw))
  exact ⟨hd, by linear_combination (1+s)*h0 - hd + s*hl⟩

theorem one_late_supported_tap_zero [IsDomain K] {x a b U : K}
    (ha : a≠0) (hab : a≠b) (hU : U≠0) (hx : x*a*(a-b)*U=0) :
    x=0 := by
  by_contra h
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h ha) (sub_ne_zero.mpr hab)) hU) hx

theorem alpha_two_commutator_crossing [IsDomain K]
    {μ rZ rW θ uZ uW kV d V : K}
    (hV : V≠0) (hz : μ*rZ=θ*uZ) (hw : μ*rW=θ*uW)
    (ha : μ*kV=-d^2*V) :
    d^2*(rZ*uW-rW*uZ)=0 := by
  have hpair : μ*(rZ*uW-rW*uZ)=0 := by
    linear_combination uW*hz-uZ*hw
  have h : V*(d^2*(rZ*uW-rW*uZ))=0 := by
    linear_combination (rZ*uW-rW*uZ)*ha-kV*hpair
  exact (mul_eq_zero.mp h).resolve_left hV

theorem one_late_neighbor_debit
    {I0 I1 I2 P0 P1 q l t w δ s T d z V : K}
    (hT : I1-d*(P1-q)+T=l*q)
    (hQ : I0-d*P0=w*q)
    (h2 : I2=t*q+(z-V)*T)
    (hIBP : (1+s)*I2=l*I1+δ*I0)
    (hOld : (1+s)*t=l^2+δ*w)
    (hP : I1=l*P1+δ*P0)
    (hL : l=s*(V-z)) :
    (d+z-V)*T=d^2*(P1-q) := by
  have hh : (z-V)*T=d*(l*(P1-q)+δ*P0) := by
    linear_combination hIBP-(1+s)*h2-q*hOld+l*hT+δ*hQ-T*hL
  linear_combination hh-d*(hP-hT)

theorem reciprocal_origin_live [IsDomain K] {G U τ H : K}
    (hτ : τ≠0) (hH : H≠0) (hrec : G*U=τ*H) :
    U≠0 := by
  intro h
  rw [h,mul_zero] at hrec
  exact mul_ne_zero hτ hH hrec.symm

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixEarlyGhost
