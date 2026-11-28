import Mathlib.Tactic.Ring.Basic

/-! Ordinary mask, two-atom and fourth-read gates for the last
seven-label paired-star chart. -/

namespace RKResearch.Certified.SDIRKEightEightZeroStarUnequalLate

variable {R : Type*} [CommRing R]

theorem star_second_mask (Y d : R) :
    (2-d^2)*((Y-1)*(Y-d))-(Y^2-d^2)
      +(1+d)*((Y-1)*(Y^2-d^2))=(1+d)*((Y-d)*(Y^2-2)) := by
  ring1

def hankel (a b c d e : R) : R :=
  a*(c*e-d^2)-b*(b*e-d*c)+c*(b*d-c^2)

theorem extend_recurrence [IsDomain R] {a b c d e u v : R}
    (hD : a*c-b^2≠0) (hh : hankel a b c d e=0)
    (hu : (a*c-b^2)*u=b*d-c^2)
    (hv : (a*c-b^2)*v=b*c-a*d) :
    e+v*d+u*c=0 := by
  have hz : (a*c-b^2)*(e+v*d+u*c)=0 := by
    calc
      _ = (a*c-b^2)*e+((a*c-b^2)*v)*d+((a*c-b^2)*u)*c := by ring1
      _ = hankel a b c d e := by rw [hu,hv]; unfold hankel; ring1
      _ = 0 := hh
  exact (mul_eq_zero.mp hz).resolve_left hD

theorem shifted_geometric {a b c d e u v : R}
    (hs : d+e=-v) (hp : d*e=u) (hm : c+v*b+u*a=0) :
    c-e*b=d*(b-e*a) := by
  apply sub_eq_zero.mp
  calc
    _ = c-(d+e)*b+(d*e)*a := by ring1
    _ = 0 := by rw [hs,hp]; calc
      _ = c+v*b+u*a := by ring1
      _ = 0 := hm

theorem fourth_jump_cleared {m g q j k w : R}
    (hr : g*q=k*j) (hj : m*j=-(g*w)) :
    g*(m*q+k*w)=0 := by
  calc
    _ = m*(g*q)+k*(g*w) := by ring1
    _ = 0 := by rw [hr]; calc
      _ = k*(m*j)+k*(g*w) := by ring1
      _ = 0 := by rw [hj]; ring1

end RKResearch.Certified.SDIRKEightEightZeroStarUnequalLate
