import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoBetaOne

variable {K : Type*} [CommRing K]

/-- Fourth-clean quintic transfer to ordinary scalars. Only the live
carrier is cancelled, not the quartic signal or the quartic primitive. -/
theorem quintic_sample [IsDomain K] {u l0 j w lp Q theta A D y : K}
    (hu : u≠0) (h0 : u*l0=j*w)
    (h5 : u*lp=j*Q+theta*j*u) (hQ : Q=w*(A+D*y)) :
    lp=theta*j+(A+D*y)*l0 := by
  have hh : u*(lp-theta*j-(A+D*y)*l0)=0 := by
    linear_combination h5+j*hQ-(A+D*y)*h0
  have he := (mul_eq_zero.mp hh).resolve_left hu
  linear_combination he

/-- The same reciprocal transfer for the affine commutator multiple,
including a possible zero quartic signal at the sampled clock. -/
theorem commutator_sample [IsDomain K] {u l0 j w Q P t m s : K}
    (hu : u≠0) (h0 : u*l0=j*w)
    (hC : P= -t*u) (hM : P=m*Q) (hQ : Q=w*s) :
    t*j=-m*s*l0 := by
  have hh : u*(t*j+m*s*l0)=0 := by
    linear_combination j*(hC-hM-m*hQ)+m*s*h0
  have he := (mul_eq_zero.mp hh).resolve_left hu
  linear_combination he

theorem affine_middle [IsDomain K] {f w a d x : K}
    (hw : w≠0) (h : f=w*(a+d*x)) (hz : f=0)
    (hl : a≠0 ∨ d≠0) :
    a+d*x=0 ∧ d≠0 := by
  have hh : w*(a+d*x)=0 := by simpa [hz] using h.symm
  have he := (mul_eq_zero.mp hh).resolve_left hw
  refine ⟨he, ?_⟩
  intro hd
  have ha : a=0 := by simpa [hd] using he
  exact hl.elim (fun h0 => h0 ha) (fun h0 => h0 hd)

/-- Eliminate the cubic parameter using its actual fourth reverse
diagonal and its actual first forward clean read. -/
theorem first_clean_eliminant {l0 D Jm Jr t : K}
    (h4 : D+t*l0=0) (hb : Jm+t*Jr=0) :
    l0*Jm-D*Jr=0 := by
  linear_combination l0*hb-Jr*h4

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoBetaOne
