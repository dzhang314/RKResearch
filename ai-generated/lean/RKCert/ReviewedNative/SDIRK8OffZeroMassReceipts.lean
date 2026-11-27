module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8OffZeroMassReceipts

/-- The two moment equations of a monic remaining linear nodal factor. -/
theorem linearHankel {K : Type*} [CommRing K] (m0 m1 m2 x : K)
    (h0 : m1-x*m0=0) (h1 : m2-x*m1=0) :
    m0*m2-m1^2=0 := by
  linear_combination -m1*h0+m0*h1

/-- The three moment equations of a monic remaining quadratic nodal
factor force the order-three Hankel determinant to vanish. -/
theorem quadraticHankel {K : Type*} [CommRing K] (m0 m1 m2 m3 m4 x y : K)
    (h0 : m0*y+m1*x+m2=0) (h1 : m1*y+m2*x+m3=0)
    (h2 : m2*y+m3*x+m4=0) :
    m0*m2*m4+2*m1*m2*m3-m0*m3^2-m1^2*m4-m2^3=0 := by
  linear_combination (m1*m3-m2^2)*h0+(m1*m2-m0*m3)*h1+(m0*m2-m1^2)*h2

/-- An active pair with nonzero residuals and zero first and second
residual moments has just one residual value and cancels in weight. -/
theorem activePairCancels {K : Type*} [Field K] (b c g h : K)
    (hb : b≠0) (hg : g≠0)
    (h1 : b*g+c*h=0) (h2 : b*g^2+c*h^2=0) :
    g=h ∧ b+c=0 := by
  have z : (b*g)*(g-h)=0 := by linear_combination h2-h*h1
  have eq : g=h := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (mul_ne_zero hb hg))
  have zz : g*(b+c)=0 := by
    rw [←eq] at h1
    linear_combination h1
  exact ⟨eq,(mul_eq_zero.mp zz).resolve_left hg⟩

def gauss70 {K : Type*} [CommRing K] (x : K) : K :=
  70*x^4-140*x^3+90*x^2-20*x+1

theorem gauss_reflect {K : Type*} [CommRing K] (x : K) :
    gauss70 (1-x)=gauss70 x := by unfold gauss70; ring

private theorem affineA {K : Type*} [CommRing K] (d : K) :
    (5103*d^2-5103*d+1296)*gauss70 d+(-63*d^2+63*d-4)*gauss70 (2-3*d)=12 := by
  unfold gauss70
  ring

private theorem affineB {K : Type*} [Field K] [CharZero K] (d : K) :
    (-28672*d^2+28672*d-6528)*gauss70 d+
      (1792*d^2-1792*d+120)*gauss70 (2*d-1/2)=117 := by
  unfold gauss70
  ring

/-- The only possible third clocks in the mixed-repeat, two-active-site
three-distinct-Gauss branch cannot themselves be fourth-Gauss clocks. -/
theorem affineGaussNoRoots {K : Type*} [Field K] [CharZero K]
    (d : K) (hd : gauss70 d = 0) :
    gauss70 (2-3*d)≠0 ∧ gauss70 (3*d-1)≠0 ∧ gauss70 (2*d-1/2)≠0 := by
  have hA : gauss70 (2-3*d)≠0 := by
    intro ha
    have hz := affineA d
    simp [hd,ha] at hz
  have hB : gauss70 (2*d-1/2)≠0 := by
    intro hb
    have hz := affineB d
    rw [hd,hb] at hz
    norm_num at hz
  refine ⟨hA,?_,hB⟩
  have hr := gauss_reflect (3*d-1)
  rw [show 1-(3*d-1)=2-3*d by ring] at hr
  rwa [←hr]

end RKCert.ReviewedNative.SDIRK8OffZeroMassReceipts
