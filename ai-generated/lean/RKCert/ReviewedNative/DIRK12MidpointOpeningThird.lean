module

public import RKCert.ReviewedNative.DIRK12MidpointOpeningSecond
public import RKCert.ReviewedNative.DIRK12MidpointOpeningG3Data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual third opening row. The only new algebraic relation is
the verified G3 substitution into Q36. Two scalar read identities are
then exactly the compensated kernel of the causal three-node read. -/

namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open RKResearch Graded DIRK12MidpointGhost
open DIRK12MidpointRealInterval DirectedRatBox
open IntegerPolyRootReplay.Packing
open scoped Matrix BigOperators

theorem g3_form (x y : ℝ) :
    360*(J 0 x y 1*J 1 x y y-J 1 x y 1*J 0 x y y)*Q0 x -
      dc x y*x^3*(x-1)^3*Q0 y = (21/4)*x*y*(x-y)*(y-1)*g3 x y := by
  rw [q_factor x,q_factor y]
  norm_num [J,dc,quartic,g3,g3Terms,bivar]
  ring

noncomputable def kY (x y : ℝ) : ℝ := K (nu x) y

theorem third_kernel_payment {x : ℝ} (hx : Encloses xBox x) (hx0 : realX x=0) :
    let y := yOf x
    J 0 x y y=rY x y*J 0 x y 1+kY x y*J 1 x y 1 ∧
    J 1 x y y=rY x y*J 1 x y 1+kY x y*(J 2 x y 1-eps x) := by
  let y := yOf x
  change _ = _ ∧ _ = _
  obtain ⟨hd,hc,_,hq,_,_⟩ := guarded_modes hx
  let I0 := J 0 x y 1
  let I1 := J 1 x y 1
  let I2 := J 2 x y 1-eps x
  let U := J 0 x y y
  let V := J 1 x y y
  let D := I0*I2-I1^2
  change U=rY x y*I0+kY x y*I1 ∧ V=rY x y*I1+kY x y*I2
  have d : D = -(db x*dc x y)/10800 := forward_kernel_det x y
  have d0 : D≠0 := by rw [d]; exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hd hc)) (by norm_num)
  have RX : D*rY x y=I2*U-I1*V := by
    rw [d,rY]
    change (-(db x*dc x y)/10800)*(-10800*(I2*U-I1*V)/(db x*dc x y))=_
    calc
      _ = (db x*dc x y)*(I2*U-I1*V)/(db x*dc x y) := by ring
      _ = _ := mul_div_cancel_left₀ _ (mul_ne_zero hd hc)
  have G : 360*(I0*V-I1*U)*Q0 x=dc x y*x^3*(x-1)^3*Q0 y := by
    have G0 := g3_real_zero hx0
    change g3 x y=0 at G0
    have F := g3_form x y
    rw [G0,mul_zero,sub_eq_zero] at F
    exact F
  have KY : D*kY x y=I0*V-I1*U := by
    calc
      D*kY x y=dc x y*x^3*(x-1)^3*Q0 y/(360*Q0 x) := by
        rw [d,kY,K_fit,nu,kX]
        field_simp [hd,hq]
        ring
      _ = _ := by
        apply (div_eq_iff (mul_ne_zero (by norm_num) hq)).2
        linear_combination -G
  constructor
  · have zero : D*(U-(rY x y*I0+kY x y*I1))=0 := by
      dsimp only [D] at ⊢
      linear_combination -I0*RX-I1*KY
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left d0)
  · have zero : D*(V-(rY x y*I1+kY x y*I2))=0 := by
      dsimp only [D] at ⊢
      linear_combination -I1*RX-I2*KY
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left d0)

/-- Paid normalized live-only read on a single entering monomial. -/
noncomputable def readPaid (s r k e : ℝ) (j : Nat) : ℝ :=
  (s^(j+1)-r)/((j+1:Nat):ℝ)-k/((j+2:Nat):ℝ)+(if j=5 then k*e else 0)

noncomputable def weights3 (x y u v w : ℝ) (i : Fin 3) : ℝ :=
  if i=0 then (w-(x+y)*v+x*y*u)/((1-x)*(1-y))
  else if i=1 then (w-(1+y)*v+y*u)/(x*(x-1)*(x-y))
  else (w-(1+x)*v+x*u)/(y*(y-1)*(y-x))

def eval3 (p : Fin 3 → ℝ) (x y : ℝ) (j : Nat) : ℝ := p 0+p 1*x^j+p 2*y^j

theorem weights3_paid (x y u v w : ℝ) (x0 : x≠0) (y0 : y≠0)
    (x1 : x≠1) (y1 : y≠1) (xy : x≠y) :
    eval3 (weights3 x y u v w) x y 1=u ∧
    eval3 (weights3 x y u v w) x y 2=v ∧
    eval3 (weights3 x y u v w) x y 3=w := by
  have e1 : 1-x≠0 := sub_ne_zero.mpr x1.symm
  have e2 : 1-y≠0 := sub_ne_zero.mpr y1.symm
  have e3 : x-1≠0 := sub_ne_zero.mpr x1
  have e4 : y-1≠0 := sub_ne_zero.mpr y1
  have e5 : x-y≠0 := sub_ne_zero.mpr xy
  have e6 : y-x≠0 := sub_ne_zero.mpr xy.symm
  refine ⟨?_,?_,?_⟩ <;> norm_num [eval3,weights3] <;>
    field_simp [e1,e2,e3,e4,e5,e6,x0,y0] <;> ring

theorem recurrence3 (p : Fin 3 → ℝ) (x y : ℝ) (j : Nat) :
    eval3 p x y (j+3)=(1+x+y)*eval3 p x y (j+2)-(x+y+x*y)*eval3 p x y (j+1)+
      x*y*eval3 p x y j := by
  simp [eval3,pow_add]
  ring

theorem paid_recurrence4 (x y r k e : ℝ)
    (h : J 0 x y y=r*J 0 x y 1+k*J 1 x y 1) :
    readPaid y r k e 4 =
      (1+x+y)*readPaid y r k e 3-(x+y+x*y)*readPaid y r k e 2+
      x*y*readPaid y r k e 1 := by
  norm_num [readPaid,J] at h ⊢
  linear_combination h

theorem paid_recurrence5 (x y r k e : ℝ)
    (h : J 1 x y y=r*J 1 x y 1+k*(J 2 x y 1-e)) :
    readPaid y r k e 5 =
      (1+x+y)*readPaid y r k e 4-(x+y+x*y)*readPaid y r k e 3+
      x*y*readPaid y r k e 2 := by
  norm_num [readPaid,J] at h ⊢
  linear_combination h

noncomputable def thirdCoeffs (x : ℝ) : Fin 3 → ℝ :=
  let y := yOf x
  let M := readPaid y (rY x y) (kY x y) (eps x)
  weights3 x y (M 1) (M 2) (M 3)

theorem third_reads (x : ℝ) (hx : Encloses xBox x) (hx0 : realX x=0) (m : Fin 5) :
    eval3 (thirdCoeffs x) x (yOf x) (m.val+1) =
      readPaid (yOf x) (rY x (yOf x)) (kY x (yOf x)) (eps x) (m.val+1) := by
  let y := yOf x
  let V := readPaid y (rY x y) (kY x y) (eps x)
  let L := thirdCoeffs x
  change eval3 L x y (m.val+1)=V (m.val+1)
  obtain ⟨xp,xy,y1⟩ := ratios_ordered hx
  obtain ⟨e0,e1⟩ := third_kernel_payment hx hx0
  obtain ⟨h1,h2,h3⟩ := weights3_paid x y (V 1) (V 2) (V 3)
    xp.ne' (xp.trans xy).ne' (xy.trans y1).ne y1.ne xy.ne
  change eval3 L x y 1=V 1 at h1
  change eval3 L x y 2=V 2 at h2
  change eval3 L x y 3=V 3 at h3
  have h4 : eval3 L x y 4=V 4 := by
    have hr := recurrence3 L x y 1
    change eval3 L x y 4=(1+x+y)*eval3 L x y 3-(x+y+x*y)*eval3 L x y 2+x*y*eval3 L x y 1 at hr
    rw [hr,h1,h2,h3]
    exact (paid_recurrence4 x y _ _ _ e0).symm
  have h5 : eval3 L x y 5=V 5 := by
    have hr := recurrence3 L x y 2
    change eval3 L x y 5=(1+x+y)*eval3 L x y 4-(x+y+x*y)*eval3 L x y 3+x*y*eval3 L x y 2 at hr
    rw [hr,h2,h3,h4]
    exact (paid_recurrence5 x y _ _ _ e1).symm
  fin_cases m
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.third_kernel_payment
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.third_reads
