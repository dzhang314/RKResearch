module

public import RKCert.ReviewedNative.DIRK12MidpointOpeningThirdPhysical
public import RKCert.ReviewedNative.DIRK12MidpointOpeningTGate0
public import RKCert.ReviewedNative.DIRK12MidpointOpeningTGate1
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! At the actual fourth opening clock t, the two ordinary
compensated kernel reads vanish for the already fitted shared modes.
Factoring the integer gates precedes their exact Q36 verification. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open DirectedRatBox DIRK12MidpointRealInterval
open IntegerPolyRootReplay.Packing

noncomputable def tOf (x : ℝ) : ℝ := ratHorner tCoeffs x

def bTOrd : Box := ⟨336/1000,337/1000⟩

set_option maxHeartbeats 0
set_option maxRecDepth 30000

theorem t_enclosed {x : ℝ} (hx : Encloses xBox x) : Encloses bTOrd (tOf x) := by
  have e := rat_horner_sound tCoeffs hx
  exact ⟨(Rat.cast_le.mpr
      (show bTOrd.lo≤(ratHornerBox tCoeffs xBox).lo by decide +kernel)).trans e.1,
    e.2.trans (Rat.cast_le.mpr
      (show (ratHornerBox tCoeffs xBox).hi≤bTOrd.hi by decide +kernel))⟩

theorem fourth_clocks_ordered {x : ℝ} (hx : Encloses xBox x) :
    0<x ∧ x<tOf x ∧ tOf x<yOf x ∧ yOf x<1 := by
  have X := x_enclosed hx
  have Y := y_enclosed hx
  have T := t_enclosed hx
  exact ⟨(ratios_ordered hx).1,
    (X.2.trans_lt (Rat.cast_lt.mpr (by decide +kernel : bx.hi<bTOrd.lo))).trans_le T.1,
    (T.2.trans_lt (Rat.cast_lt.mpr (by decide +kernel : bTOrd.hi<byy.lo))).trans_le Y.1,
    (ratios_ordered hx).2.2⟩

def qHat (t : ℝ) : ℝ := t*(t-1)*quartic t
def cHat (t : ℝ) : ℝ :=
  t*(429*t^6-2574*t^5+5940*t^4-6600*t^3+3600*t^2-864*t+64)
noncomputable def jHat (n : Nat) (x y t : ℝ) : ℝ := 420*J n x y t
def rNum (x : ℝ) : ℝ := x^3*(15*x^3-49*x^2+55*x-20)
def kNum (x : ℝ) : ℝ := -30*x^3*(x-1)^3

theorem Q0_hat (t : ℝ) : Q0 t=(21/4)*qHat t := by rw [q_factor,qHat]; ring
theorem cHat_eq (t : ℝ) : cHat t=5*C0 t := by unfold cHat C0 leg7; ring

theorem qHat_nonzero {t : ℝ} (h : Q0 t≠0) : qHat t≠0 := by
  intro e
  exact h (by rw [Q0_hat,e,mul_zero])

theorem rNum_eq (x : ℝ) (h : db x≠0) : rNum x=db x*rX x := by
  unfold rX rNum
  symm
  rw [← mul_div_assoc,mul_div_cancel_left₀ _ h]

theorem kNum_eq (x : ℝ) (h : db x≠0) : kNum x=db x*kX x := by
  unfold kX kNum
  symm
  rw [← mul_div_assoc,mul_div_cancel_left₀ _ h]

noncomputable def rxRead (x y : ℝ) : ℝ :=
  jHat 0 x y 1*(5*rNum x+db x*cHat x)+5*jHat 1 x y 1*kNum x

noncomputable def ryRead (x y : ℝ) : ℝ := 5*jHat 0 x y y+jHat 0 x y 1*cHat y

noncomputable def gate0Full (x y t : ℝ) : ℝ :=
  db x*qHat x*qHat y*(y-x)*(5*jHat 0 x y t+jHat 0 x y 1*cHat t) -
    qHat t*((y-t)*qHat y*rxRead x y+(t-x)*db x*qHat x*ryRead x y)

noncomputable def gate1Full (x y t : ℝ) : ℝ :=
  qHat x*(jHat 0 x y 1*jHat 1 x y t-jHat 1 x y 1*jHat 0 x y t) -
    490*dc x y*x^3*(x-1)^3*qHat t

def factor0 (x y t : ℝ) : ℝ :=
  105*x*(x-1)*y*(y-1)*t*(t-1)*(y-x)*(t-x)*(t-y)*db x

def factor1 (x _y t : ℝ) : ℝ := 490*x*(x-1)*t*(t-1)*(t-x)

theorem factor_gate0 (x y t : ℝ) :
    gate0Full x y t=factor0 x y t*trivar tTerms0 x y t := by
  norm_num [gate0Full,factor0,rxRead,ryRead,db,qHat,cHat,quartic,jHat,J,rNum,kNum,tTerms0,trivar]
  ring

theorem factor_gate1 (x y t : ℝ) :
    gate1Full x y t=factor1 x y t*trivar tTerms1 x y t := by
  norm_num [gate1Full,factor1,dc,qHat,quartic,jHat,J,tTerms1,trivar]
  ring

noncomputable def rAt (x s : ℝ) : ℝ := R (alpha x (yOf x)) (mu x (yOf x)) s
noncomputable def kAt (x s : ℝ) : ℝ := K (nu x) s

theorem R_interpolate (x y z : ℝ) (hxy : y-x≠0) :
    (y-x)*(R (alpha x y) (mu x y) z+C0 z)=
      Q0 z*((y-z)*rhoX x+(z-x)*rhoY x y) := by
  rw [R_fit]
  have a := alpha_fits x y hxy
  unfold mu slope at ⊢
  unfold slope at a
  linear_combination Q0 z*(z-x)*a

theorem K_propagate (x z : ℝ) (hx : Q0 x≠0) : Q0 x*kAt x z=Q0 z*kX x := by
  rw [kAt,K_fit,nu]
  field_simp [hx]

theorem K_hat_propagate (x z : ℝ) (hx : Q0 x≠0) : qHat x*kAt x z=qHat z*kX x := by
  have h := K_propagate x z hx
  rw [Q0_hat x,Q0_hat z] at h
  linear_combination (4/21:ℝ)*h

theorem joint_interpolate {x : ℝ} (hx : Encloses xBox x) (hx0 : realX x=0) (z : ℝ) :
    let y := yOf x
    let I0 := J 0 x y 1
    let I1 := J 1 x y 1
    (y-x)*qHat x*qHat y*(I0*(rAt x z+C0 z)+I1*kAt x z) =
      qHat z*((y-z)*qHat y*(I0*(rX x+C0 x)+I1*kX x) +
        (z-x)*qHat x*(J 0 x y y+I0*C0 y)) := by
  let y := yOf x
  let I0 := J 0 x y 1
  let I1 := J 1 x y 1
  change (y-x)*qHat x*qHat y*(I0*(rAt x z+C0 z)+I1*kAt x z)=_
  obtain ⟨_,_,_,hq,hqy,hxy⟩ := guarded_modes hx
  have hr := R_interpolate x y z hxy
  change (y-x)*(rAt x z+C0 z)=_ at hr
  have ex : Q0 x*rhoX x=rX x+C0 x := by
    rw [rhoX,←mul_div_assoc,mul_div_cancel_left₀ _ hq]
  have ey : Q0 y*rhoY x y=rY x y+C0 y := by
    rw [rhoY,←mul_div_assoc,mul_div_cancel_left₀ _ hqy]
  have rLine : (y-x)*Q0 x*Q0 y*(rAt x z+C0 z) =
      Q0 z*((y-z)*Q0 y*(rX x+C0 x)+(z-x)*Q0 x*(rY x y+C0 y)) := by
    linear_combination Q0 x*Q0 y*hr + Q0 z*(y-z)*Q0 y*ex + Q0 z*(z-x)*Q0 x*ey
  have kz := K_propagate x z hq
  have ky := K_propagate x y hq
  have kLine : (y-x)*Q0 x*Q0 y*kAt x z =
      Q0 z*((y-z)*Q0 y*kX x+(z-x)*Q0 x*kAt x y) := by
    linear_combination (y-x)*Q0 y*kz - Q0 z*(z-x)*ky
  have yPay := (third_kernel_payment hx hx0).1
  change J 0 x y y=rY x y*I0+kAt x y*I1 at yPay
  have yRead : J 0 x y y+I0*C0 y=I0*(rY x y+C0 y)+I1*kAt x y := by
    linear_combination yPay
  rw [yRead]
  rw [Q0_hat x,Q0_hat y,Q0_hat z] at rLine kLine
  linear_combination (16/441:ℝ)*(I0*rLine+I1*kLine)

theorem gate0_semantic {x : ℝ} (hx : Encloses xBox x) (hx0 : realX x=0) (z : ℝ) :
    let y := yOf x
    gate0Full x y z=(2100*db x*qHat x*qHat y*(y-x))*
      (J 0 x y z-J 0 x y 1*rAt x z-J 1 x y 1*kAt x z) := by
  let y := yOf x
  let I0 := J 0 x y 1
  let I1 := J 1 x y 1
  change gate0Full x y z=(2100*db x*qHat x*qHat y*(y-x))*
    (J 0 x y z-I0*rAt x z-I1*kAt x z)
  have hdb := (db_pos hx).ne'
  have ux : rxRead x y=2100*db x*(I0*(rX x+C0 x)+I1*kX x) := by
    rw [rxRead,rNum_eq x hdb,kNum_eq x hdb,cHat_eq]
    unfold jHat
    dsimp only [I0,I1]
    ring
  have uy : ryRead x y=2100*(J 0 x y y+I0*C0 y) := by
    unfold ryRead jHat
    rw [cHat_eq]
    dsimp only [I0]
    ring
  have uz : 5*jHat 0 x y z+jHat 0 x y 1*cHat z=2100*(J 0 x y z+I0*C0 z) := by
    unfold jHat
    rw [cHat_eq]
    dsimp only [I0]
    ring
  rw [gate0Full,ux,uy,uz]
  have h := joint_interpolate hx hx0 z
  change (y-x)*qHat x*qHat y*(I0*(rAt x z+C0 z)+I1*kAt x z) =
    qHat z*((y-z)*qHat y*(I0*(rX x+C0 x)+I1*kX x)+(z-x)*qHat x*(J 0 x y y+I0*C0 y)) at h
  linear_combination 2100*db x*h

theorem gate1_semantic {x : ℝ} (hx : Encloses xBox x) (z : ℝ) :
    let y := yOf x
    gate1Full x y z=176400*qHat x*
      (J 0 x y 1*J 1 x y z-J 1 x y 1*J 0 x y z -
        (J 0 x y 1*(J 2 x y 1-eps x)-(J 1 x y 1)^2)*kAt x z) := by
  let y := yOf x
  change gate1Full x y z=_
  have hq := (qvals_neg hx).1.ne
  have hK := K_hat_propagate x z hq
  have hn := (kNum_eq x (db_pos hx).ne').symm
  have c : 176400*qHat x*(J 0 x y 1*(J 2 x y 1-eps x)-(J 1 x y 1)^2)*kAt x z =
      490*dc x y*x^3*(x-1)^3*qHat z := by
    rw [forward_kernel_det]
    unfold kNum at hn
    linear_combination (-49/3:ℝ)*dc x y*db x*hK+(-49/3:ℝ)*dc x y*qHat z*hn
  unfold gate1Full jHat
  linear_combination c

theorem I0_pos {x : ℝ} (hx : Encloses xBox x) : 0<J 0 x (yOf x) 1 := by
  have X := x_enclosed hx
  have Y := y_enclosed hx
  have h10 : Encloses (point 10) (10:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 10
  have h5 : Encloses (point 5) (5:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 5
  have h3 : Encloses (point 3) (3:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 3
  have B := enclose_add (enclose_sub (enclose_sub (enclose_mul h10 (enclose_mul X Y))
    (enclose_mul h5 X)) (enclose_mul h5 Y)) h3
  have neg := negative B (by decide +kernel)
  have h : J 0 x (yOf x) 1=-(10*(x*yOf x)-5*x-5*yOf x+3)/60 := by norm_num [J]; ring
  rw [h]
  exact div_pos (neg_pos.mpr neg) (by norm_num)

theorem fourth_kernel_payment {x : ℝ} (hx : Encloses xBox x) (hx0 : realX x=0) :
    let y := yOf x
    let t := tOf x
    J 0 x y t=rAt x t*J 0 x y 1+kAt x t*J 1 x y 1 ∧
    J 1 x y t=rAt x t*J 1 x y 1+kAt x t*(J 2 x y 1-eps x) := by
  let y := yOf x
  let t := tOf x
  let I0 := J 0 x y 1
  let I1 := J 1 x y 1
  let I2 := J 2 x y 1-eps x
  change J 0 x y t=rAt x t*I0+kAt x t*I1 ∧ J 1 x y t=rAt x t*I1+kAt x t*I2
  obtain ⟨hd,_,_,qx,qy,hxy⟩ := guarded_modes hx
  have qxh := qHat_nonzero qx
  have qyh := qHat_nonzero qy
  have h0 : gate0Full x y t=0 := by
    have h := tGate0_zero hx0
    change trivar tTerms0 x y t=0 at h
    rw [factor_gate0,h,mul_zero]
  have h1 : gate1Full x y t=0 := by
    have h := tGate1_zero hx0
    change trivar tTerms1 x y t=0 at h
    rw [factor_gate1,h,mul_zero]
  have m0 := gate0_semantic hx hx0 t
  change gate0Full x y t=(2100*db x*qHat x*qHat y*(y-x))*
    (J 0 x y t-I0*rAt x t-I1*kAt x t) at m0
  rw [h0] at m0
  have dn : 2100*db x*qHat x*qHat y*(y-x)≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hd) qxh) qyh) hxy
  have n0 := (mul_eq_zero.mp m0.symm).resolve_left dn
  have a : J 0 x y t=rAt x t*I0+kAt x t*I1 := by
    change J 0 x y t-I0*rAt x t-I1*kAt x t=0 at n0
    linear_combination n0
  have m1 := gate1_semantic hx t
  change gate1Full x y t=176400*qHat x*
     (I0*J 1 x y t-I1*J 0 x y t-(I0*I2-I1^2)*kAt x t) at m1
  rw [h1] at m1
  have n1 := (mul_eq_zero.mp m1.symm).resolve_left (mul_ne_zero (by norm_num) qxh)
  change I0*J 1 x y t-I1*J 0 x y t-(I0*I2-I1^2)*kAt x t=0 at n1
  have zero : I0*(J 1 x y t-(rAt x t*I1+kAt x t*I2))=0 := by
    linear_combination n1+I1*a
  exact ⟨a,sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (I0_pos hx).ne')⟩

end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.factor_gate0
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.factor_gate1
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.fourth_kernel_payment
