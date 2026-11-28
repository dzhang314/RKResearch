module

public import RKCert.ReviewedNative.DIRK12MidpointRealForwardWiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

@[expose] public section

/-! Literal paid opening modes of the midpoint DIRK12 tableau. The
first Legendre relation has already fixed γ in terms of α. A factorized
2-by-2 fit determines the remaining shared α, μ, ν from the actual two
next clock ratios. Every moving denominator has a checked guard. -/
namespace RKResearch.Certified.DIRK12MidpointForward.Opening

open RKResearch.Certified DirectedRatBox DIRK12MidpointRealInterval

noncomputable def yOf (x : ℝ) : ℝ := ratHorner yCoeffs x

def db (x : ℝ) : ℝ := 5*x^2-5*x+1
def dc (x y : ℝ) : ℝ := 2*x*y-x-3*y^2+2*y
def quartic (x : ℝ) : ℝ := 33*x^4-132*x^3+168*x^2-72*x+8

noncomputable def rX (x : ℝ) : ℝ :=
  x^3*(15*x^3-49*x^2+55*x-20)/db x

noncomputable def kX (x : ℝ) : ℝ := -30*x^3*(x-1)^3/db x

noncomputable def eps (x : ℝ) : ℝ := -(7*x^2-7*x+2)/1260

/-- J_n integrates T^n·T(T−1)(T−x)(T−y) from 0 to its literal upper limit. -/
noncomputable def J (n : Nat) (x y t : ℝ) : ℝ :=
  t^(n+5)/((n+5:Nat):ℝ)-(1+x+y)*t^(n+4)/((n+4:Nat):ℝ)+
    (x+y+x*y)*t^(n+3)/((n+3:Nat):ℝ)-x*y*t^(n+2)/((n+2:Nat):ℝ)

noncomputable def rY (x y : ℝ) : ℝ :=
  -10800*((J 2 x y 1-eps x)*J 0 x y y-J 1 x y 1*J 1 x y y)/(db x*dc x y)

/-- True unweighted and weighted shifted-Legendre modes in normalized T. -/
noncomputable def R (alpha mu t : ℝ) : ℝ :=
  t*(alpha*leg5 (t/2)+mu*leg6 (t/2)+gammaFrom alpha*leg7 (t/2))

noncomputable def K (nu t : ℝ) : ℝ := (nu/2)*t*leg6 (t/2)

noncomputable def P0 (t : ℝ) : ℝ := t*(leg5 (t/2)+(6/7)*leg7 (t/2))
noncomputable def Q0 (t : ℝ) : ℝ := t*leg6 (t/2)
noncomputable def C0 (t : ℝ) : ℝ := (8/35)*t*leg7 (t/2)
noncomputable def slope (t : ℝ) : ℝ := (13/7)*(t-1)

theorem q_factor (t : ℝ) : Q0 t=(21/4)*t*(t-1)*quartic t := by
  unfold Q0 leg6 quartic
  ring

theorem p_factor (t : ℝ) : P0 t=slope t*Q0 t := by
  unfold P0 Q0 slope leg5 leg6 leg7
  ring

theorem R_fit (alpha mu t : ℝ) :
    R alpha mu t = Q0 t*(slope t*alpha+mu)-C0 t := by
  calc
    R alpha mu t=P0 t*alpha+Q0 t*mu-C0 t := by
      unfold R gammaFrom P0 Q0 C0
      ring
    _ = _ := by rw [p_factor]; ring

theorem K_fit (nu t : ℝ) : K nu t=(nu/2)*Q0 t := by unfold K Q0; ring

theorem fit_det (x y : ℝ) :
    P0 x*Q0 y-Q0 x*P0 y=(13/7)*(x-y)*Q0 x*Q0 y := by
  rw [p_factor,p_factor]
  unfold slope
  ring

noncomputable def rhoX (x : ℝ) : ℝ := (rX x+C0 x)/Q0 x
noncomputable def rhoY (x y : ℝ) : ℝ := (rY x y+C0 y)/Q0 y
noncomputable def alpha (x y : ℝ) : ℝ := (7/13)*(rhoY x y-rhoX x)/(y-x)
noncomputable def mu (x y : ℝ) : ℝ := rhoX x-slope x*alpha x y
noncomputable def nu (x : ℝ) : ℝ := 2*kX x/Q0 x

theorem alpha_fits (x y : ℝ) (h : y-x≠0) :
    (slope y-slope x)*alpha x y=rhoY x y-rhoX x := by
  rw [show slope y-slope x=(13/7)*(y-x) by unfold slope; ring]
  unfold alpha
  field_simp [h]

theorem modes_fit (x y : ℝ) (hx : Q0 x≠0) (hy : Q0 y≠0) (hxy : y-x≠0) :
    R (alpha x y) (mu x y) 1=1 ∧ R (alpha x y) (mu x y) x=rX x ∧
    R (alpha x y) (mu x y) y=rY x y ∧ K (nu x) x=kX x := by
  refine ⟨?_,?_,?_,?_⟩
  · unfold R
    simpa using mode_normalization (alpha x y) (mu x y)
  · rw [R_fit]
    have lin : slope x*alpha x y+mu x y=rhoX x := by unfold mu; ring
    rw [lin,rhoX]
    field_simp [hx]
    ring
  · rw [R_fit]
    have lin : slope y*alpha x y+mu x y=rhoY x y := by
      unfold mu
      linear_combination alpha_fits x y hxy
    rw [lin,rhoY]
    field_simp [hy]
    ring
  · rw [K_fit,nu]
    field_simp [hx]

/-- The guarded solved modes are the unique solution of the original
Legendre equations (after the known first row determines γ). -/
theorem modes_unique (x y u v w : ℝ) (hx : Q0 x≠0) (hy : Q0 y≠0) (hxy : y-x≠0)
    (rx : R u v x=rX x) (ry : R u v y=rY x y) (kx : K w x=kX x) :
    u=alpha x y ∧ v=mu x y ∧ w=nu x := by
  rw [R_fit] at rx ry
  have X : slope x*u+v=rhoX x := by
    rw [rhoX,eq_div_iff hx]
    linear_combination rx
  have Y : slope y*u+v=rhoY x y := by
    rw [rhoY,eq_div_iff hy]
    linear_combination ry
  have ca : (slope y-slope x)*(u-alpha x y)=0 := by
    linear_combination Y-X-alpha_fits x y hxy
  have sl : slope y-slope x≠0 := by
    rw [show slope y-slope x=(13/7)*(y-x) by unfold slope; ring]
    exact mul_ne_zero (by norm_num) hxy
  have uu : u=alpha x y := sub_eq_zero.mp ((mul_eq_zero.mp ca).resolve_left sl)
  refine ⟨uu,?_,?_⟩
  · rw [mu]
    linear_combination X-slope x*uu
  · rw [K_fit] at kx
    rw [nu,eq_div_iff hx]
    linear_combination 2*kx

theorem forward_kernel_det (x y : ℝ) :
    J 0 x y 1*(J 2 x y 1-eps x)-(J 1 x y 1)^2 = -(db x*dc x y)/10800 := by
  norm_num [J,eps,db,dc]
  ring

/-! Geometry and exact guards. Broad decimal brackets are used only inside
small sign checks, not as equalities or approximations to the coefficients. -/

def bx : Box := ⟨129/1000,13/100⟩
def byy : Box := ⟨799/1000,4/5⟩

set_option maxHeartbeats 0
set_option maxRecDepth 16000

theorem x_enclosed {x : ℝ} (hx : Encloses xBox x) : Encloses bx x :=
  ⟨(Rat.cast_le.mpr (show bx.lo≤xBox.lo by decide +kernel)).trans hx.1,
    hx.2.trans (Rat.cast_le.mpr (show xBox.hi≤bx.hi by decide +kernel))⟩

theorem y_enclosed {x : ℝ} (hx : Encloses xBox x) : Encloses byy (yOf x) := by
  have e := rat_horner_sound yCoeffs hx
  exact ⟨(Rat.cast_le.mpr (show byy.lo≤(ratHornerBox yCoeffs xBox).lo by decide +kernel)).trans e.1,
    e.2.trans (Rat.cast_le.mpr (show (ratHornerBox yCoeffs xBox).hi≤byy.hi by decide +kernel))⟩

theorem ratios_ordered {x : ℝ} (hx : Encloses xBox x) : 0<x ∧ x<yOf x ∧ yOf x<1 := by
  have X := x_enclosed hx
  have Y := y_enclosed hx
  -- The rational bounds above are transported exactly.
  exact ⟨positive X (by decide +kernel),
    (X.2.trans_lt (Rat.cast_lt.mpr (by decide +kernel : bx.hi<byy.lo))).trans_le Y.1,
    Y.2.trans_lt (by norm_num [byy])⟩

theorem db_pos {x : ℝ} (hx : Encloses xBox x) : 0<db x := by
  have e := rat_horner_sound [1,-5,5] (x_enclosed hx)
  have eq : db x=ratHorner [1,-5,5] x := by
    simp [db,ratHorner,horner]
    ring
  rw [eq]
  exact positive e (by decide +kernel)

theorem dc_neg {x : ℝ} (hx : Encloses xBox x) : dc x (yOf x)<0 := by
  have X := x_enclosed hx
  have Y := y_enclosed hx
  have h2 : Encloses (point 2) (2:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 2
  have h3 : Encloses (point 3) (3:ℝ) := by simpa only [Rat.cast_ofNat] using enclose_point (K:=ℝ) 3
  have e := enclose_add
    (enclose_sub (enclose_sub (enclose_mul h2 (enclose_mul X Y)) X)
      (enclose_mul h3 (enclose_pow Y 2))) (enclose_mul h2 Y)
  have h := negative e (by decide +kernel)
  unfold dc
  linear_combination h

private theorem quartic_pos_at {s : ℝ} {B : Box} (hs : Encloses B s)
    (hp : 0<(ratHornerBox [8,-72,168,-132,33] B).lo) : 0<quartic s := by
  have eq : quartic s=ratHorner [8,-72,168,-132,33] s := by
    simp [quartic,ratHorner,horner]
    ring
  rw [eq]
  exact positive (rat_horner_sound _ hs) hp

theorem qvals_neg {x : ℝ} (hx : Encloses xBox x) : Q0 x<0 ∧ Q0 (yOf x)<0 := by
  obtain ⟨hx0,hxy,hy1⟩ := ratios_ordered hx
  have gy := quartic_pos_at (y_enclosed hx) (by decide +kernel)
  have gx := quartic_pos_at (x_enclosed hx) (by decide +kernel)
  have hq (s : ℝ) (hs : 0<s) (ht : s<1) (hg : 0<quartic s) : Q0 s<0 := by
    rw [q_factor]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) hs) (sub_neg.mpr ht)) hg
  exact ⟨hq _ hx0 (hxy.trans hy1) gx,hq _ (hx0.trans hxy) hy1 gy⟩

theorem guarded_modes {x : ℝ} (hx : Encloses xBox x) :
    db x≠0 ∧ dc x (yOf x)≠0 ∧
    P0 x*Q0 (yOf x)-Q0 x*P0 (yOf x)≠0 ∧
    Q0 x≠0 ∧ Q0 (yOf x)≠0 ∧ yOf x-x≠0 := by
  obtain ⟨qx,qy⟩ := qvals_neg hx
  have hxy := (ratios_ordered hx).2.1
  refine ⟨(db_pos hx).ne',(dc_neg hx).ne,?_,qx.ne,qy.ne,(sub_pos.mpr hxy).ne'⟩
  rw [fit_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hxy.ne)) qx.ne) qy.ne

end RKResearch.Certified.DIRK12MidpointForward.Opening

#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.modes_fit
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.modes_unique
#print axioms RKResearch.Certified.DIRK12MidpointForward.Opening.guarded_modes
