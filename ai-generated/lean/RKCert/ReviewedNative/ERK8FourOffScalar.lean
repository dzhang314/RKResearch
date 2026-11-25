module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar endpoint for the native order-eight four-off branch

Source-only draft. The two final declarations consume exact scalar data and
make no claim that an RK tableau produces that data. No tableau hypotheses,
order conditions, chronology or rank are hidden inside the scalar certificate.
-/
namespace RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

variable {K : Type*} [Field K] [CharZero K]

/-- The factor 14 times the monic interior Lobatto cubic. -/
def lobattoNumer (u : K) : K := (2*u-1)*(7*u^2-7*u+1)

structure CleanClocks (h x z : K) : Prop where
  h_ne_x : h ≠ x
  h_ne_z : h ≠ z
  x_ne_z : x ≠ z
  root_h : lobattoNumer h = 0
  root_x : lobattoNumer x = 0
  root_z : lobattoNumer z = 0

/-- `cleanE` is `12*h` times the unscaled E in the source proof. -/
def cleanE (h x z : K) : K := 3*h^2-4*h*(x+z)+6*x*z

def cleanNumer (h x : K) : K := 4*h*x-3*h^2

structure Quad (K : Type*) where
  p0 : K
  p1 : K
  p2 : K

def Quad.eval (p : Quad K) (u : K) : K := p.p0+p.p1*u+p.p2*u^2

def shape (h x z theta k : K) : Quad K :=
  ⟨theta*x*z+2*k*h*x, -theta*(x+z)-k*(4*x+3*h), theta+5*k⟩

/-- The polynomial coefficient obstruction replacing the h=5 inverse table. -/
def gatePoly (p : Quad K) : K :=
  p.p1*(28*p.p0^2+9*p.p0*p.p2+p.p1*p.p2)-3*p.p0*(p.p2^2-21*p.p0*p.p2)

/-- The `u`-summand weight, after cancelling the factor `u` of `Q'(u)`.
Its intended use is `r=1,2,3,4`, not `r=0`. -/
def cleanWeight (p : Quad K) (u v w : K) : K := (p.eval u*(u-v)*(u-w))⁻¹

def moment (p : Quad K) (h x z : K) (r : ℕ) : K :=
  cleanWeight p h x z*h^(r-1)+cleanWeight p x h z*x^(r-1)+cleanWeight p z h x*z^(r-1)

/-- The cubic coefficient of the three actual early pure primitive profiles. -/
structure EarlyRows (C : ℕ → K) (d e h t : K) : Prop where
  r2 : d*(C 2-e*C 1)+t*h = C 2/2
  r3 : d*(C 3-e*C 2)+t*h^2 = C 3/3
  r4 : d*(C 4-e*C 3)+t*h^3 = C 4/4

/-- The clean row when physical `h` occurs before the fourth off debut. -/
structure FirstCleanRows (C : ℕ → K) (e h gain : K) : Prop where
  r2 : gain*(C 2-e*C 1) = h^2/2
  r3 : gain*(C 3-e*C 2) = h^3/3
  r4 : gain*(C 4-e*C 3) = h^4/4

private theorem root_dichotomy {u : K} (hr : lobattoNumer u = 0) :
    u = (1:K)/2 ∨ 7*u^2-7*u+1 = 0 := by
  unfold lobattoNumer at hr
  rcases mul_eq_zero.mp hr with hz | hq
  · left
    linear_combination ((1:K)/2)*hz
  · exact Or.inr hq

private theorem root_ne_zero {u : K} (hr : lobattoNumer u = 0) : u ≠ 0 := by
  intro h
  rw [h] at hr
  norm_num [lobattoNumer] at hr

private theorem quad_complement {u v : K} (hu : 7*u^2-7*u+1 = 0)
    (hv : 7*v^2-7*v+1 = 0) (hne : u ≠ v) : u+v=1 := by
  have hm : (u-v)*(u+v-1)=0 := by
    linear_combination ((1:K)/7)*hu-((1:K)/7)*hv
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne))

private theorem no_double {h x z : K} (D : CleanClocks h x z) : 4*z-2*h ≠ 0 := by
  intro H
  have hz2 : h = 2*z := by linear_combination -(1/2:K)*H
  rcases root_dichotomy D.root_z with hz | hz
  · have hh1 : h = 1 := by linear_combination hz2+2*hz
    have hh := D.root_h
    rw [hh1] at hh
    norm_num [lobattoNumer] at hh
  · rcases root_dichotomy D.root_h with hh | hh
    · have hz4 : z = (1:K)/4 := by linear_combination (1/2:K)*(hh-hz2)
      rw [hz4] at hz
      norm_num at hz
    · have hs := quad_complement hh hz D.h_ne_z
      have hz3 : z = (1:K)/3 := by linear_combination (1/3:K)*(hs-hz2)
      rw [hz3] at hz
      norm_num at hz

private def low (w : K) := (1-w)/2
private def high (w : K) := (1+w)/2

private theorem low_at (u : K) : low (1-2*u)=u := by unfold low; ring
private theorem high_at (u : K) : high (1-2*u)=1-u := by unfold high; ring
private theorem square_at {u : K} (hu : 7*u^2-7*u+1=0) :
    (1-2*u)^2=(3:K)/7 := by linear_combination ((4:K)/7)*hu

/-- The sign of w is not fixed; conjugating the three orientations gives the other three. -/
private theorem orientations {h x z : K} (D : CleanClocks h x z) :
    ∃ w : K, w^2=3/7 ∧
      ((h=low w ∧ x=1/2 ∧ z=high w) ∨
       (h=low w ∧ x=high w ∧ z=1/2) ∨
       (h=1/2 ∧ x=low w ∧ z=high w)) := by
  by_cases hh : h = (1:K)/2
  · have hx : x ≠ (1:K)/2 := fun e => D.h_ne_x (hh.trans e.symm)
    have hz : z ≠ (1:K)/2 := fun e => D.h_ne_z (hh.trans e.symm)
    have qx := (root_dichotomy D.root_x).resolve_left hx
    have qz := (root_dichotomy D.root_z).resolve_left hz
    have hs := quad_complement qx qz D.x_ne_z
    have H : z=1-x := by linear_combination hs
    exact ⟨1-2*x, square_at qx, Or.inr (Or.inr
      ⟨hh,(low_at x).symm,H.trans (high_at x).symm⟩)⟩
  · have qh := (root_dichotomy D.root_h).resolve_left hh
    by_cases hx : x = (1:K)/2
    · have hz : z ≠ (1:K)/2 := fun e => D.x_ne_z (hx.trans e.symm)
      have qz := (root_dichotomy D.root_z).resolve_left hz
      have hs := quad_complement qh qz D.h_ne_z
      have H : z=1-h := by linear_combination hs
      exact ⟨1-2*h, square_at qh, Or.inl
        ⟨(low_at h).symm,hx,H.trans (high_at h).symm⟩⟩
    · have qx := (root_dichotomy D.root_x).resolve_left hx
      have hs := quad_complement qh qx D.h_ne_x
      have hz : z = (1:K)/2 := by
        rcases root_dichotomy D.root_z with hz | qz
        · exact hz
        · have hs' := quad_complement qh qz D.h_ne_z
          have bad : x=z := by linear_combination hs-hs'
          exact (D.x_ne_z bad).elim
      have H : x=1-h := by linear_combination hs
      exact ⟨1-2*h, square_at qh, Or.inr (Or.inl
        ⟨(low_at h).symm,H.trans (high_at h).symm,hz⟩)⟩

private theorem affine_ne_zero {w a b : K} (hw : w^2=3/7)
    (gap : a^2 ≠ 3*b^2/7) : a+b*w ≠ 0 := by
  intro hz
  apply gap
  linear_combination (a-b*w)*hz+b^2*hw

/-- The finite scalar input needed by both branches; no off-node fields. -/
private structure ChartValues (h x z theta : K) : Prop where
  E_ne : cleanE h x z ≠ 0
  theta_ok : theta*cleanE h x z = cleanNumer h x
  p0_ne : (shape h x z theta 1).p0 ≠ 0
  p2_ne : (shape h x z theta 1).p2 ≠ 0
  ph_ne : (shape h x z theta 1).eval h ≠ 0
  px_ne : (shape h x z theta 1).eval x ≠ 0
  pz_ne : (shape h x z theta 1).eval z ≠ 0
  gate_ne : gatePoly (shape h x z theta 1) ≠ 0

-- GENERATED CHART VALUES
private theorem chartLCR (w : K) (hw : w^2=(3:K)/7) :
    ChartValues (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) := by
  have hE : cleanE (low w) ((1:K)/2) (high w) = (1:K)+(1:K)*w := by
    simp only [cleanE, low, high]
    linear_combination (((7:K)/4))*hw
  have htheta : (((-1:K)/2)+(1:K)*w)*cleanE (low w) ((1:K)/2) (high w) = cleanNumer (low w) ((1:K)/2) := by
    simp only [cleanE, cleanNumer, low, high]
    linear_combination (((7:K)/8)+((7:K)/4)*w)*hw
  have hp0 : (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1).p0 = ((27:K)/56)+((-3:K)/8)*w := by
    simp only [shape, low, high]
    linear_combination (((1:K)/4))*hw
  have hp1 : (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1).p1 = ((-45:K)/14)+((3:K)/4)*w := by
    simp only [shape, low, high]
    linear_combination (((-1:K)/2))*hw
  have hp2 : (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1).p2 = ((9:K)/2)+(1:K)*w := by
    simp only [shape]
    ring
  have hPh : (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1).eval (low w) = ((3:K)/28)+((-2:K)/7)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    unfold low
    linear_combination (((1:K)/4)+((1:K)/4)*w)*hw
  have hPx : (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1).eval ((1:K)/2) = (0:K)+((1:K)/4)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    ring
  have hPz : (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1).eval (high w) = ((6:K)/7)+(1:K)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    unfold high
    linear_combination ((2:K)+((1:K)/4)*w)*hw
  have hG : gatePoly (shape (low w) ((1:K)/2) (high w) (((-1:K)/2)+(1:K)*w) 1) = ((1539:K)/784)+((243:K)/112)*w := by
    simp only [gatePoly, hp0, hp1, hp2]
    linear_combination (((5319:K)/896)+((351:K)/32)*w)*hw
  refine ⟨?_,htheta,?_,?_,?_,?_,?_,?_⟩
  · rw [hE]
    apply affine_ne_zero hw
    norm_num
  · rw [hp0]
    apply affine_ne_zero hw
    norm_num
  · rw [hp2]
    apply affine_ne_zero hw
    norm_num
  · rw [hPh]
    apply affine_ne_zero hw
    norm_num
  · rw [hPx]
    apply affine_ne_zero hw
    norm_num
  · rw [hPz]
    apply affine_ne_zero hw
    norm_num
  · rw [hG]
    apply affine_ne_zero hw
    norm_num

private theorem chartLRC (w : K) (hw : w^2=(3:K)/7) :
    ChartValues (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) := by
  have hE : cleanE (low w) (high w) ((1:K)/2) = (1:K)+(1:K)*w := by
    simp only [cleanE, low, high]
    linear_combination (((7:K)/4))*hw
  have htheta : ((-2:K)+((7:K)/2)*w)*cleanE (low w) (high w) ((1:K)/2) = cleanNumer (low w) (high w) := by
    simp only [cleanE, cleanNumer, low, high]
    linear_combination (((7:K)/4)+((49:K)/8)*w)*hw
  have hp0 : (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1).p0 = ((9:K)/56)+((3:K)/8)*w := by
    simp only [shape, low, high]
    linear_combination (((3:K)/8))*hw
  have hp1 : (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1).p1 = ((-9:K)/4)+(-3:K)*w := by
    simp only [shape, low, high]
    linear_combination (((-7:K)/4))*hw
  have hp2 : (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1).p2 = (3:K)+((7:K)/2)*w := by
    simp only [shape]
    ring
  have hPh : (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1).eval (low w) = (0:K)+((-1:K)/4)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    unfold low
    linear_combination (((1:K)/2)+((7:K)/8)*w)*hw
  have hPx : (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1).eval (high w) = ((3:K)/14)+((1:K)/2)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    unfold high
    linear_combination ((1:K)+((7:K)/8)*w)*hw
  have hPz : (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1).eval ((1:K)/2) = ((-3:K)/14)+((-1:K)/4)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    ring
  have hG : gatePoly (shape (low w) (high w) ((1:K)/2) ((-2:K)+((7:K)/2)*w) 1) = ((405:K)/56)+((81:K)/8)*w := by
    simp only [gatePoly, hp0, hp1, hp2]
    linear_combination (((27:K)/4)+((189:K)/128)*w)*hw
  refine ⟨?_,htheta,?_,?_,?_,?_,?_,?_⟩
  · rw [hE]
    apply affine_ne_zero hw
    norm_num
  · rw [hp0]
    apply affine_ne_zero hw
    norm_num
  · rw [hp2]
    apply affine_ne_zero hw
    norm_num
  · rw [hPh]
    apply affine_ne_zero hw
    norm_num
  · rw [hPx]
    apply affine_ne_zero hw
    norm_num
  · rw [hPz]
    apply affine_ne_zero hw
    norm_num
  · rw [hG]
    apply affine_ne_zero hw
    norm_num

private theorem chartCLR (w : K) (hw : w^2=(3:K)/7) :
    ChartValues ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) := by
  have hE : cleanE ((1:K)/2) (low w) (high w) = ((-11:K)/28)+(0:K)*w := by
    simp only [cleanE, low, high]
    linear_combination (((-3:K)/2))*hw
  have htheta : (((-7:K)/11)+((28:K)/11)*w)*cleanE ((1:K)/2) (low w) (high w) = cleanNumer ((1:K)/2) (low w) := by
    simp only [cleanE, cleanNumer, low, high]
    linear_combination (((21:K)/22)+((-42:K)/11)*w)*hw
  have hp0 : (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1).p0 = ((9:K)/22)+((-3:K)/22)*w := by
    simp only [shape, low, high]
    linear_combination (((7:K)/44)+((-7:K)/11)*w)*hw
  have hp1 : (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1).p1 = ((-63:K)/22)+((-6:K)/11)*w := by
    simp only [shape, low, high]
    ring
  have hp2 : (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1).p2 = ((48:K)/11)+((28:K)/11)*w := by
    simp only [shape]
    ring
  have hPh : (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1).eval ((1:K)/2) = ((3:K)/44)+((5:K)/22)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    ring
  have hPx : (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1).eval (low w) = ((3:K)/28)+((-1:K)/4)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    unfold low
    linear_combination (((1:K)/11)+((7:K)/11)*w)*hw
  have hPz : (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1).eval (high w) = ((27:K)/28)+((5:K)/4)*w := by
    unfold Quad.eval
    rw [hp0,hp1,hp2]
    unfold high
    linear_combination (((23:K)/11)+((7:K)/11)*w)*hw
  have hG : gatePoly (shape ((1:K)/2) (low w) (high w) (((-7:K)/11)+((28:K)/11)*w) 1) = ((810:K)/847)+((81:K)/121)*w := by
    simp only [gatePoly, hp0, hp1, hp2]
    linear_combination (((1107:K)/242)+((945:K)/121)*w)*hw
  refine ⟨?_,htheta,?_,?_,?_,?_,?_,?_⟩
  · rw [hE]
    apply affine_ne_zero hw
    norm_num
  · rw [hp0]
    apply affine_ne_zero hw
    norm_num
  · rw [hp2]
    apply affine_ne_zero hw
    norm_num
  · rw [hPh]
    apply affine_ne_zero hw
    norm_num
  · rw [hPx]
    apply affine_ne_zero hw
    norm_num
  · rw [hPz]
    apply affine_ne_zero hw
    norm_num
  · rw [hG]
    apply affine_ne_zero hw
    norm_num

private theorem chart_choice {h x z : K} (D : CleanClocks h x z) :
    ∃ theta, ChartValues h x z theta := by
  obtain ⟨w,hw,hor⟩ := orientations D
  rcases hor with ⟨hh,hx,hz⟩ | ⟨hh,hx,hz⟩ | ⟨hh,hx,hz⟩
  · rw [hh,hx,hz]
    exact ⟨_,chartLCR w hw⟩
  · rw [hh,hx,hz]
    exact ⟨_,chartLRC w hw⟩
  · rw [hh,hx,hz]
    exact ⟨_,chartCLR w hw⟩

/-- This nonvanishing is usable upstream before the producer has obtained `k ≠ 0`. -/
theorem cleanE_ne_zero {h x z : K} (D : CleanClocks h x z) : cleanE h x z ≠ 0 := by
  obtain ⟨_,T⟩ := chart_choice D
  exact T.E_ne

private theorem symmetric_clocks {h x z : K} (D : CleanClocks h x z) :
    h+x+z=(3:K)/2 ∧ h*x+h*z+x*z=(9:K)/14 ∧ h*x*z=(1:K)/14 := by
  obtain ⟨w,hw,hor⟩ := orientations D
  rcases hor with ⟨hh,hx,hz⟩ | ⟨hh,hx,hz⟩ | ⟨hh,hx,hz⟩ <;>
    rw [hh,hx,hz] <;>
    simp only [low,high] <;>
    exact ⟨by ring, by linear_combination -(1/4:K)*hw,
      by linear_combination -(1/8:K)*hw⟩

structure ShapeNonzero (p : Quad K) (h x z : K) : Prop where
  p0_ne : p.p0 ≠ 0
  p2_ne : p.p2 ≠ 0
  ph_ne : p.eval h ≠ 0
  px_ne : p.eval x ≠ 0
  pz_ne : p.eval z ≠ 0
  gate_ne : gatePoly p ≠ 0

private def qscale (k : K) (p : Quad K) : Quad K := ⟨k*p.p0,k*p.p1,k*p.p2⟩

private theorem shape_scale (h x z k theta : K) :
    shape h x z (k*theta) k = qscale k (shape h x z theta 1) := by
  simp only [shape,qscale]
  congr 1 <;> ring

private theorem eval_scale (k : K) (p : Quad K) (u : K) :
    (qscale k p).eval u = k*(p.eval u) := by
  simp only [Quad.eval,qscale]
  ring

private theorem gate_scale (k : K) (p : Quad K) :
    gatePoly (qscale k p)=k^3*gatePoly p := by
  simp only [gatePoly,qscale]
  ring

theorem shape_nonzero_of_clean {h x z theta k : K} (D : CleanClocks h x z) (hk : k ≠ 0)
    (eq : theta*cleanE h x z = k*cleanNumer h x) :
    ShapeNonzero (shape h x z theta k) h x z := by
  obtain ⟨theta0,T⟩ := chart_choice D
  have Htheta : theta=k*theta0 := by
    apply mul_right_cancel₀ T.E_ne
    linear_combination eq-k*T.theta_ok
  rw [Htheta,shape_scale]
  refine ⟨mul_ne_zero hk T.p0_ne, mul_ne_zero hk T.p2_ne, ?_, ?_, ?_, ?_⟩
  · rw [eval_scale]; exact mul_ne_zero hk T.ph_ne
  · rw [eval_scale]; exact mul_ne_zero hk T.px_ne
  · rw [eval_scale]; exact mul_ne_zero hk T.pz_ne
  · rw [gate_scale]; exact mul_ne_zero (pow_ne_zero 3 hk) T.gate_ne

/-- Every subsequent residue identity is a three-term linear test. -/
private theorem moment_test (p : Quad K) (h x z a0 a1 a2 a3 : K) :
    a0*moment p h x z 1+a1*moment p h x z 2+a2*moment p h x z 3+a3*moment p h x z 4 =
    cleanWeight p h x z*(a0+a1*h+a2*h^2+a3*h^3)+
    cleanWeight p x h z*(a0+a1*x+a2*x^2+a3*x^3)+
    cleanWeight p z h x*(a0+a1*z+a2*z^2+a3*z^3) := by
  simp only [moment]
  norm_num <;> ring

private theorem weight_cancel (p : Quad K) {u v w : K} (hp : p.eval u ≠ 0)
    (huv : u ≠ v) (huw : u ≠ w) :
    cleanWeight p u v w*((u-v)*(u-w))=(p.eval u)⁻¹ := by
  unfold cleanWeight
  field_simp [hp,sub_ne_zero.mpr huv,sub_ne_zero.mpr huw] <;> ring

private theorem weight_rec (p : Quad K) {u v w : K} (hp : p.eval u ≠ 0)
    (huv : u ≠ v) (huw : u ≠ w) :
    cleanWeight p u v w*p.eval u=((u-v)*(u-w))⁻¹ := by
  unfold cleanWeight
  field_simp [hp,sub_ne_zero.mpr huv,sub_ne_zero.mpr huw] <;> ring

private theorem barycentric1 {h x z : K} (D : CleanClocks h x z) :
    ((h-x)*(h-z))⁻¹+((x-h)*(x-z))⁻¹+((z-h)*(z-x))⁻¹=0 := by
  field_simp [sub_ne_zero.mpr D.h_ne_x,sub_ne_zero.mpr D.h_ne_z,sub_ne_zero.mpr D.x_ne_z,
    sub_ne_zero.mpr D.h_ne_x.symm,sub_ne_zero.mpr D.h_ne_z.symm,
    sub_ne_zero.mpr D.x_ne_z.symm] <;> ring

private theorem barycentricX {h x z : K} (D : CleanClocks h x z) :
    ((h-x)*(h-z))⁻¹*h+((x-h)*(x-z))⁻¹*x+((z-h)*(z-x))⁻¹*z=0 := by
  field_simp [sub_ne_zero.mpr D.h_ne_x,sub_ne_zero.mpr D.h_ne_z,sub_ne_zero.mpr D.x_ne_z,
    sub_ne_zero.mpr D.h_ne_x.symm,sub_ne_zero.mpr D.h_ne_z.symm,
    sub_ne_zero.mpr D.x_ne_z.symm] <;> ring

private theorem recur1 {p : Quad K} {h x z : K} (D : CleanClocks h x z)
    (N : ShapeNonzero p h x z) :
    p.p0*moment p h x z 1+p.p1*moment p h x z 2+p.p2*moment p h x z 3=0 := by
  have E := moment_test p h x z p.p0 p.p1 p.p2 0
  simp only [zero_mul,add_zero] at E
  change _ = cleanWeight p h x z*p.eval h+cleanWeight p x h z*p.eval x+
    cleanWeight p z h x*p.eval z at E
  rw [E, weight_rec p N.ph_ne D.h_ne_x D.h_ne_z,
    weight_rec p N.px_ne D.h_ne_x.symm D.x_ne_z,
    weight_rec p N.pz_ne D.h_ne_z.symm D.x_ne_z.symm]
  exact barycentric1 D

private theorem recur2 {p : Quad K} {h x z : K} (D : CleanClocks h x z)
    (N : ShapeNonzero p h x z) :
    p.p0*moment p h x z 2+p.p1*moment p h x z 3+p.p2*moment p h x z 4=0 := by
  have E := moment_test p h x z 0 p.p0 p.p1 p.p2
  simp only [zero_mul,zero_add] at E
  have ev (u : K) : p.p0*u+p.p1*u^2+p.p2*u^3=p.eval u*u := by
    unfold Quad.eval
    ring
  rw [E,ev h,ev x,ev z,
    ←mul_assoc (cleanWeight p h x z) (p.eval h) h,
    ←mul_assoc (cleanWeight p x h z) (p.eval x) x,
    ←mul_assoc (cleanWeight p z h x) (p.eval z) z,
    weight_rec p N.ph_ne D.h_ne_x D.h_ne_z,
    weight_rec p N.px_ne D.h_ne_x.symm D.x_ne_z,
    weight_rec p N.pz_ne D.h_ne_z.symm D.x_ne_z.symm]
  exact barycentricX D

private theorem recurCubic {p : Quad K} {h x z : K} (D : CleanClocks h x z) :
    14*moment p h x z 4-21*moment p h x z 3+9*moment p h x z 2-moment p h x z 1=0 := by
  have ci {u : K} (H : lobattoNumer u=0) : -1+9*u+(-21)*u^2+14*u^3=0 := by
    unfold lobattoNumer at H
    linear_combination H
  have E := moment_test p h x z (-1) 9 (-21) 14
  rw [ci D.root_h,ci D.root_x,ci D.root_z] at E
  simp only [mul_zero,add_zero] at E
  linear_combination E

private def trace (C : ℕ → K) (v w : K) : K := C 3-(v+w)*C 2+v*w*C 1

private theorem trace_test (p : Quad K) (h x z v w : K) :
    trace (moment p h x z) v w = cleanWeight p h x z*((h-v)*(h-w))+
      cleanWeight p x h z*((x-v)*(x-w))+cleanWeight p z h x*((z-v)*(z-w)) := by
  simp only [trace,moment]
  norm_num <;> ring

private theorem traceH {p : Quad K} {h x z : K} (D : CleanClocks h x z)
    (N : ShapeNonzero p h x z) : trace (moment p h x z) x z ≠ 0 := by
  rw [trace_test]
  simp only [sub_self,mul_zero,zero_mul,add_zero]
  rw [weight_cancel p N.ph_ne D.h_ne_x D.h_ne_z]
  exact inv_ne_zero N.ph_ne

private theorem traceX {p : Quad K} {h x z : K} (D : CleanClocks h x z)
    (N : ShapeNonzero p h x z) : trace (moment p h x z) h z ≠ 0 := by
  rw [trace_test]
  simp only [sub_self,mul_zero,zero_mul,zero_add,add_zero]
  rw [weight_cancel p N.px_ne D.h_ne_x.symm D.x_ne_z]
  exact inv_ne_zero N.px_ne

/-- h5 rank factor, using only a rank-one specialization and two residue traces.
No division by C1 and no quotient-field construction is needed. -/
private theorem hankel_ne {p : Quad K} {h x z : K} (D : CleanClocks h x z)
    (N : ShapeNonzero p h x z) :
    moment p h x z 1*moment p h x z 3-(moment p h x z 2)^2≠0 := by
  let C := moment p h x z
  change C 1*C 3-(C 2)^2 ≠ 0
  intro delta
  have R1 : p.p0*C 1+p.p1*C 2+p.p2*C 3=0 := recur1 D N
  have R2 : p.p0*C 2+p.p1*C 3+p.p2*C 4=0 := recur2 D N
  have R3 : 14*C 4-21*C 3+9*C 2-C 1=0 := recurCubic (p:=p) D
  have det1 : C 1*C 4-C 2*C 3=0 := by
    apply (mul_eq_zero.mp (_ : p.p2*(C 1*C 4-C 2*C 3)=0)).resolve_left N.p2_ne
    linear_combination C 1*R2-C 2*R1-p.p1*delta
  have pow3 : (C 1)^2*C 4=(C 2)^3 := by
    linear_combination C 1*det1+C 2*delta
  obtain ⟨s1,s2,s3⟩ := symmetric_clocks D
  have factor : (C 2-h*C 1)*(C 2-x*C 1)*(C 2-z*C 1)=0 := by
    have expand : (C 2-h*C 1)*(C 2-x*C 1)*(C 2-z*C 1)=
        (C 2)^3-(h+x+z)*C 1*(C 2)^2+(h*x+h*z+x*z)*(C 1)^2*C 2-h*x*z*(C 1)^3 := by ring
    rw [expand,s1,s2,s3]
    linear_combination (1/14:K)*(C 1)^2*R3-pow3+(3/2:K)*C 1*delta
  have TH : trace C x z ≠ 0 := traceH D N
  have TX : trace C h z ≠ 0 := traceX D N
  have z1 : C 1=0 := by
    rcases mul_eq_zero.mp factor with ff | ff
    · rcases mul_eq_zero.mp ff with fH | fX
      · have eqX : C 1*trace C h z=0 := by
          unfold trace
          linear_combination delta+(C 2-z*C 1)*fH
        exact (mul_eq_zero.mp eqX).resolve_right TX
      · have eqH : C 1*trace C x z=0 := by
          unfold trace
          linear_combination delta+(C 2-z*C 1)*fX
        exact (mul_eq_zero.mp eqH).resolve_right TH
    · have eqH : C 1*trace C x z=0 := by
        unfold trace
        linear_combination delta+(C 2-x*C 1)*ff
      exact (mul_eq_zero.mp eqH).resolve_right TH
  have zz2 : (C 2)^2=0 := by linear_combination C 3*z1-delta
  have z2 : C 2=0 := eq_zero_of_pow_eq_zero zz2
  have p3 : p.p2*C 3=0 := by simpa only [z1,z2,mul_zero,zero_add] using R1
  have z3 : C 3=0 := (mul_eq_zero.mp p3).resolve_left N.p2_ne
  exact TH (by simp only [trace,z1,z2,z3,mul_zero,sub_zero,zero_add])

/-- h5 remaining factor, by a 2-by-2 polynomial coefficient resultant. -/
private theorem cleared_last_ne {p : Quad K} {h x z : K} (D : CleanClocks h x z)
    (N : ShapeNonzero p h x z) :
    p.p2*moment p h x z 4-2*p.p0*moment p h x z 2≠0 := by
  let C := moment p h x z
  change p.p2*C 4-2*p.p0*C 2 ≠ 0
  intro H
  have R1 : p.p0*C 1+p.p1*C 2+p.p2*C 3=0 := recur1 D N
  have R2 : p.p0*C 2+p.p1*C 3+p.p2*C 4=0 := recur2 D N
  have R3 : 14*C 4-21*C 3+9*C 2-C 1=0 := recurCubic (p:=p) D
  let B2 := 28*p.p0^2+9*p.p0*p.p2+p.p1*p.p2
  let B3 := p.p2^2-21*p.p0*p.p2
  have A : 3*p.p0*C 2+p.p1*C 3=0 := by linear_combination R2-H
  have B : B2*C 2+B3*C 3=0 := by
    dsimp only [B2,B3]
    linear_combination p.p0*p.p2*R3+p.p2*R1-14*p.p0*H
  have j2 : gatePoly p*C 2=0 := by
    dsimp only [B2,B3] at B
    unfold gatePoly
    linear_combination p.p1*B-(p.p2^2-21*p.p0*p.p2)*A
  have j3 : gatePoly p*C 3=0 := by
    dsimp only [B2,B3] at B
    unfold gatePoly
    linear_combination (28*p.p0^2+9*p.p0*p.p2+p.p1*p.p2)*A-3*p.p0*B
  have z2 := (mul_eq_zero.mp j2).resolve_left N.gate_ne
  have z3 := (mul_eq_zero.mp j3).resolve_left N.gate_ne
  have j1 : p.p0*C 1=0 := by simpa only [z2,z3,mul_zero,add_zero] using R1
  have z1 := (mul_eq_zero.mp j1).resolve_left N.p0_ne
  have TH : trace C x z ≠ 0 := traceH D N
  exact TH (by simp only [trace,z1,z2,z3,mul_zero,sub_zero,zero_add])

/-- Equality (5), with neither division by h nor division by the `gain`. -/
theorem indexFour_difference_zero {C : ℕ → K} {d e h t gain : K}
    (hh : h ≠ 0) (off : EarlyRows C d e h t) (clean : FirstCleanRows C e h gain) :
    C 4-2*h*C 3+h^2*C 2=0 := by
  obtain ⟨O2,O3,O4⟩ := off
  obtain ⟨H2,H3,H4⟩ := clean
  have gain_ne : gain ≠ 0 := by
    intro zero
    have sq : h^2=0 := by linear_combination -2*H2+2*(C 2-e*C 1)*zero
    exact pow_ne_zero 2 hh sq
  have E2 : d*h^2+2*gain*t*h=gain*C 2 := by linear_combination 2*gain*O2-2*d*H2
  have E3 : d*h^3+3*gain*t*h^2=gain*C 3 := by linear_combination 3*gain*O3-3*d*H3
  have E4 : d*h^4+4*gain*t*h^3=gain*C 4 := by linear_combination 4*gain*O4-4*d*H4
  have G : gain*(C 4-2*h*C 3+h^2*C 2)=0 := by linear_combination -E4+2*h*E3-h^2*E2
  exact (mul_eq_zero.mp G).resolve_left gain_ne

/-- Cleared form of (6) follows directly from the three early rows. -/
theorem indexFive_product_zero {C : ℕ → K} {d e h : K} {p : Quad K}
    (off : EarlyRows C d e h 0)
    (R1 : p.p0*C 1+p.p1*C 2+p.p2*C 3=0)
    (R2 : p.p0*C 2+p.p1*C 3+p.p2*C 4=0) :
    (C 1*C 3-(C 2)^2)*(p.p2*C 4-2*p.p0*C 2)=0 := by
  obtain ⟨O2,O3,O4⟩ := off
  simp only [zero_mul,add_zero] at O2 O3 O4
  have det : C 1*C 3*C 4-3*(C 2)^2*C 4+2*C 2*(C 3)^2=0 := by
    linear_combination -12*((C 3)^2-C 2*C 4)*O2-12*(C 1*C 4-C 2*C 3)*O3-
      12*((C 2)^2-C 1*C 3)*O4
  have R : p.p2*(C 2*C 4-(C 3)^2)-p.p0*(C 1*C 3-(C 2)^2)=0 := by
    linear_combination C 2*R2-C 3*R1
  linear_combination p.p2*det+2*C 2*R

private theorem residue_h4 {h x z theta k : K} (D : CleanClocks h x z) (hk : k ≠ 0)
    (N : ShapeNonzero (shape h x z theta k) h x z) :
    let p := shape h x z theta k
    let C := moment p h x z
    C 4-2*h*C 3+h^2*C 2=-(4*z-2*h)/(p.eval z) := by
  dsimp only
  let p := shape h x z theta k
  let C := moment p h x z
  change C 4-2*h*C 3+h^2*C 2=-(4*z-2*h)/(p.eval z)
  have E := moment_test p h x z 0 (h^2) (-2*h) 1
  simp only [zero_mul,zero_add,one_mul] at E
  have f (u : K) : h^2*u+(-2*h)*u^2+u^3=u*(u-h)^2 := by ring
  rw [f h,f x,f z] at E
  simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add] at E
  have px : p.eval x=k*x*(x-h) := by dsimp only [p,shape,Quad.eval]; ring
  have pz : p.eval z=k*(z*(z-h)+(4*z-2*h)*(z-x)) := by
    dsimp only [p,shape,Quad.eval]
    ring
  have cancelX : cleanWeight p x h z*(x*(x-h)^2)=(k*(x-z))⁻¹ := by
    unfold cleanWeight
    rw [px]
    field_simp [hk,root_ne_zero D.root_x,sub_ne_zero.mpr D.h_ne_x.symm,
      sub_ne_zero.mpr D.x_ne_z] <;> ring
  have cancelZ : cleanWeight p z h x*(z*(z-h)^2)=z*(z-h)/(p.eval z*(z-x)) := by
    unfold cleanWeight
    field_simp [N.pz_ne,sub_ne_zero.mpr D.h_ne_z.symm,sub_ne_zero.mpr D.x_ne_z.symm] <;> ring
  have sum : (k*(x-z))⁻¹+z*(z-h)/(p.eval z*(z-x))=-(4*z-2*h)/(p.eval z) := by
    have clear (q : K) (hq : q ≠ 0)
        (pq : q=k*(z*(z-h)+(4*z-2*h)*(z-x))) :
        (k*(x-z))⁻¹+z*(z-h)/(q*(z-x))=-(4*z-2*h)/q := by
      field_simp [hk,hq,sub_ne_zero.mpr D.x_ne_z,sub_ne_zero.mpr D.x_ne_z.symm]
      rw [pq]
      ring
    exact clear (p.eval z) N.pz_ne pz
  rw [cancelX,cancelZ] at E
  linear_combination E+sum

/-- Final scalar endpoint when the first nonzero clean row is physical 4. -/
theorem firstCleanAt4_contradiction {h x z theta k d e t gain : K}
    (D : CleanClocks h x z) (hk : k ≠ 0)
    (hs : theta*cleanE h x z = k*cleanNumer h x)
    (off : EarlyRows (moment (shape h x z theta k) h x z) d e h t)
    (clean : FirstCleanRows (moment (shape h x z theta k) h x z) e h gain) : False := by
  have N := shape_nonzero_of_clean D hk hs
  have z0 := indexFour_difference_zero (root_ne_zero D.root_h) off clean
  have val := residue_h4 D hk N
  exact (div_ne_zero (neg_ne_zero.mpr (no_double D)) N.pz_ne) (val.symm.trans z0)

/-- Final scalar endpoint when the first nonzero clean row is physical 5.
The only early clean tap is absent, hence the literal zero argument. -/
theorem firstCleanAt5_contradiction {h x z theta k d e : K}
    (D : CleanClocks h x z) (hk : k ≠ 0)
    (hs : theta*cleanE h x z = k*cleanNumer h x)
    (off : EarlyRows (moment (shape h x z theta k) h x z) d e h 0) : False := by
  have N := shape_nonzero_of_clean D hk hs
  exact (mul_ne_zero (hankel_ne D N) (cleared_last_ne D N))
    (indexFive_product_zero off (recur1 D N) (recur2 D N))

end RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
