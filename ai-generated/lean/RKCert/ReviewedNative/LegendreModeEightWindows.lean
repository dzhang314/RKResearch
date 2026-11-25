module
public import RKCert.ReviewedNative.LegendreModeEight
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.LegendreModeEightWindows
open Polynomial
open RKCert.ReviewedNative.LegendreModeEight
open RKCert.ReviewedNative.LegendreEnergy

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def g (x : K) : K := 715*x^3-1001*x^2+385*x-35
private def q (x y : K) : K := 715*(x^2+x*y+y^2)-1001*(x+y)+385
private abbrev a : K := 1/9
private abbrev b : K := 4/25
private abbrev c : K := 9/25
private abbrev d : K := 9/16
private abbrev e : K := 25/36
private abbrev f : K := 81/100

private theorem difference (x y : K) : g y-g x=(y-x)*q x y := by
  dsimp only [g,q]
  ring

private theorem pos_mix {x y u v : K} (hx : 0≤x) (hy : 0≤y) (hs : 0<x+y)
    (hu : 0<u) (hv : 0<v) : 0<x*u+y*v := by
  rcases hx.eq_or_lt with z | z
  · have h : 0<y := by linarith only [hs,z]
    simpa [←z] using mul_pos h hv
  · exact add_pos_of_pos_of_nonneg (mul_pos z hu) (mul_nonneg hy hv.le)

private theorem neg_mix {x y u v : K} (hx : 0≤x) (hy : 0≤y) (hs : 0<x+y)
    (hu : u<0) (hv : v<0) : x*u+y*v<0 := by
  have h := pos_mix hx hy hs (neg_pos.mpr hu) (neg_pos.mpr hv)
  linarith only [h]

private theorem quad_neg_between {l r x A B C : K} (lr : l<r) (lx : l≤x) (xr : x≤r)
    (A0 : 0≤A) (vl : A*l^2+B*l+C<0) (vr : A*r^2+B*r+C<0) :
    A*x^2+B*x+C<0 := by
  have sec :
      (r-l)*(A*x^2+B*x+C)-((r-x)*(A*l^2+B*l+C)+(x-l)*(A*r^2+B*r+C)) =
        (r-l)*A*(x-l)*(x-r) := by ring
  have s : (r-l)*A*(x-l)*(x-r)≤0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr lr.le) A0) (sub_nonneg.mpr lx))
      (sub_nonpos.mpr xr)
  have vs := neg_mix (sub_nonneg.mpr xr) (sub_nonneg.mpr lx)
    (by linarith only [lr] : 0<(r-x)+(x-l)) vl vr
  have h : (r-l)*(A*x^2+B*x+C)<0 := by linarith only [sec,s,vs]
  by_contra! bad
  exact (not_lt_of_ge (mul_nonneg (sub_nonneg.mpr lr.le) bad)) h

private theorem lo_increasing {x y : K} (x0 : 0≤x) (xy : x<y) (yb : y≤(b:K)) :
    g x<g y := by
  have y0 := x0.trans xy.le
  have xb := xy.le.trans yb
  have qpos : 0<q x y := by
    dsimp only [q]
    nlinarith only [sq_nonneg x,sq_nonneg y,mul_nonneg x0 y0,xb,yb,
      show (385:K)-2002*b>0 by norm_num]
  have h := mul_pos (sub_pos.mpr xy) qpos
  rw [←difference] at h
  exact sub_pos.mp h

private theorem middle_decreasing {x y : K} (cx : (c:K)≤x) (xy : x<y) (yd : y≤(d:K)) :
    g y<g x := by
  have cd : (c:K)<d := by norm_num
  have cy := cx.trans xy.le
  have xd := xy.le.trans yd
  have qc : q c y<0 := by
    have h := quad_neg_between (K:=K) (x:=y) (A:=715) (B:=715*c-1001)
      (C:=715*c^2-1001*c+385) cd cy yd (by norm_num)
      (by norm_num) (by norm_num)
    convert h using 1 <;> dsimp only [q] <;> ring
  have qd : q d y<0 := by
    have h := quad_neg_between (K:=K) (x:=y) (A:=715) (B:=715*d-1001)
      (C:=715*d^2-1001*d+385) cd cy yd (by norm_num)
      (by norm_num) (by norm_num)
    dsimp only [q]
    linarith only [h]
  have qx : q x y<0 := by
    have eq (u : K) : q u y=715*u^2+(715*y-1001)*u+(715*y^2-1001*y+385) := by
      dsimp only [q];ring
    rw [eq] at qc qd ⊢
    exact quad_neg_between cd cx xd (by norm_num) qc qd
  have h := mul_neg_of_pos_of_neg (sub_pos.mpr xy) qx
  rw [←difference] at h
  exact sub_neg.mp h

private theorem hi_increasing {x y : K} (ex : (e:K)≤x) (xy : x<y) :
    g x<g y := by
  have ey := ex.trans xy.le
  let u := x-e
  let v := y-e
  have u0 : 0≤u := sub_nonneg.mpr ex
  have v0 : 0≤v := sub_nonneg.mpr ey
  have form : q x y=q e e+(2145*e-1001)*(u+v)+715*(u^2+u*v+v^2) := by
    dsimp only [q,u,v];ring
  have base : 0<q (e:K) e := by norm_num [q]
  have coef : 0≤(2145:K)*e-1001 := by norm_num
  have qpos : 0<q x y := by
    rw [form]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg base (mul_nonneg coef (add_nonneg u0 v0)))
      (mul_nonneg (by norm_num) (add_nonneg (add_nonneg (sq_nonneg u) (mul_nonneg u0 v0))
        (sq_nonneg v)))
  have h := mul_pos (sub_pos.mpr xy) qpos
  rw [←difference] at h
  exact sub_pos.mp h

private theorem cubic_secant (l r x : K) :
    (r-l)*g x-((r-x)*g l+(x-l)*g r)=
      (r-l)*(x-l)*(x-r)*(715*(x+l+r)-1001) := by
  dsimp only [g];ring

private theorem first_gap {x : K} (bx : (b:K)≤x) (xc : x≤(c:K)) : 0<g x := by
  have base := pos_mix (sub_nonneg.mpr xc) (sub_nonneg.mpr bx)
    (by linarith only [show (b:K)<c by norm_num [b,c]] : 0<(c:K)-x+(x-b))
    (by norm_num [g] : 0<g (b:K)) (by norm_num [g] : 0<g (c:K))
  have k : 715*(x+b+c)-1001≤0 := by
    linarith only [xc,show (715:K)*(c+b+c)-1001<0 by norm_num]
  -- The last product is nonnegative because both displayed factors are nonpositive.
  have shape' :
      (c-b)*(x-b)*(x-c)*(715*(x+b+c)-1001)≥0 :=
    mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num : 0≤(c:K)-b) (sub_nonneg.mpr bx)) (sub_nonpos.mpr xc)) k
  have h : 0<((c:K)-b)*g x := by
    linarith only [base,cubic_secant (b:K) c x,shape']
  exact (mul_pos_iff_of_pos_left (by norm_num : 0<(c:K)-b)).mp h

private theorem second_gap {x : K} (dx : (d:K)≤x) (xe : x≤(e:K)) : g x<0 := by
  have base := neg_mix (sub_nonneg.mpr xe) (sub_nonneg.mpr dx)
    (by linarith only [show (d:K)<e by norm_num [d,e]] : 0<(e:K)-x+(x-d))
    (by norm_num [g] : g (d:K)<0) (by norm_num [g] : g (e:K)<0)
  have k : 0≤715*(x+d+e)-1001 := by
    linarith only [dx,show (0:K)<715*(d+d+e)-1001 by norm_num]
  have shape :
      (e-d)*(x-d)*(x-e)*(715*(x+d+e)-1001)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num : 0≤(e:K)-d) (sub_nonneg.mpr dx)) (sub_nonpos.mpr xe)) k
  have h : ((e:K)-d)*g x<0 := by
    linarith only [base,cubic_secant (d:K) e x,shape]
  by_contra! bad
  exact (not_lt_of_ge (mul_nonneg (by norm_num : 0 ≤ (e : K) - d) bad)) h

private theorem squared_windows {x : K} (x0 : 0≤x) (g0 : g x=0) :
    a<x ∧ x<b ∨ c<x ∧ x<d ∨ e<x ∧ x<f := by
  have ax : a<x := by
    by_contra! bad
    have h : g x≤g (a:K) := by
      rcases bad.lt_or_eq with h | h
      · exact (lo_increasing x0 h (by norm_num : (a:K)≤b)).le
      · rw [h]
    rw [g0] at h
    linarith only [h,show g (a:K)<0 by norm_num [g]]
  have xf : x<f := by
    by_contra! bad
    have h : g (f:K)≤g x := by
      rcases bad.lt_or_eq with h | h
      · exact (hi_increasing (by norm_num : (e:K)≤f) h).le
      · rw [←h]
    rw [g0] at h
    linarith only [h,show 0<g (f:K) by norm_num [g]]
  by_cases bx : x<b
  · exact Or.inl ⟨ax,bx⟩
  have cx : c<x := by
    by_contra! h
    exact (first_gap (le_of_not_gt bx) h).ne' g0
  by_cases dx : x<d
  · exact Or.inr (Or.inl ⟨cx,dx⟩)
  have ex : e<x := by
    by_contra! h
    exact (second_gap (le_of_not_gt dx) h).ne g0
  exact Or.inr (Or.inr ⟨ex,xf⟩)

private theorem factor_prime (x : K) : (polynomial K).derivative.eval x=(9/16)*x*g (x^2) := by
  rw [prime_value]
  dsimp only [g]
  ring

private theorem g_of_positive_critical {x : K} (x0 : 0<x)
    (dx : (polynomial K).derivative.eval x=0) : g (x^2)=0 := by
  rw [factor_prime] at dx
  exact (mul_eq_zero.mp dx).resolve_left (mul_ne_zero (by norm_num) x0.ne')

theorem positive_critical_windows {x : K} (x0 : 0<x)
    (dx : (polynomial K).derivative.eval x=0) :
    1/3<x ∧ x<2/5 ∨ 3/5<x ∧ x<3/4 ∨ 5/6<x ∧ x<9/10 := by
  have W := squared_windows (sq_nonneg x) (g_of_positive_critical x0 dx)
  have cv {l r : K} (l0 : 0≤l) (r0 : 0≤r) (h : l^2<x^2 ∧ x^2<r^2) :
      l<x ∧ x<r := by
    constructor
    · by_contra! bad
      nlinarith only [h.1,mul_nonneg (sub_nonneg.mpr bad) (add_nonneg x0.le l0)]
    · by_contra! bad
      nlinarith only [h.2,mul_nonneg (sub_nonneg.mpr bad) (add_nonneg x0.le r0)]
  rcases W with W | W | W
  · exact Or.inl (cv (by norm_num) (by norm_num) (by norm_num at W ⊢;exact W))
  · exact Or.inr (Or.inl (cv (by norm_num) (by norm_num) (by norm_num at W ⊢;exact W)))
  · exact Or.inr (Or.inr (cv (by norm_num) (by norm_num) (by norm_num at W ⊢;exact W)))


private def window (i : Fin 3) (x : K) : Prop :=
  if i=0 then a<x ∧ x<b else if i=1 then c<x ∧ x<d else e<x ∧ x<f

private theorem locate {x : K} (x0 : 0≤x) (g0 : g x=0) : ∃ i : Fin 3, window i x := by
  rcases squared_windows x0 g0 with h | h | h
  · exact ⟨0,by simpa [window] using h⟩
  · exact ⟨1,by simpa [window] using h⟩
  · exact ⟨2,by simpa [window] using h⟩

private theorem labels_lt {u v : K} (u0 : 0≤u) (uv : u<v)
    (gu : g u=0) (gv : g v=0) {i j : Fin 3}
    (wi : window i u) (wj : window j v) : i<j := by
  fin_cases i <;> fin_cases j <;> simp [window] at wi wj ⊢
  all_goals
    first
    | have bad := lo_increasing u0 uv wj.2.le
      rw [gu,gv] at bad
      exact (lt_irrefl _ bad).elim
    | have bad := middle_decreasing wi.1.le uv wj.2.le
      rw [gu,gv] at bad
      exact (lt_irrefl _ bad).elim
    | have bad := hi_increasing wi.1.le uv
      rw [gu,gv] at bad
      exact (lt_irrefl _ bad).elim
    | linarith only [wi.1,wi.2,wj.1,wj.2,uv,
        show (b:K)<c by norm_num [b,c],show (d:K)<e by norm_num [d,e],
        show (b:K)<e by norm_num [b,e]]

theorem critical_three_spacing {x y z : K} (x0 : 0≤x) (xy : x<y) (yz : y<z)
    (dx : (polynomial K).derivative.eval x=0)
    (dy : (polynomial K).derivative.eval y=0)
    (dz : (polynomial K).derivative.eval z=0) : 4*x+y<3*z := by
  rcases x0.eq_or_lt with h | h
  · rw [←h]
    linarith only [x0.trans xy.le,yz]
  · have y0 := h.trans xy
    have z0 := y0.trans yz
    have xy₂ : x^2<y^2 := by nlinarith [mul_pos (sub_pos.mpr xy) (add_pos h y0)]
    have yz₂ : y^2<z^2 := by nlinarith [mul_pos (sub_pos.mpr yz) (add_pos y0 z0)]
    have gx := g_of_positive_critical h dx
    have gy := g_of_positive_critical y0 dy
    have gz := g_of_positive_critical z0 dz
    obtain ⟨i,wi⟩ := locate (sq_nonneg x) gx
    obtain ⟨j,wj⟩ := locate (sq_nonneg y) gy
    obtain ⟨k,wk⟩ := locate (sq_nonneg z) gz
    have ij : i.val<j.val := labels_lt (sq_nonneg x) xy₂ gx gy wi wj
    have jk : j.val<k.val := labels_lt (sq_nonneg y) yz₂ gy gz wj wk
    have i0 : i=0 := Fin.ext (by have hi:=i.isLt;have hj:=j.isLt;have hk:=k.isLt;change i.val=0;omega)
    have j1 : j=1 := Fin.ext (by have hi:=i.isLt;have hj:=j.isLt;have hk:=k.isLt;change j.val=1;omega)
    have k2 : k=2 := Fin.ext (by have hi:=i.isLt;have hj:=j.isLt;have hk:=k.isLt;change k.val=2;omega)
    rw [i0] at wi
    rw [j1] at wj
    rw [k2] at wk
    have xu2 : x^2<((2:K)/5)^2 := by
      have xx : a<x^2 ∧ x^2<b := by simpa [window] using wi
      norm_num [b] at xx ⊢
      exact xx.2
    have yu2 : y^2<((3:K)/4)^2 := by
      have yy : c<y^2 ∧ y^2<d := by simpa [window] using wj
      norm_num [d] at yy ⊢
      exact yy.2
    have zl2 : ((5:K)/6)^2<z^2 := by
      have zz : e<z^2 ∧ z^2<f := by simpa [window] using wk
      norm_num [e] at zz ⊢
      exact zz.1
    have xu : x<(2:K)/5 := by
      by_contra! p
      nlinarith only [xu2,mul_nonneg (sub_nonneg.mpr p) (add_nonneg h.le (by norm_num : (0 : K) ≤ 2/5))]
    have yu : y<(3:K)/4 := by
      by_contra! p
      nlinarith only [yu2,mul_nonneg (sub_nonneg.mpr p) (add_nonneg y0.le (by norm_num : (0 : K) ≤ 3/4))]
    have zl : (5:K)/6<z := by
      by_contra! p
      nlinarith only [zl2,mul_nonneg (sub_nonneg.mpr p) (add_nonneg z0.le (by norm_num : (0 : K) ≤ 5/6))]
    linarith only [xu,yu,zl]

end
end RKCert.ReviewedNative.LegendreModeEightWindows
