module

public import RKCert.ReviewedNative.WeakFiveSoleOuterOrder

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Ordered reciprocal gluing of the paid sole-outer moments

The rational function is only a pointwise comparison. The integrated
quantity combines two genuine polynomial moments with an exact-degree
interpolating test. Every evaluation takes place in the ordered field
supplying the actual quartic roots. -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.RightPoleInterpolation RKCert.ReviewedNative.FiniteStoppedBracket
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem cuts_filter_hull (xs : List K) (p : K → Bool) :
    cutProduct xs = cutProduct (xs.filter p) * cutProduct (xs.filter fun x => !p x) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hp : p a <;> simp only [List.filter_cons,hp,Bool.not_false,Bool.not_true,
      if_true,Bool.false_eq_true,if_false,cutProduct_cons,ih] <;> ring

private theorem cuts_filter_count (xs : List K) (p : K → Bool) :
    (xs.filter p).length + (xs.filter fun x => !p x).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a <;> simp only [List.filter_cons,hp,Bool.not_false,Bool.not_true,
      if_true,Bool.false_eq_true,if_false,List.length_cons] <;> omega

private theorem right_poles_cons (a : K) (ds : List K) :
    poleProduct (a::ds)=(C a-X)*poleProduct ds := rfl

private theorem right_poles_nil : poleProduct ([] : List K)=1 := rfl

private theorem right_poles_mul (ds es : List K) :
    poleProduct (ds++es)=poleProduct ds*poleProduct es := by
  simp only [poleProduct,List.map_append,List.prod_append]

private theorem right_poles_recip (ds : List K) {x : K} (all : ∀ d∈ds,x<d) :
    (poleProduct ds).eval x * (ds.map (fun d => (d-x)⁻¹)).prod=1 := by
  induction ds with
  | nil => simp [right_poles_nil]
  | cons a ds ih =>
    have an : a-x≠0 := (sub_pos.mpr (all a (by simp))).ne'
    have tail := ih (fun d hd => all d (List.mem_cons_of_mem _ hd))
    simp only [right_poles_cons,eval_mul,eval_sub,eval_C,eval_X,List.map_cons,List.prod_cons]
    calc
      _ = ((a-x)*(a-x)⁻¹)*((poleProduct ds).eval x*(ds.map (fun d => (d-x)⁻¹)).prod) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ an,tail,mul_one]

private theorem pole_parity_sq (n : ℕ) : ((-1:K)^n)*((-1:K)^n)=1 := by
  rw [← mul_pow]
  norm_num

private theorem right_poles_square (rs : List K) :
    poleProduct rs* poleProduct rs=(cutProduct rs)^2 := by
  apply Polynomial.funext
  intro x
  simp only [eval_mul,eval_pow,poleProduct_orientation]
  calc
    _ = (((-1:K)^rs.length)*((-1:K)^rs.length))*((cutProduct rs).eval x)^2 := by ring
    _ = _ := by rw [pole_parity_sq,one_mul]

/-- Literal sole-outer endpoint with the truthful, already-paid order. -/
theorem sole_outer_words_impossible {q : K[X]} {u a h z : K} (W : SoleOuterWords q u a h z)
    (gap : GapComplete q) : False := by
  obtain ⟨B,xs,r,S⟩ := sole_outer_unit_split W gap
  have ha := sole_outer_forward_inner_after_h W S
  let p : K → Bool := fun x => decide (x<u)
  let ls := xs.filter p
  let rs := (xs.filter fun x => !p x)++[r]
  let L := cutProduct ls
  let R := cutProduct rs
  have early (x : K) (hx : x∈ls) : x<u := by simpa [p] using (List.mem_filter.mp hx).2
  have nonempty : ls≠[] := by
    obtain ⟨x,hx,xu⟩ := S.leftLive
    have hit : x∈ls := List.mem_filter.mpr ⟨hx,by simp [p,xu]⟩
    intro eq
    rw [eq] at hit
    exact List.not_mem_nil hit
  have no_at_stop (x : K) (hx : x∈xs) : x≠u := by
    intro same
    subst x
    apply W.uActive
    have r0 : (cutProduct xs).eval u=0 := cut_list_has_root hx
    rw [S.factor,eval_mul,eval_mul,r0,mul_zero,zero_mul]
  have right (x : K) (hx : x∈rs) : u<x := by
    rcases List.mem_append.mp hx with pre | last
    · have nu : ¬x<u := by simpa [p] using (List.mem_filter.mp pre).2
      exact lt_of_le_of_ne (le_of_not_gt nu) (no_at_stop x (List.mem_filter.mp pre).1).symm
    · have e := List.mem_singleton.mp last
      simpa only [e] using W.uh.trans S.late.1
  have count : ls.length+rs.length=xs.length+1 := by
    change (xs.filter p).length+((xs.filter fun x => !p x)++[r]).length=_
    simp only [List.length_append,List.length_singleton]
    have splitCount := cuts_filter_count xs p
    omega
  have card := S.upper
  have rl : 0<rs.length := by simp [rs]
  have ll : 0<ls.length := List.length_pos_iff.mpr nonempty
  have leftcount : L.natDegree≤3 := (cutProduct_degree ls).trans (by omega)
  have route : q=B*L*R := by
    rw [S.factor,cuts_filter_hull xs p]
    simp only [rs,cut_list_append,cutProduct_cons,cutProduct_nil,mul_one,L,R,ls]
    ring
  have qval (x : K) : q.eval x=B.eval x*L.eval x*R.eval x := by
    simpa only [eval_mul] using congrArg (Polynomial.eval x) route
  let d := [u,a,a,h,h]++rs
  let ds := 1::d
  have eligible {x : K} (hx : x∈d) : u≤x := by
    rcases List.mem_append.mp hx with fixedPoles | tail
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixedPoles
      rcases fixedPoles with rfl | rfl | rfl | rfl | rfl
      · exact le_rfl
      · exact (W.uh.trans ha).le
      · exact (W.uh.trans ha).le
      · exact W.uh.le
      · exact W.uh.le
    · exact (right x tail).le
  have allPole {x : K} (hx : x∈ds) : u≤x := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact W.uUnit.2.le
    · exact eligible hx
  let f : K → K := fun x => (ds.map (fun d => (d-x)⁻¹)).prod
  have fp : RightPoleFun u f := by
    simpa only [f,ds,List.map_cons,List.prod_cons] using
      (RightPoleFun.pole 1 W.uUnit.2.le).mul_pole_list d (fun x hx => eligible hx)
  obtain ⟨H,g,I⟩ := fp.interpolant ls early
  let P := R*(X-C a)*(X-C h)*H
  have pd : P.natDegree≤5 := by
    have D := I.degree
    have rd := cutProduct_degree rs
    have step₁ := natDegree_mul_le_of_le rd (natDegree_X_sub_C a).le
    have step₂ := natDegree_mul_le_of_le step₁ (natDegree_X_sub_C h).le
    have total := natDegree_mul_le_of_le step₂ D
    change P.natDegree≤_
    exact total.trans (by omega)
  let T := X*(1-X)*(q*rawFourHull u a h z)*P
  let τ : K := (-1)^rs.length
  let J := C τ*(X*(X-C z)*q)
  let D := (1-X)*(C u-X)*R^2*(X-C a)^2*(X-C h)^2
  have T0 : integral 0 1 T=0 := W.global P pd
  have J0 : integral 0 u J=0 := by
    change integral 0 u (C τ * (X * (X - C z) * q)) = 0
    rw [integral_C_mul, W.left_tilt_zero z, mul_zero]
  have Td : T.natDegree≤15 := natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (outer_unit_bubble_degree (K:=K)) (natDegree_mul_le_of_le W.degree.le (raw_four_hull_degree u a h z))) pd
  have Jd : J.natDegree≤6 := (natDegree_C_mul_le _ _).trans
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C _).le) W.degree.le)
  have flatten : poleProduct ds =
      (1-X)*(C u-X)*(C a-X)^2*(C h-X)^2*poleProduct rs := by
    change poleProduct ([1,u,a,a,h,h]++rs)=_
    rw [right_poles_mul [1,u,a,a,h,h] rs]
    simp only [right_poles_cons,right_poles_nil,map_one,mul_one]
    ring
  have dd : D=poleProduct ds*poleProduct rs := by
    calc D = (1-X)*(C u-X)*(C a-X)^2*(C h-X)^2*(poleProduct rs*poleProduct rs) := by
           rw [right_poles_square]
           dsimp only [D,R]
           ring
         _ = _ := by rw [flatten]; ring
  have Dval (x : K) : D.eval x=(1-x)*(u-x)*(R.eval x)^2*(x-a)^2*(x-h)^2 := by
    simp only [D,eval_mul,eval_pow,eval_sub,eval_one,eval_X,eval_C]
  have gval (x : K) : T.eval x = x*(1-x)*(x-z)*B.eval x*L.eval x*(x-u)*
      (R.eval x)^2*(x-a)^2*(x-h)^2*H.eval x := by
    simp only [T,P,rawFourHull,eval_mul,eval_sub,eval_X,eval_C,eval_one,qval]
    ring
  have jval (x : K) : J.eval x=x*(x-z)*B.eval x*L.eval x*(poleProduct rs).eval x := by
    simp only [J,eval_mul,eval_C,eval_sub,eval_X,qval,poleProduct_orientation,τ,R]
    ring
  have prefSign (x : K) (hx : x∈Set.Ioo 0 u) :
      (T+J).eval x=(x*(x-z)*B.eval x)*(L.eval x)^2*D.eval x*g x := by
    have de : D.eval x*f x=(poleProduct rs).eval x := by
      rw [dd,eval_mul]
      calc
        _ = (poleProduct rs).eval x*((poleProduct ds).eval x*f x) := by ring
        _ = _ := by rw [show (poleProduct ds).eval x*f x=1 from
          right_poles_recip ds (fun d hd => hx.2.trans_le (allPole hd)),mul_one]
    calc
      (T+J).eval x =
          (x*(x-z)*B.eval x)*L.eval x*((poleProduct rs).eval x-D.eval x*H.eval x) := by
        rw [eval_add,gval,jval,Dval]
        ring
      _ = (x*(x-z)*B.eval x)*L.eval x*(D.eval x*(f x-H.eval x)) := by rw [← de]; ring
      _ = (x*(x-z)*B.eval x)*(L.eval x)^2*D.eval x*g x := by
        rw [I.error x hx.2]
        dsimp only [L]
        ring
  have allStrict (x : K) (hx : x∈Set.Ioo 0 u) :
      0<(x*(x-z)*B.eval x)*D.eval x*g x := by
    have dp : 0<D.eval x := by
      rw [dd,eval_mul]
      exact mul_pos (poleProduct_pos ds x (fun d hd => hx.2.trans_le (allPole hd)))
        (poleProduct_pos rs x (fun r hr => hx.2.trans (right r hr)))
    exact mul_pos (mul_pos (mul_pos (mul_pos hx.1 (sub_pos.mpr (W.zNeg.trans hx.1)))
      (S.positive x ⟨hx.1,hx.2.trans W.uUnit.2⟩)) dp) (I.rest.positive x hx.2)
  have pos : 0 < integral 0 u (T+J) := by
    have both : (T+J).natDegree≤15 := natDegree_add_le_of_le Td (Jd.trans (by decide : 6 ≤ 15))
    obtain ⟨i,live⟩ := exists_nonzero_grid_sample W.uUnit.1 (cut_list_nonzero ls)
      (leftcount.trans_lt (by decide))
    apply integral_pos_of_grid_samples W.uUnit.1 (both.trans (by decide))
    · intro j
      have hx := intervalPoint_mem W.uUnit.1 j
      rw [prefSign _ hx]
      have s := mul_nonneg (allStrict _ hx).le (sq_nonneg (L.eval (intervalPoint 0 u j)))
      convert s using 1 <;> ring
    · refine ⟨i,?_⟩
      have hx := intervalPoint_mem W.uUnit.1 i
      rw [prefSign _ hx]
      have s := mul_pos (allStrict _ hx) (sq_pos_of_ne_zero live)
      convert s using 1 <;> ring
  have suffix : 0 ≤ integral u 1 T := by
    apply outer_integral_nonneg W.uUnit.2 (Td.trans (by decide))
    intro x hx
    have x0 := W.uUnit.1.trans hx.1
    have lc : 0<L.eval x := cut_list_pos_above ls (fun r hr => (early r hr).trans hx.1)
    have positivePrefix : 0 < x*(1-x)*(x-z)*B.eval x*L.eval x*(x-u) :=
      mul_pos (mul_pos (mul_pos (mul_pos (mul_pos x0 (sub_pos.mpr hx.2))
        (sub_pos.mpr (W.zNeg.trans x0))) (S.positive x ⟨x0,hx.2⟩)) lc) (sub_pos.mpr hx.1)
    rw [gval]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg positivePrefix.le (sq_nonneg _)) (sq_nonneg _))
        (sq_nonneg _))
      (I.nonneg x hx.1)
  have split := exact_integral_join T 0 u 1
  rw [map_add,J0,add_zero] at pos
  have allPos : 0 < integral 0 1 T := split ▸ add_pos_of_pos_of_nonneg pos suffix
  exact (ne_of_gt allPos) T0

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
