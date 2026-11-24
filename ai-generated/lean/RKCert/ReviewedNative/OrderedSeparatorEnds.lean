module

public import RKCert.ReviewedNative.OneWeightOrderedSigns
public import RKCert.ReviewedNative.OrderedAlternationDegree

import Mathlib.Data.List.Chain
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact finite separators and signs near simple roots -/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem posBridge {a b c : K} (ab : 0 < a*b) (bc : 0 < b*c) : 0 < a*c := by
  have h : 0 < (b*b)*(a*c) := by
    calc
      0 < (a*b)*(b*c) := mul_pos ab bc
      _ = _ := by ring
  exact lt_of_not_ge fun no => h.not_ge (mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg b) no)

private theorem negBridge {a b c : K} (ab : a*b < 0) (bc : 0 < b*c) : a*c < 0 := by
  have h : (b*b)*(a*c) < 0 := by
    calc
      _ = (a*b)*(b*c) := by ring
      _ < 0 := mul_neg_of_neg_of_pos ab bc
  exact lt_of_not_ge fun no => h.not_ge (mul_nonneg (mul_self_nonneg b) no)

private theorem fitOpposite {a b s t : K} (ab : a*b < 0)
    (asFit : 0 < a*s) (btFit : 0 < b*t) : s*t < 0 := by
  have h : 0 < (a*b)*(s*t) := by
    calc
      0 < (a*s)*(b*t) := mul_pos asFit btFit
      _ = _ := by ring
  exact lt_of_not_ge fun no => h.not_ge (mul_nonpos_of_nonpos_of_nonneg ab.le no)

/-- Elementary sign preservation at a nonzero value of a polynomial.
Factor the displaced polynomial by X and bound the quotient by the
finite sum of its absolute coefficients on the unit interval. -/
theorem eval_same_sign_near (P : K[X]) {r : K} (pn : P.eval r≠0) :
    ∃ lo hi, lo<r ∧ r<hi ∧ ∀ x∈Set.Ioo lo hi, 0<P.eval r*P.eval x := by
  classical
  let F : K[X] := P.comp (X+C r)-C (P.eval r)
  have f0 : F.eval 0=0 := by
    simp [F,eval_comp]
  have fd : (X:K[X]) ∣ F := by
    rw [X_dvd_iff,coeff_zero_eq_eval_zero]
    exact f0
  obtain ⟨Q,hQ⟩ := fd
  have diff (x : K) : P.eval x-P.eval r=(x-r)*Q.eval (x-r) := by
    have h := congrArg (Polynomial.eval (x-r)) hQ
    simpa only [F,eval_sub,eval_comp,eval_add,eval_X,eval_C,sub_add_cancel,eval_mul] using h
  let M : K := ∑ i ∈ Q.support, |Q.coeff i|
  have M0 : 0≤M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have M1 : 0<M+1 := M0.trans_lt (lt_add_of_pos_right M zero_lt_one)
  have bound (t : K) (ht : |t|≤1) : |Q.eval t|≤M := by
    have e : Q.eval t=∑ i ∈ Q.support, Q.coeff i*t^i := by
      simpa only [eval_finsetSum,eval_monomial] using congrArg (Polynomial.eval t) Q.as_sum_support
    calc
      |Q.eval t| = |∑ i ∈ Q.support, Q.coeff i*t^i| := by rw [e]
      _ ≤ ∑ i ∈ Q.support, |Q.coeff i*t^i| :=
        Finset.abs_sum_le_sum_abs (fun i => Q.coeff i*t^i) Q.support
      _ ≤ M := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_pow]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg t) ht)
          (abs_nonneg (Q.coeff i))).trans_eq (mul_one _)
  let E : K := min 1 (|P.eval r|/(M+1))
  have Ep : 0<E := lt_min zero_lt_one (div_pos (abs_pos.mpr pn) M1)
  refine ⟨r-E,r+E,sub_lt_self r Ep,lt_add_of_pos_right r Ep,?_⟩
  intro x hx
  have lo : -E<x-r := by
    have h := sub_lt_sub_right hx.1 r
    have e : (r-E)-r = -E := by ring
    rwa [e] at h
  have hi : x-r<E := by
    have h := sub_lt_sub_right hx.2 r
    have e : (r+E)-r = E := by ring
    rwa [e] at h
  have close : |x-r|<E := abs_lt.mpr ⟨lo,hi⟩
  have small : |x-r|≤1 := (close.trans_le (min_le_left _ _)).le
  have narrow : |x-r| < |P.eval r|/(M+1) := close.trans_le (min_le_right _ _)
  have err : |P.eval x-P.eval r| < |P.eval r| := by
    rw [diff x,abs_mul]
    calc
      |x-r| * |Q.eval (x-r)| ≤ |x-r| * M :=
        mul_le_mul_of_nonneg_left (bound _ small) (abs_nonneg _)
      _ ≤ |x-r| * (M+1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg _)
      _ < |P.eval r| := (lt_div_iff₀ M1).mp narrow
  rcases lt_or_gt_of_ne pn with hn | hp
  · have b : P.eval x-P.eval r < -P.eval r := by
      simpa only [abs_of_neg hn] using (abs_lt.mp err).2
    have px : P.eval x<0 := by
      simpa only [sub_add_cancel,neg_add_cancel] using add_lt_add_left b (P.eval r)
    exact mul_pos_of_neg_of_neg hn px
  · have b : -P.eval r < P.eval x-P.eval r := by
      simpa only [abs_of_pos hp] using (abs_lt.mp err).1
    have px : 0<P.eval x := by
      simpa only [sub_add_cancel,neg_add_cancel] using add_lt_add_left b (P.eval r)
    exact mul_pos hp px

/-- An exact alternating witness inherits the sign at a live left endpoint. -/
theorem exact_chain_left_sign {P : K[X]} {l r : K} {m : ℕ} {xs : List K}
    (top : ¬ HasAlternationsOn P (Set.Ioo l r) (m+1)) (hne : xs≠[])
    (inc : xs.Pairwise (· < ·)) (inside : ∀ x∈xs, x∈Set.Ioo l r)
    (alt : AlternatingSamples P xs) (len : xs.length=m+1) (pl : P.eval l≠0) :
    0<P.eval l*P.eval (xs.head hne) := by
  let f := xs.head hne
  have fm : f∈xs := List.head_mem hne
  have fLive := alt.nonzero f fm
  change 0<P.eval l*P.eval f
  by_contra no
  have neg : P.eval f*P.eval l<0 := by
    simpa only [mul_comm] using
      (lt_of_le_of_ne (le_of_not_gt no) (mul_ne_zero pl fLive))
  obtain ⟨lo,hi,hl,lh,good⟩ := eval_same_sign_near P pl
  obtain ⟨y,ly,ymax⟩ := exists_between (lt_min (inside f fm).1 lh)
  have yf : y<f := ymax.trans_le (min_le_left _ _)
  have yh : y<hi := ymax.trans_le (min_le_right _ _)
  have yn : 0<P.eval l*P.eval y := good y ⟨hl.trans ly,yh⟩
  have yl : P.eval y≠0 := (mul_ne_zero_iff.mp yn.ne').2
  have link : P.eval y*P.eval f<0 := by
    simpa only [mul_comm] using negBridge neg yn
  have winc : (y::xs).Pairwise (· < ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨fun x hx => yf.trans_le ?_,inc⟩
    have ile : xs.Pairwise (· ≤ ·) := inc.imp (fun h => h.le)
    exact ile.rel_head hx
  have walt : AlternatingSamples P (y::xs) := by
    refine ⟨?_,alt.jumps.cons_of_ne_nil hne link⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact yl
    · exact alt.nonzero x hx
  exact top (HasAlternationsOn.of_alternating_samples winc (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨ly,yf.trans (inside f fm).2⟩
    · exact inside x hx) walt (by simp [len]))

/-- An exact alternating witness inherits the sign at a live right endpoint. -/
theorem exact_chain_right_sign {P : K[X]} {l r : K} {m : ℕ} {xs : List K}
    (top : ¬ HasAlternationsOn P (Set.Ioo l r) (m+1)) (hne : xs≠[])
    (inc : xs.Pairwise (· < ·)) (inside : ∀ x∈xs, x∈Set.Ioo l r)
    (alt : AlternatingSamples P xs) (len : xs.length=m+1) (pr : P.eval r≠0) :
    0<P.eval r*P.eval (xs.getLast hne) := by
  let f := xs.getLast hne
  have fm : f∈xs := List.getLast_mem hne
  have fLive := alt.nonzero f fm
  change 0<P.eval r*P.eval f
  by_contra no
  have neg : P.eval f*P.eval r<0 := by
    simpa only [mul_comm] using
      (lt_of_le_of_ne (le_of_not_gt no) (mul_ne_zero pr fLive))
  obtain ⟨lo,hi,hl,lh,good⟩ := eval_same_sign_near P pr
  obtain ⟨y,lowY,yr⟩ := exists_between (max_lt_iff.mpr ⟨(inside f fm).2,hl⟩)
  have fy : f<y := (le_max_left _ _).trans_lt lowY
  have loY : lo<y := (le_max_right _ _).trans_lt lowY
  have yn : 0<P.eval r*P.eval y := good y ⟨loY,yr.trans lh⟩
  have yl : P.eval y≠0 := (mul_ne_zero_iff.mp yn.ne').2
  have link : P.eval f*P.eval y<0 := negBridge neg yn
  have winc : (xs++[y]).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨inc,by simp,?_⟩
    intro u hu v hv
    have ev : v=y := by simpa using hv
    subst v
    have ile : xs.Pairwise (· ≤ ·) := inc.imp (fun h => h.le)
    exact (ile.rel_getLast hu).trans_lt fy
  have walt : AlternatingSamples P (xs++[y]) := by
    refine ⟨?_,alt.jumps.append (List.IsChain.singleton y) ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact alt.nonzero x hx
      · have e : x=y := by simpa using hx
        simpa only [e] using yl
    · intro u hu v hv
      rw [List.getLast?_eq_some_getLast hne] at hu
      change v∈some y at hv
      rw [(Option.mem_some.mp hu).symm,(Option.mem_some.mp hv).symm]
      exact link
  exact top (HasAlternationsOn.of_alternating_samples winc (by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact inside x hx
    · have e : x=y := by simpa using hx
      rw [e]
      exact ⟨(inside f fm).1.trans fy,yr⟩) walt (by simp [len]))

/-- A positive leading coefficient is earned by scaling the checked separator
by its own leading coefficient. The original ordered witnesses are retained. -/
private theorem exact_grid_separator {q : K[X]} {l r : K} {m : ℕ}
    (lr : l<r) (qn : q≠0) (small : q.natDegree<19) (mp : 1≤m)
    (low : m≤gridVariation q l r) (top : ¬ HasAlternationsOn q (Set.Ioo l r) (m+1)) :
    ∃ (B : K[X]) (c : K) (ys : List K),
      B.natDegree=m ∧ 0<B.leadingCoeff ∧
      (∀ i : Fin 19, q.eval (intervalPoint l r i)≠0 →
        0<c*(q.eval (intervalPoint l r i)*B.eval (intervalPoint l r i))) ∧
      List.Sublist ys (gridSamples l r) ∧ ys.length=m+1 ∧
      AlternatingSamples q ys ∧ AlternatingSamples B ys := by
  have upper : gridVariation q l r≤m := by
    apply le_of_not_gt
    intro bad
    exact top (HasAlternationsOn.of_grid lr (by omega))
  have gv : gridVariation q l r=m := le_antisymm upper low
  obtain ⟨ys,sub,cnt,yalt⟩ := exists_alternating_subsequence q (gridSamples l r)
  have len : ys.length=m+1 := by
    change ys.length-1=gridVariation q l r at cnt
    omega
  have sorted : ys.Pairwise (· < ·) := List.Pairwise.sublist sub (gridSamples_increasing lr)
  have inGrid (x : K) (hx : x∈ys) : ∃ i : Fin 19, intervalPoint l r i=x := by
    have h := sub.subset hx
    change x∈List.ofFn (intervalPoint l r) at h
    exact List.mem_ofFn.mp h
  have live := exists_nonzero_grid_sample lr qn small
  obtain ⟨A,ad,fit⟩ := exists_grid_separator (intervalPoint_strictMono lr) live
  have afit (x : K) (hx : x∈ys) : 0<q.eval x*A.eval x := by
    obtain ⟨i,hi⟩ := inGrid x hx
    rw [←hi]
    exact fit i (by simpa only [hi] using yalt.nonzero x hx)
  have aalt : AlternatingSamples A ys := by
    refine ⟨fun x hx => (mul_ne_zero_iff.mp (afit x hx).ne').2,?_⟩
    apply yalt.jumps.imp_of_mem_imp
    intro x y hx hy jump
    exact fitOpposite jump (afit x hx) (afit y hy)
  have age : m≤A.natDegree :=
    (HasAlternationsOn.of_alternating_samples (S:=Set.Ioo l r) sorted
      (fun x hx => gridSamples_inside lr x (sub.subset hx)) aalt (by omega : m≤ys.length-1)).le_natDegree
  have adeg : A.natDegree=m := le_antisymm (by simpa only [←gridVariation_eq,gv] using ad) age
  have an : A≠0 := by
    intro e
    rw [e,natDegree_zero] at adeg
    omega
  let c := A.leadingCoeff
  let B := C c*A
  have cn : c≠0 := leadingCoeff_ne_zero.mpr an
  have bdeg : B.natDegree=m := by simpa only [B,natDegree_C_mul cn] using adeg
  have bp : 0<B.leadingCoeff := by
    simp only [B,leadingCoeff_mul,leadingCoeff_C]
    exact mul_self_pos.mpr cn
  have bval (x : K) : B.eval x=c*A.eval x := by simp only [B,eval_mul,eval_C]
  refine ⟨B,c,ys,bdeg,bp,?_,sub,len,yalt,?_⟩
  · intro i hi
    rw [bval]
    calc
      0 < (c*c)*(q.eval (intervalPoint l r i)*A.eval (intervalPoint l r i)) :=
        mul_pos (mul_self_pos.mpr cn) (fit i hi)
      _ = _ := by ring
  · refine ⟨fun x hx => by rw [bval]; exact mul_ne_zero cn (aalt.nonzero x hx),?_⟩
    apply aalt.jumps.imp
    intro x y jump
    rw [bval,bval]
    calc
      _ = (c*c)*(A.eval x*A.eval y) := by ring
      _ < 0 := mul_neg_of_pos_of_neg (mul_self_pos.mpr cn) jump

private theorem score_at_pos {e c g v w : K} (eg : 0<e*g)
    (fit : 0<c*(g*v)) (vp : 0<v) (wfit : 0<c*w) : 0<e*w := by
  have gc : 0<g*c := (mul_pos_iff_of_pos_right vp).mp (by
    calc
      0 < c*(g*v) := fit
      _ = (g*c)*v := by ring)
  exact posBridge (posBridge eg gc) wfit

private theorem score_at_neg {e c g v w : K} (eg : 0<e*g)
    (fit : 0<c*(g*v)) (vn : v<0) (wfit : 0<c*w) : 0<e*(-w) :=
  score_at_pos (c:=-c) (v:=-v) eg (by calc
    0 < c*(g*v) := fit
    _ = (-c)*(g*(-v)) := by ring)
    (neg_pos.mpr vn) (by simpa only [neg_mul_neg] using wfit)

/-- A degree-one separator is negative before the left interval endpoint
and positive after the right endpoint. Grid scores inherit either live end. -/
theorem exact_one_separator_signs {q : K[X]} {l r : K}
    (lr : l < r) (qn : q ≠ 0) (small : q.natDegree < 19)
    (low : 1 ≤ gridVariation q l r) (top : ¬ HasAlternationsOn q (Set.Ioo l r) 2) :
    ∃ k u : K, 0 < k ∧
      (let B : K[X] := C k * X + C u
       (∀ x ≤ l, B.eval x < 0) ∧ (∀ x ≥ r, 0 < B.eval x) ∧
       (q.eval l ≠ 0 → ∀ i : Fin 19, q.eval (intervalPoint l r i) ≠ 0 →
         0 < q.eval l * (q.eval (intervalPoint l r i) * (-B.eval (intervalPoint l r i)))) ∧
       (q.eval r ≠ 0 → ∀ i : Fin 19, q.eval (intervalPoint l r i) ≠ 0 →
         0 < q.eval r * (q.eval (intervalPoint l r i) * B.eval (intervalPoint l r i)))) := by
  obtain ⟨B,c,ys,bd,bp,fit,sub,len,alt,balt⟩ :=
    exact_grid_separator (m:=1) lr qn small le_rfl low top
  obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp len
  let k := B.leadingCoeff
  let u := B.coeff 0
  have lc : B.coeff 1 = k := by dsimp only [k]; rw [←bd,coeff_natDegree]
  have be : B = C k * X + C u :=
    (eq_X_add_C_of_natDegree_le_one bd.le).trans (by rw [lc])
  have beval (s : K) : B.eval s = k*s+u := by rw [be]; simp only [eval_add,eval_mul,eval_C,eval_X]
  have increasing : StrictMono B.eval := by
    intro s t st
    change B.eval s < B.eval t
    rw [beval s,beval t]
    exact add_lt_add_left (mul_lt_mul_of_pos_left st bp) _
  have sorted : ([x,y] : List K).Pairwise (· < ·) :=
    List.Pairwise.sublist sub (gridSamples_increasing lr)
  have xy := List.pairwise_pair.mp sorted
  have inside (s : K) (hs : s∈[x,y]) : s∈Set.Ioo l r :=
    gridSamples_inside lr s (sub.subset hs)
  have hfit (s : K) (hs : s∈[x,y]) : 0<c*(q.eval s*B.eval s) := by
    have hs' := sub.subset hs
    change s∈List.ofFn (intervalPoint l r) at hs'
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hs'
    rw [←hi]
    exact fit i (by simpa only [hi] using alt.nonzero s hs)
  have signs : B.eval x < 0 ∧ 0 < B.eval y := by
    have opp : B.eval x * B.eval y < 0 := (List.isChain_pair (R := fun x y : K => B.eval x * B.eval y < 0)).mp balt.jumps
    rcases mul_neg_iff.mp opp with ⟨xp,yn⟩ | h
    · exact ((xp.trans (increasing xy)).not_ge yn.le).elim
    · exact h
  have left : ∀ s ≤ l, B.eval s < 0 := fun s hs =>
    (increasing (hs.trans_lt (inside x (by simp)).1)).trans signs.1
  have right : ∀ s ≥ r, 0 < B.eval s := fun s hs =>
    signs.2.trans (increasing ((inside y (by simp)).2.trans_le hs))
  have orL (ql : q.eval l ≠ 0) (i : Fin 19) (hi : q.eval (intervalPoint l r i) ≠ 0) :
      0 < q.eval l * (q.eval (intervalPoint l r i) * (-B.eval (intervalPoint l r i))) := by
    have tag : 0 < q.eval l*q.eval x :=
      exact_chain_left_sign (m:=1) top (by simp) sorted inside alt len ql
    simpa only [mul_neg] using score_at_neg tag (hfit x (by simp)) signs.1 (fit i hi)
  have orR (qr : q.eval r ≠ 0) (i : Fin 19) (hi : q.eval (intervalPoint l r i) ≠ 0) :
      0 < q.eval r * (q.eval (intervalPoint l r i) * B.eval (intervalPoint l r i)) := by
    have tag : 0 < q.eval r*q.eval y :=
      exact_chain_right_sign (m:=1) top (by simp) sorted inside alt len qr
    exact score_at_pos tag (hfit y (by simp)) signs.2 (fit i hi)
  refine ⟨k,u,bp,?_⟩
  simpa only [←be] using And.intro left (And.intro right (And.intro orL orR))

/-- A positive-leading quadratic with two witnessed changes is positive
outside the witness extremes. Secants suffice; no roots are adjoined. -/
theorem quadratic_exterior_signs {B : K[X]} {k t u x y z : K}
    (be : B = C k*X^2-C t*X+C u) (kp : 0<k) (xy : x<y) (yz : y<z)
    (a : B.eval x*B.eval y<0) (b : B.eval y*B.eval z<0) :
    0<B.eval x ∧ 0<B.eval z ∧ ∀ w, w≤x ∨ z≤w → 0<B.eval w := by
  have delta (v w : K) : B.eval w-B.eval v = (w-v)*(k*(v+w)-t) := by
    simp only [be,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X]
    ring
  have rise {v w : K} (vw : v<w) (h : B.eval v<B.eval w) : 0<k*(v+w)-t := by
    apply (mul_pos_iff_of_pos_left (sub_pos.mpr vw)).mp
    rw [←delta v w]
    exact sub_pos.mpr h
  have fall {v w : K} (vw : v<w) (h : B.eval w<B.eval v) : k*(v+w)-t<0 := by
    have nn : (w-v)*(k*(v+w)-t)<0 := by rw [←delta v w]; exact sub_neg.mpr h
    exact lt_of_not_ge fun bad => nn.not_ge (mul_nonneg (sub_nonneg.mpr vw.le) bad)
  have signs : 0<B.eval x ∧ B.eval y<0 ∧ 0<B.eval z := by
    rcases mul_neg_iff.mp a with ⟨xp,yn⟩ | ⟨xn,yp⟩
    · rcases mul_neg_iff.mp b with ⟨hp,_⟩ | ⟨_,hp⟩
      · exact (yn.not_ge hp.le).elim
      · exact ⟨xp,yn,hp⟩
    · rcases mul_neg_iff.mp b with ⟨_,zn⟩ | ⟨hn,_⟩
      · have gap : x+y<y+z := by
          exact (add_lt_add_left (xy.trans yz) y).trans_le (add_comm z y).le
        have inc : k*(x+y)-t<k*(y+z)-t :=
          sub_lt_sub_right (mul_lt_mul_of_pos_left gap kp) t
        exact (lt_irrefl (0:K) ((rise xy (xn.trans yp)).trans
          (inc.trans (fall yz (zn.trans yp))))).elim
      · exact (hn.not_ge yp.le).elim
  refine ⟨signs.1,signs.2.2,?_⟩
  intro w hw
  rcases hw with hx | hz
  · have h : w+x≤x+y := by
      exact (add_le_add_left (hx.trans xy.le) x).trans (add_comm y x).le
    have sl : k*(w+x)-t≤0 :=
      (sub_le_sub_right (mul_le_mul_of_nonneg_left h kp.le) t).trans
        (fall xy (signs.2.1.trans signs.1)).le
    have dp : 0≤B.eval w-B.eval x := by
      rw [delta x w,add_comm x w]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx) sl
    exact signs.1.trans_le (sub_nonneg.mp dp)
  · have h : y+z≤z+w := by
      exact (add_le_add_left (yz.le.trans hz) z).trans (add_comm w z).le
    have sl : 0≤k*(z+w)-t :=
      (rise yz (signs.2.1.trans signs.2.2)).le.trans
        (sub_le_sub_right (mul_le_mul_of_nonneg_left h kp.le) t)
    have dp : 0≤B.eval w-B.eval z := by
      rw [delta z w]
      exact mul_nonneg (sub_nonneg.mpr hz) sl
    exact signs.2.2.trans_le (sub_nonneg.mp dp)

/-- The calibrated quadratic separator for a grid with exactly two changes
in the open interval. Both endpoint scores use the same separator. -/
theorem exact_two_separator_signs {q : K[X]} {l r : K}
    (lr : l < r) (qn : q ≠ 0) (small : q.natDegree < 19)
    (low : 2 ≤ gridVariation q l r) (top : ¬ HasAlternationsOn q (Set.Ioo l r) 3) :
    ∃ k t u : K, 0 < k ∧
      (let B : K[X] := C k*X^2-C t*X+C u
       (∀ s, s≤l ∨ r≤s → 0<B.eval s) ∧
       (q.eval l≠0 → ∀ i : Fin 19, q.eval (intervalPoint l r i)≠0 →
         0<q.eval l*(q.eval (intervalPoint l r i)*B.eval (intervalPoint l r i))) ∧
       (q.eval r≠0 → ∀ i : Fin 19, q.eval (intervalPoint l r i)≠0 →
         0<q.eval r*(q.eval (intervalPoint l r i)*B.eval (intervalPoint l r i)))) := by
  obtain ⟨B,c,ys,bd,bp,fit,sub,len,alt,balt⟩ :=
    exact_grid_separator (m:=2) lr qn small (by decide) low top
  obtain ⟨x,y,z,rfl⟩ := List.length_eq_three.mp len
  let k := B.leadingCoeff
  let t := -B.coeff 1
  let u := B.coeff 0
  have lc : B.coeff 2 = k := by dsimp only [k]; rw [←bd,coeff_natDegree]
  have ex : B = monomial 0 (B.coeff 0)+monomial 1 (B.coeff 1)+monomial 2 (B.coeff 2) := by
    nth_rw 1 [B.as_sum_range' 3 (by omega)]
    simp [Finset.sum_range_succ]
  have be : B = C k*X^2-C t*X+C u := by
    calc
      B = _ := ex
      _ = _ := by
        simp only [← C_mul_X_pow_eq_monomial,pow_zero,pow_one,mul_one,lc,t,u,map_neg]
        ring
  have sorted : ([x,y,z] : List K).Pairwise (· < ·) :=
    List.Pairwise.sublist sub (gridSamples_increasing lr)
  have xy : x<y := (List.pairwise_cons.mp sorted).1 y (by simp)
  have yz : y<z := List.pairwise_pair.mp (List.pairwise_cons.mp sorted).2
  have inside (s : K) (hs : s∈[x,y,z]) : s∈Set.Ioo l r :=
    gridSamples_inside lr s (sub.subset hs)
  have hfit (s : K) (hs : s∈[x,y,z]) : 0<c*(q.eval s*B.eval s) := by
    have hs' := sub.subset hs
    change s∈List.ofFn (intervalPoint l r) at hs'
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hs'
    rw [←hi]
    exact fit i (by simpa only [hi] using alt.nonzero s hs)
  have jxy := (List.isChain_cons_cons.mp balt.jumps).1
  have jyz := List.isChain_pair.mp (List.isChain_cons_cons.mp balt.jumps).2
  obtain ⟨xp,zp,out⟩ := quadratic_exterior_signs be bp xy yz jxy jyz
  have eOut (s : K) (h : s≤l ∨ r≤s) : 0<B.eval s := by
    rcases h with h | h
    · exact out s (Or.inl (h.trans (inside x (by simp)).1.le))
    · exact out s (Or.inr ((inside z (by simp)).2.le.trans h))
  have orL (ql : q.eval l≠0) (i : Fin 19) (hi : q.eval (intervalPoint l r i)≠0) :
      0<q.eval l*(q.eval (intervalPoint l r i)*B.eval (intervalPoint l r i)) := by
    have tag : 0<q.eval l*q.eval x :=
      exact_chain_left_sign (m:=2) top (by simp) sorted inside alt len ql
    exact score_at_pos tag (hfit x (by simp)) xp (fit i hi)
  have orR (qr : q.eval r≠0) (i : Fin 19) (hi : q.eval (intervalPoint l r i)≠0) :
      0<q.eval r*(q.eval (intervalPoint l r i)*B.eval (intervalPoint l r i)) := by
    have tag : 0<q.eval r*q.eval z :=
      exact_chain_right_sign (m:=2) top (by simp) sorted inside alt len qr
    exact score_at_pos tag (hfit z (by simp)) zp (fit i hi)
  refine ⟨k,t,u,bp,?_⟩
  simpa only [←be] using And.intro eOut (And.intro orL orR)

/-- A witnessed sign chain is unchanged when evaluations are multiplied
by a positive polynomial factor on the sample set. -/
theorem alternations_mul_pos_iff {P R : K[X]} {S : Set K} {m : ℕ}
    (pos : ∀ x∈S, 0<R.eval x) :
    HasAlternationsOn (R*P) S m ↔ HasAlternationsOn P S m := by
  have transport {A B : K[X]} (h : HasAlternationsOn A S m)
      (fit : ∀ x∈S, A.eval x≠0 → 0<A.eval x*B.eval x) :
      HasAlternationsOn B S m := by
    obtain ⟨xs,inc,inside,alt,low⟩ := h.alternating_samples
    have f (x : K) (hx : x∈xs) : 0<A.eval x*B.eval x := fit x (inside x hx) (alt.nonzero x hx)
    apply HasAlternationsOn.of_alternating_samples inc inside _ low
    refine ⟨fun x hx => (mul_ne_zero_iff.mp (f x hx).ne').2,?_⟩
    apply alt.jumps.imp_of_mem_imp
    intro x y hx hy jump
    exact fitOpposite jump (f x hx) (f y hy)
  constructor
  · intro h
    apply transport h
    intro x hx hn
    have pn : P.eval x≠0 := by
      intro e
      exact hn (by simp only [eval_mul,e,mul_zero])
    simpa only [eval_mul,mul_assoc] using mul_pos (pos x hx) (mul_self_pos.mpr pn)
  · intro h
    apply transport h
    intro x hx pn
    calc
      0 < R.eval x*(P.eval x*P.eval x) := mul_pos (pos x hx) (mul_self_pos.mpr pn)
      _ = P.eval x*(R*P).eval x := by simp only [eval_mul]; ring

/-- Odd reflection moves a finite sign chain to the opposite open window. -/
theorem reflect_odd_alternations {P : K[X]} {l r : K} {m : ℕ}
    (odd : P.comp (1-X) = -P) (h : HasAlternationsOn P (Set.Ioo l r) m) :
    HasAlternationsOn P (Set.Ioo (1-r) (1-l)) m := by
  let t : K → K := fun x => 1-x
  have ev (x : K) : P.eval (t x) = -P.eval x := by
    have e := congrArg (Polynomial.eval x) odd
    simpa only [t,eval_comp,eval_sub,eval_one,eval_X,eval_neg] using e
  obtain ⟨xs,inc,inside,alt,low⟩ := h.alternating_samples
  let ys := xs.reverse.map t
  have yinc : ys.Pairwise (· < ·) := by
    dsimp only [ys]
    apply List.pairwise_map.mpr
    apply List.pairwise_reverse.mpr
    exact inc.imp (fun h => sub_lt_sub_left h (1:K))
  have yinside (y : K) (hy : y∈ys) : y∈Set.Ioo (1-r) (1-l) := by
    change y∈xs.reverse.map t at hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    have xm := inside x (List.mem_reverse.mp hx)
    exact ⟨sub_lt_sub_left xm.2 _,sub_lt_sub_left xm.1 _⟩
  have yalt : AlternatingSamples P ys := by
    refine ⟨?_,?_⟩
    · intro y hy
      change y∈xs.reverse.map t at hy
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      rw [ev]
      exact neg_ne_zero.mpr (alt.nonzero x (List.mem_reverse.mp hx))
    · dsimp only [ys]
      apply (List.isChain_map t).mpr
      apply List.isChain_reverse.mpr
      apply alt.jumps.imp
      intro x y h
      simpa only [ev,neg_mul_neg,mul_comm] using h
  exact HasAlternationsOn.of_alternating_samples yinc yinside yalt
    (by simpa only [ys,List.length_map,List.length_reverse] using low)

/-- Passing one simple root adds at least one change to any finite
preceding witness, with no root-splitting or completeness hypothesis. -/
theorem simple_root_prefix_jump {P U : K[X]} {l r s : K} {m : ℕ}
    (lr : l<r) (rs : r<s) (fac : P=(X-C r)*U) (ur : U.eval r≠0)
    (h : HasAlternationsOn P (Set.Ioo l r) m) :
    HasAlternationsOn P (Set.Ioo l s) (m+1) := by
  obtain ⟨xs,inc,inside,low⟩ := h
  have base (ys : List K) : l≤ys.foldr max l := by
    induction ys with
    | nil => exact le_rfl
    | cons x ys ih => exact ih.trans (le_max_right x _)
  have bounded (ys : List K) : (∀ x∈ys, x<r) → ys.foldr max l<r := by
    induction ys with
    | nil => intro _; exact lr
    | cons x ys ih =>
      intro H
      exact max_lt_iff.mpr ⟨H x (by simp),ih (fun w hw => H w (List.mem_cons_of_mem x hw))⟩
  obtain ⟨lo,hi,lor,rhi,near⟩ := eval_same_sign_near U ur
  let b := xs.foldr max l
  have br : b<r := bounded xs (fun x hx => (inside x hx).2)
  obtain ⟨x,bx,xr⟩ := exists_between (max_lt_iff.mpr ⟨br,lor⟩)
  obtain ⟨y,ry,yb⟩ := exists_between (lt_min rs rhi)
  have bx' : b<x := (le_max_left b lo).trans_lt bx
  have lx : l<x := (base xs).trans_lt bx'
  have ys : y<s := yb.trans_le (min_le_left _ _)
  have tx : 0<U.eval r*U.eval x :=
    near x ⟨(le_max_right b lo).trans_lt bx,xr.trans rhi⟩
  have ty : 0<U.eval r*U.eval y :=
    near y ⟨lor.trans ry,yb.trans_le (min_le_right _ _)⟩
  have uu : 0<U.eval x*U.eval y := posBridge (by simpa only [mul_comm] using tx) ty
  have pairOpp : P.eval x*P.eval y<0 := by
    have e : P.eval x*P.eval y=((x-r)*(y-r))*(U.eval x*U.eval y) := by
      simp only [fac,eval_mul,eval_sub,eval_X,eval_C]
      ring
    rw [e]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr xr) (sub_pos.mpr ry)) uu
  have left : HasAlternationsOn P (Set.Ioo l x) m := by
    refine ⟨xs,inc,?_,low⟩
    intro w hw
    exact ⟨(inside w hw).1,(List.le_max_of_le' l hw le_rfl).trans_lt bx'⟩
  have pair : HasAlternationsOn P (Set.Icc x y) 1 := by
    apply HasAlternationsOn.of_alternating_samples (xs:=[x,y]) (List.pairwise_pair.mpr (xr.trans ry))
    · intro w hw
      have hxy : x≤y := (xr.trans ry).le
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨le_rfl,hxy⟩
      · exact ⟨hxy,le_rfl⟩
    · refine ⟨?_,List.isChain_pair.mpr pairOpp⟩
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact (mul_ne_zero_iff.mp pairOpp.ne).1
      · exact (mul_ne_zero_iff.mp pairOpp.ne).2
    · simp
  have joined := left.add_separated pair (fun _ hw _ hv => hw.2.trans_le hv.1)
  apply joined.mono _ le_rfl
  intro w hw
  rcases hw with hw | hw
  · exact ⟨hw.1,hw.2.trans (xr.trans rs)⟩
  · exact ⟨lx.trans_le hw.1,hw.2.trans_lt ys⟩

end
end RKCert.ReviewedNative.FiniteOrderedSigns
