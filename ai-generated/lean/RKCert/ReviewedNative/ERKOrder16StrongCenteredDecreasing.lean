module

public import RKCert.ReviewedNative.OrderedSeparatorEnds
public import RKCert.ReviewedNative.TwoWeightOrderedSigns
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredResidual

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The decreasing numerical order of the two centered pivots -/
namespace RKCert.ReviewedNative.StrongCentered16

open Polynomial
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Six local moments, the two live pivots, and the odd contrast are
incompatible when the numerical order reverses the physical order. -/
theorem decreasing_local_impossible {q : K[X]} {a z : K}
    (qn : q≠0) (qd : q.natDegree≤5) (z0 : 0<z) (za : z<a) (a1 : a<1)
    (qa : q.eval a≠0) (qz : q.eval z≠0)
    (oddJ : ((X-C a)*(X-C z)*q).comp (1-X) = -((X-C a)*(X-C z)*q))
    (f1 : integral 0 a (X*q)=0) (f2 : integral 0 a (X^2*q)=0)
    (fm : integral 0 z (X*(X-C a)*q)=0)
    (r1 : integral z 1 ((1-X)*q)=0) (r2 : integral z 1 ((1-X)^2*q)=0)
    (rm : integral a 1 ((1-X)*(X-C z)*q)=0) : False := by
  let Y : K[X] := 1-X
  let U : K[X] := X*(C a-X)
  let V : K[X] := Y*(X-C z)
  have a0 : 0<a := z0.trans za
  have z1 : z<1 := za.trans a1
  have small : q.natDegree<19 := by omega
  have ydeg : Y.natDegree≤1 := by
    simpa only [Y,natDegree_one,natDegree_X,max_eq_right (Nat.zero_le 1)] using
      (natDegree_sub_le (1:K[X]) (X:K[X]))
  have udeg : U.natDegree≤2 := by
    have d : (C a-X : K[X]).natDegree≤1 := by
      simpa only [natDegree_C,natDegree_X,max_eq_right (Nat.zero_le 1)] using
        (natDegree_sub_le (C a) (X:K[X]))
    exact natDegree_mul_le_of_le natDegree_X.le d
  have vdeg : V.natDegree≤2 := natDegree_mul_le_of_le ydeg (natDegree_X_sub_C z).le
  have scale (l r c : K) (P : K[X]) : integral l r (C c*P)=c*integral l r P := by
    simpa only [smul_eq_C_mul,smul_eq_mul] using (integral l r).map_smul c P
  have splice (l m r : K) (P : K[X]) :
      integral l m P+integral m r P=integral l r P := by
    simp only [integral_apply]
    ring
  have ry : integral z 1 (Y*q)=0 := r1
  have ry2 : integral z 1 (Y^2*q)=0 := r2
  have ua : integral 0 a (U*q)=0 := by
    have e : U*q=C a*(X*q)-X^2*q := by dsimp only [U]; ring
    simp only [e,map_sub,scale,f1,f2,mul_zero,sub_zero]
  have ul : integral 0 z (U*q)=0 := by
    have e : U*q = -(X*(X-C a)*q) := by dsimp only [U]; ring
    simp only [e,map_neg,fm,neg_zero]
  have um : integral z a (U*q)=0 := by
    simpa only [ul,ua,zero_add] using splice 0 z a (U*q)
  have vz : integral z 1 (V*q)=0 := by
    have e : V*q=C (1-z)*(Y*q)-Y^2*q := by
      simp only [V,Y,map_sub,map_one]
      ring
    rw [e, map_sub, scale, ry, ry2, mul_zero, sub_zero]
  have vr : integral a 1 (V*q)=0 := rm
  have vm : integral z a (V*q)=0 := by
    simpa only [vz,vr,add_zero] using splice z a 1 (V*q)
  have leftGrid : 1≤gridVariation q 0 z := by
    apply grid_variation_of_positive_moments (P:=q) (U:=U) (m:=1) z0 qn small
    · omega
    · intro x hx
      simpa only [U,eval_mul,eval_sub,eval_C,eval_X] using
        mul_pos hx.1 (sub_pos.mpr (hx.2.trans za))
    · intro i
      have iv : i.val=0 := by have h := i.isLt; omega
      simpa only [iv,pow_zero,mul_one] using ul
  have rightGrid : 1≤gridVariation q a 1 := by
    apply grid_variation_of_positive_moments (P:=q) (U:=V) (m:=1) a1 qn small
    · omega
    · intro x hx
      simpa only [V,Y,eval_mul,eval_sub,eval_C,eval_X,eval_one] using
        mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr (za.trans hx.1))
    · intro i
      have iv : i.val=0 := by have h := i.isLt; omega
      simpa only [iv,pow_zero,mul_one] using vr
  have upos : ∀ x∈Set.Ioo z a, 0<U.eval x := by
    intro x hx
    simpa only [U,eval_mul,eval_sub,eval_C,eval_X] using
      mul_pos (z0.trans hx.1) (sub_pos.mpr hx.2)
  have vpos : ∀ x∈Set.Ioo z a, 0<V.eval x := by
    intro x hx
    simpa only [V,Y,eval_mul,eval_sub,eval_C,eval_X,eval_one] using
      mul_pos (sub_pos.mpr (hx.2.trans a1)) (sub_pos.mpr hx.1)
  have eqRatio (x : K) :
      U.eval x/V.eval x=(x/(x-z))*((a-x)/(1-x)) := by
    simp only [U,V,Y,eval_mul,eval_sub,eval_C,eval_X,eval_one,div_mul_div_comm,
      mul_comm (x-z) (1-x)]
  have anti : StrictAntiOn (fun x => U.eval x/V.eval x) (Set.Ioo z a) := by
    intro x hx y hy hxy
    have px : 0<x-z := sub_pos.mpr hx.1
    have py : 0<y-z := sub_pos.mpr hy.1
    have ox : 0<1-x := sub_pos.mpr (hx.2.trans a1)
    have oy : 0<1-y := sub_pos.mpr (hy.2.trans a1)
    have h1 : y/(y-z)<x/(x-z) := by
      apply (div_lt_div_iff₀ py px).mpr
      apply sub_pos.mp
      calc
        0 < z*(y-x) := mul_pos z0 (sub_pos.mpr hxy)
        _ = x*(y-z)-y*(x-z) := by ring
    have h2 : (a-y)/(1-y)<(a-x)/(1-x) := by
      apply (div_lt_div_iff₀ oy ox).mpr
      apply sub_pos.mp
      calc
        0 < (1-a)*(y-x) := mul_pos (sub_pos.mpr a1) (sub_pos.mpr hxy)
        _ = (a-x)*(1-y)-(a-y)*(1-x) := by ring
    change U.eval y / V.eval y < U.eval x / V.eval x
    rw [eqRatio y,eqRatio x]
    exact (mul_lt_mul_of_pos_right h1 (div_pos (sub_pos.mpr hy.2) oy)).trans
      (mul_lt_mul_of_pos_left h2 (div_pos (z0.trans hx.1) px))
  have midGrid : 2≤gridVariation q z a :=
    grid_variation_of_monotone_ratio (P:=q) (U:=U) (V:=V)
      za qn small (by omega) (by omega) upos vpos (Or.inr anti) um vm
  have hL := HasAlternationsOn.of_grid z0 leftGrid
  have hM := HasAlternationsOn.of_grid za midGrid
  have hR := HasAlternationsOn.of_grid a1 rightGrid
  have noSix {mL mM mR : ℕ} (big : 6≤mL+mM+mR)
      (L : HasAlternationsOn q (Set.Ioo 0 z) mL)
      (M : HasAlternationsOn q (Set.Ioo z a) mM)
      (R : HasAlternationsOn q (Set.Ioo a 1) mR) : False := by
    have LM := L.add_open M z0.le le_rfl za.le
    have d := (LM.add_open R a0.le le_rfl a1.le).le_natDegree
    omega
  have tagged {l r : K} (lr : l<r) (e : K) (G : K[X]) (gd : G.natDegree≤2)
      (fit : ∀ i : Fin 19, q.eval (intervalPoint l r i)≠0 →
        0<e*(q.eval (intervalPoint l r i)*G.eval (intervalPoint l r i))) :
      0<e*integral l r (G*q) := by
    let P := C e*(G*q)
    have pd : P.natDegree≤19 :=
      (natDegree_C_mul_le e (G*q)).trans (natDegree_mul_le.trans (by omega))
    have strict (i : Fin 19) (hi : q.eval (intervalPoint l r i)≠0) :
        0<P.eval (intervalPoint l r i) := by
      simpa only [P,eval_mul,eval_C,mul_comm] using fit i hi
    have nonneg (i : Fin 19) : 0≤P.eval (intervalPoint l r i) := by
      by_cases hi : q.eval (intervalPoint l r i)=0
      · simp only [P,eval_mul,eval_C,hi,mul_zero,le_rfl]
      · exact (strict i hi).le
    obtain ⟨i,hi⟩ := exists_nonzero_grid_sample lr qn small
    simpa only [P,scale] using integral_pos_of_grid_samples lr pd nonneg ⟨i,strict i hi⟩
  have release {e v w d c : K} (dp : 0<d) (cp : 0<c)
      (eq : d*v=c*w) (pw : 0<e*w) : 0<e*v := by
    apply (mul_pos_iff_of_pos_left dp).mp
    calc
      0 < c*(e*w) := mul_pos cp pw
      _ = e*(c*w) := by ring
      _ = e*(d*v) := congrArg (fun x : K => e*x) eq.symm
      _ = _ := by ring
  have M3 : HasAlternationsOn q (Set.Ioo z a) 3 := by
    by_contra noM
    obtain ⟨k,t,u,kp,sOut,sL,sR⟩ := exact_two_separator_signs za qn small midGrid noM
    let S : K[X] := C k*X^2-C t*X+C u
    have se (x : K) : S.eval x=k*x^2-t*x+u := by
      simp only [S,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X]
    have sd : S.natDegree≤2 := by
      apply natDegree_add_le_of_degree_le (n:=2) _ (by simp)
      exact (natDegree_sub_le _ _).trans (max_le
        ((natDegree_C_mul_le k (X^2:K[X])).trans (natDegree_X_pow 2).le)
        ((natDegree_C_mul_le t (X:K[X])).trans (natDegree_X.le.trans (by decide))))
    have deficit : (¬HasAlternationsOn q (Set.Ioo 0 z) 2) ∨
        (¬HasAlternationsOn q (Set.Ioo a 1) 2) := by
      by_cases l : HasAlternationsOn q (Set.Ioo 0 z) 2
      · exact Or.inr (fun r => noSix (by decide) l hM r)
      · exact Or.inl l
    rcases deficit with noL | noR

    · obtain ⟨b,f,_,_,bOut,_,bFit⟩ := exact_one_separator_signs z0 qn small leftGrid noL
      let B : K[X] := C b*X+C f
      have be (x : K) : B.eval x=b*x+f := by
        simp only [B,eval_add,eval_mul,eval_C,eval_X]
      have bd : B.natDegree≤1 :=
        natDegree_add_le_of_degree_le ((natDegree_C_mul_le b (X:K[X])).trans natDegree_X.le) (by simp)
      have bp : 0<B.eval a := bOut a za.le
      have polL : C (B.eval a)*X-C b*U-C (0:K)*U=C (1:K)*(X*B) := by
        rw [be a]
        simp only [U,B,map_add,map_mul,map_zero,map_one,zero_mul,sub_zero,one_mul]
        ring
      have eqL := scaled_moment_of_residual polL ul ul
      have signL : 0<q.eval z*integral 0 z (X*q) := by
        apply release bp zero_lt_one eqL
        apply tagged z0 (q.eval z) (X*B) (natDegree_mul_le_of_le natDegree_X.le bd)
        intro i hi
        let x := intervalPoint (0:K) z i
        change 0<q.eval z*(q.eval x*(X*B).eval x)
        have e : q.eval z*(q.eval x*(X*B).eval x)=x*(q.eval z*(q.eval x*B.eval x)) := by
          simp only [eval_mul,eval_X]
          ring
        rw [e]
        exact mul_pos (intervalPoint_mem z0 i).1 (bFit qz i hi)
      let D := (1+z-a)*u+z*(k*a-t)
      have u0 : 0<u := by
        have e : u=S.eval 0 := by rw [se]; ring
        rw [e]
        exact sOut 0 (Or.inl z0.le)
      have isa : 0<S.eval a := sOut a (Or.inr le_rfl)
      have ap : 0<a*D := by
        have e : a*D=u*(1-a)*(a-z)+z*S.eval a := by rw [se]; dsimp only [D]; ring
        rw [e]
        exact add_pos (mul_pos (mul_pos u0 (sub_pos.mpr a1)) (sub_pos.mpr za)) (mul_pos z0 isa)
      have dp : 0<D := lt_of_not_ge fun h => ap.not_ge (mul_nonpos_of_nonneg_of_nonpos a0.le h)
      have polM : C D*X-C (z*k-u)*U-C u*V=C z*S := by
        simp only [D,U,V,Y,S,map_add,map_sub,map_mul,map_one,map_ofNat]
        ring
      have eqM := scaled_moment_of_residual polM um vm
      have signM : 0<q.eval z*integral z a (X*q) :=
        release dp z0 eqM (tagged za (q.eval z) S sd (sL qz))
      have cross := (splice 0 z a (X*q)).trans f1
      have pos : 0<q.eval z*(integral 0 z (X*q)+integral z a (X*q)) := by
        rw [mul_add]
        exact add_pos signL signM
      rw [cross,mul_zero] at pos
      exact lt_irrefl _ pos
    · obtain ⟨b,f,_,bOut,_,bFit,_⟩ := exact_one_separator_signs a1 qn small rightGrid noR
      let B : K[X] := C b*X+C f
      let T := -(Y*B)
      have be (x : K) : B.eval x=b*x+f := by
        simp only [B,eval_add,eval_mul,eval_C,eval_X]
      have bd : B.natDegree≤1 :=
        natDegree_add_le_of_degree_le ((natDegree_C_mul_le b (X:K[X])).trans natDegree_X.le) (by simp)
      have td : T.natDegree≤2 := by
        dsimp only [T]
        rw [natDegree_neg]
        exact natDegree_mul_le_of_le ydeg bd
      have bp : 0 < -B.eval z := neg_pos.mpr (bOut z za.le)
      have polR : C (-B.eval z)*Y-C b*V-C (0:K)*V=C (1:K)*T := by
        rw [be z]
        simp only [V,T,B,map_add,map_mul,map_neg,map_zero,map_one,zero_mul,sub_zero,one_mul]
        ring
      have eqR := scaled_moment_of_residual polR vr vr
      have signR : 0<q.eval a*integral a 1 (Y*q) := by
        apply release bp zero_lt_one eqR
        apply tagged a1 (q.eval a) T td
        intro i hi
        let x := intervalPoint a (1:K) i
        change 0<q.eval a*(q.eval x*T.eval x)
        have yp : 0<Y.eval x := by
          simpa only [Y,eval_sub,eval_one,eval_X,x] using sub_pos.mpr (intervalPoint_mem a1 i).2
        have e : q.eval a*(q.eval x*T.eval x)=Y.eval x*(q.eval a*(q.eval x*(-B.eval x))) := by
          simp only [T,eval_neg,eval_mul]
          ring
        rw [e]
        exact mul_pos yp (bFit qa i hi)
      let a' := 1-z
      let z' := 1-a
      let t' := 2*k-t
      let u' := k-t+u
      let D' := (1+z'-a')*u'+z'*(k*a'-t')
      have ap0 : 0<a' := sub_pos.mpr z1
      have zp0 : 0<z' := sub_pos.mpr a1
      have up0 : 0<u' := by
        have e : u'=S.eval 1 := by rw [se]; dsimp only [u']; ring
        rw [e]
        exact sOut 1 (Or.inr a1.le)
      have om : 0<1-a' := by dsimp only [a']; rwa [sub_sub_cancel]
      have step : 0<a'-z' := by
        have e : a'-z'=a-z := by dsimp only [a',z']; ring
        rw [e]
        exact sub_pos.mpr za
      have sp : 0<S.eval z := sOut z (Or.inl le_rfl)
      have ap : 0<a'*D' := by
        have e : a'*D'=u'*(1-a')*(a'-z')+z'*S.eval z := by
          rw [se]
          dsimp only [D',a',z',t',u']
          ring
        rw [e]
        exact add_pos (mul_pos (mul_pos up0 om) step) (mul_pos zp0 sp)
      have dp : 0<D' := lt_of_not_ge fun h => ap.not_ge (mul_nonpos_of_nonneg_of_nonpos ap0.le h)
      have polM : C D'*Y-C (z'*k-u')*V-C u'*U=C z'*S := by
        simp only [D',a',z',t',u',U,V,Y,S,map_add,map_sub,map_mul,map_one,map_ofNat]
        ring
      have eqM := scaled_moment_of_residual polM vm um
      have signM : 0<q.eval a*integral z a (Y*q) :=
        release dp zp0 eqM (tagged za (q.eval a) S sd (sR qa))
      have cross := (splice z a 1 (Y*q)).trans ry
      have pos : 0<q.eval a*(integral z a (Y*q)+integral a 1 (Y*q)) := by
        rw [mul_add]
        exact add_pos signM signR
      rw [cross,mul_zero] at pos
      exact lt_irrefl _ pos

  have noL2 : ¬ HasAlternationsOn q (Set.Ioo 0 z) 2 := fun h =>
    noSix (mL:=2) (mM:=3) (mR:=1) (by decide) h M3 hR
  have noR2 : ¬ HasAlternationsOn q (Set.Ioo a 1) 2 := fun h =>
    noSix (mL:=1) (mM:=3) (mR:=2) (by decide) hL M3 h
  let D : K[X] := (X-C a)*(X-C z)
  let J := D*q
  have jOdd : J.comp (1-X) = -J := oddJ
  have dL : ∀ x∈Set.Ioo 0 z, 0<D.eval x := by
    intro x hx
    simpa only [D,eval_mul,eval_sub,eval_C,eval_X] using
      mul_pos_of_neg_of_neg (sub_neg.mpr (hx.2.trans za)) (sub_neg.mpr hx.2)
  have dR : ∀ x∈Set.Ioo a 1, 0<D.eval x := by
    intro x hx
    simpa only [D,eval_mul,eval_sub,eval_C,eval_X] using
      mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr (za.trans hx.1))
  have jL : HasAlternationsOn J (Set.Ioo 0 z) 1 :=
    (alternations_mul_pos_iff dL).mpr hL
  have jR : HasAlternationsOn J (Set.Ioo a 1) 1 :=
    (alternations_mul_pos_iff dR).mpr hR
  have noJL : ¬ HasAlternationsOn J (Set.Ioo 0 z) 2 := fun h =>
    noL2 ((alternations_mul_pos_iff dL).mp h)
  have noJR : ¬ HasAlternationsOn J (Set.Ioo a 1) 2 := fun h =>
    noR2 ((alternations_mul_pos_iff dR).mp h)
  have jrPre : HasAlternationsOn J (Set.Ioo 0 (1-a)) 1 := by
    simpa only [sub_self] using reflect_odd_alternations jOdd jR
  have noJrPre : ¬ HasAlternationsOn J (Set.Ioo 0 (1-a)) 2 := by
    intro h
    apply noJR
    simpa only [sub_sub_cancel,sub_zero] using reflect_odd_alternations jOdd h
  let QZ : K[X] := (X-C a)*q
  let QA : K[X] := (X-C z)*q
  let QC := QA.comp (1-X)
  have jFacZ : J=(X-C z)*QZ := by dsimp only [J,D,QZ]; ring
  have jFacA : J=(X-C a)*QA := by dsimp only [J,D,QA]; ring
  have jFacC : J=(X-C (1-a))*QC := by
    have h : J.comp (1-X) = -((X-C (1-a))*QC) := by
      rw [jFacA,mul_comp]
      simp only [QC,sub_comp,X_comp,C_comp,map_sub,map_one]
      ring
    exact neg_injective (jOdd.symm.trans h)
  have qzLive : QZ.eval z≠0 := by
    simp only [QZ,eval_mul,eval_sub,eval_C,eval_X]
    exact mul_ne_zero (sub_ne_zero.mpr za.ne) qz
  have qcLive : QC.eval (1-a)≠0 := by
    simp only [QC,QA,eval_comp,eval_sub,eval_one,eval_X,sub_sub_cancel,eval_mul,eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr za.ne') qa
  have pivot : z=1-a := by
    apply le_antisymm
    · apply le_of_not_gt
      intro h
      exact noJL (simple_root_prefix_jump (sub_pos.mpr a1) h jFacC qcLive jrPre)
    · apply le_of_not_gt
      intro h
      exact noJrPre (simple_root_prefix_jump z0 h jFacZ qzLive jL)
  have dSym : D.comp (1-X)=D := by
    simp only [D,mul_comp,sub_comp,X_comp,C_comp,one_comp,pivot,map_sub,map_one]
    ring
  have qOdd : q.comp (1-X) = -q := by
    have dn : D≠0 :=
      mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero z)
    apply mul_left_cancel₀ dn
    change (D*q).comp (1-X) = -(D*q) at jOdd
    simpa only [mul_comp,dSym,mul_neg] using jOdd
  let W : K[X] := X*Y
  have wOdd : (W*q).comp (1-X) = -(W*q) := by
    simp only [W,Y,mul_comp,sub_comp,one_comp,X_comp,sub_sub_cancel,qOdd]
    ring
  have global0 : integral 0 1 (W*q)=0 := by
    have e := integral_reflect (W*q) (0:K)
    rw [sub_zero,wOdd,map_neg] at e
    linarith only [e]
  have wExpand : W*q=X*q-X^2*q := by dsimp only [W,Y]; ring
  have atA : integral 0 a (W*q)=0 := by simp only [wExpand,map_sub,f1,f2,sub_zero]
  have afterA : integral a 1 (W*q)=0 := by
    simpa only [atA,global0,zero_add] using splice 0 a 1 (W*q)
  have atZ : integral 0 z (W*q)=0 := by
    have e := integral_reflect (W*q) a
    rw [←pivot,wOdd,map_neg,afterA,neg_eq_zero] at e
    exact e
  have same : integral 0 z (X*q)=integral 0 z (X^2*q) := by
    simpa only [wExpand,map_sub,sub_eq_zero] using atZ
  have vi : integral 0 z (X^2*q)=a*integral 0 z (X*q) := by
    have e : X*(X-C a)*q=X^2*q-C a*(X*q) := by ring
    simpa only [e,map_sub,scale,sub_eq_zero] using fm
  have zf1 : integral 0 z (X*q)=0 := by
    have prod : (1-a)*integral 0 z (X*q)=0 := by
      calc
        _ = integral 0 z (X*q)-a*integral 0 z (X*q) := by ring
        _ = integral 0 z (X^2*q)-a*integral 0 z (X*q) := by
          exact congrArg (fun e : K => e-a*integral 0 z (X*q)) same
        _ = 0 := sub_eq_zero.mpr vi
    exact (mul_eq_zero.mp prod).resolve_left (sub_pos.mpr a1).ne'
  have zf2 := same.symm.trans zf1
  have leftTwo : 2≤gridVariation q 0 z := by
    apply grid_variation_of_positive_moments (P:=q) (U:=(X:K[X])) (m:=2) z0 qn small
    · rw [natDegree_X]
      omega
    · intro x hx
      simpa only [eval_X] using hx.1
    · intro i
      have ii : i.val=0 ∨ i.val=1 := by have h := i.isLt; omega
      rcases ii with h | h
      · simpa only [h,pow_zero,mul_one] using zf1
      · rw [h,pow_one,show X*q*X=X^2*q by ring]
        exact zf2
  exact noL2 (HasAlternationsOn.of_grid z0 leftTwo)

end
end RKCert.ReviewedNative.StrongCentered16
