module

public import RKCert.ReviewedNative.OneWeightOrderedSigns
public import RKCert.ReviewedNative.TwoWeightOrderedSigns
public import RKCert.ReviewedNative.OrderedAlternationDegree

import Mathlib.Tactic.Ring

@[expose] public section

/-! # The increasing numerical order of the two centered pivots -/
namespace RKCert.ReviewedNative.StrongCentered16

open Polynomial
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The physical order agrees with the increasing numerical order.
The six local moments alone suffice after the pivots are interior. -/
theorem increasing_local_impossible {q : K[X]} {a z : K}
    (qn : q≠0) (qd : q.natDegree≤5)
    (a0 : 0<a) (az : a<z) (z1 : z<1)
    (f1 : integral 0 a (X*q)=0) (f2 : integral 0 a (X^2*q)=0)
    (fm : integral 0 z (X*(X-C a)*q)=0)
    (r1 : integral z 1 ((1-X)*q)=0) (r2 : integral z 1 ((1-X)^2*q)=0)
    (rm : integral a 1 ((1-X)*(X-C z)*q)=0) : False := by
  let Y : K[X] := 1-X
  let U : K[X] := X*(X-C a)
  let V : K[X] := Y*(C z-X)
  have ydeg : Y.natDegree≤1 := by
    simpa only [Y,natDegree_one,natDegree_X,max_eq_right (Nat.zero_le 1)] using
      (natDegree_sub_le (1:K[X]) (X:K[X]))
  have udeg : U.natDegree≤2 :=
    natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C a).le
  have vdeg : V.natDegree≤2 := by
    have vd : (C z-X : K[X]).natDegree≤1 := by
      simpa only [natDegree_C,natDegree_X,max_eq_right (Nat.zero_le 1)] using
        (natDegree_sub_le (C z) (X:K[X]))
    exact natDegree_mul_le_of_le ydeg vd
  have small : q.natDegree<19 := by omega
  have scale (l r c : K) (P : K[X]) : integral l r (C c*P)=c*integral l r P := by
    simpa only [smul_eq_C_mul,smul_eq_mul] using (integral l r).map_smul c P
  have splice (l m r : K) (P : K[X]) :
      integral l m P+integral m r P=integral l r P := by
    simp only [integral_apply]
    ring
  have ry : integral z 1 (Y*q)=0 := r1
  have ry2 : integral z 1 (Y^2*q)=0 := r2
  have ryx : integral z 1 (Y*q*X)=0 := by
    have e : Y*q*X=Y*q-Y^2*q := by
      dsimp only [Y]
      ring
    simp only [e,map_sub,ry,ry2,sub_zero]
  have leftGrid : 2≤gridVariation q 0 a := by
    apply grid_variation_of_positive_moments (U:=(X:K[X])) (m:=2) a0 qn small
    · rw [natDegree_X]
      omega
    · intro x hx
      simpa only [eval_X] using hx.1
    · intro k
      have hk : k.val=0 ∨ k.val=1 := by
        have h := k.isLt
        omega
      rcases hk with h | h
      · simpa only [h,pow_zero,mul_one] using f1
      · rw [h,pow_one,show X*q*X=X^2*q by ring]
        exact f2
  have rightGrid : 2≤gridVariation q z 1 := by
    apply grid_variation_of_positive_moments (U:=Y) (m:=2) z1 qn small
    · omega
    · intro x hx
      simpa only [Y,eval_sub,eval_one,eval_X] using sub_pos.mpr hx.2
    · intro k
      have hk : k.val=0 ∨ k.val=1 := by
        have h := k.isLt
        omega
      rcases hk with h | h
      · simpa only [h,pow_zero,mul_one] using ry
      · simpa only [h,pow_one] using ryx
  have u0a : integral 0 a (U*q)=0 := by
    have e : U*q=X^2*q-C a*(X*q) := by
      dsimp only [U]
      ring
    simp only [e,map_sub,scale,f2,f1,mul_zero,sub_zero]
  have u0z : integral 0 z (U*q)=0 := fm
  have umid : integral a z (U*q)=0 := by
    simpa only [u0a,u0z,zero_add] using splice 0 a z (U*q)
  have vz1 : integral z 1 (V*q)=0 := by
    have e : V*q=Y^2*q-C (1-z)*(Y*q) := by
      simp only [V,Y,map_sub,map_one]
      ring
    rw [e,map_sub,scale,ry2,ry,mul_zero,sub_zero]
  have va1 : integral a 1 (V*q)=0 := by
    have e : V*q=-((1-X)*(X-C z)*q) := by
      dsimp only [V,Y]
      ring
    simp only [e,map_neg,rm,neg_zero]
  have vmid : integral a z (V*q)=0 := by
    simpa only [vz1,va1,add_zero] using splice a z 1 (V*q)
  have upos : ∀ x∈Set.Ioo a z, 0<U.eval x := by
    intro x hx
    simpa only [U,eval_mul,eval_sub,eval_X,eval_C] using
      mul_pos (a0.trans hx.1) (sub_pos.mpr hx.1)
  have vpos : ∀ x∈Set.Ioo a z, 0<V.eval x := by
    intro x hx
    simpa only [V,Y,eval_mul,eval_sub,eval_X,eval_C,eval_one] using
      mul_pos (sub_pos.mpr (hx.2.trans z1)) (sub_pos.mpr hx.2)
  have eqRatio (x : K) :
      U.eval x/V.eval x=(x/(1-x))*((x-a)/(z-x)) := by
    simp only [U,V,Y,eval_mul,eval_sub,eval_X,eval_C,eval_one,div_mul_div_comm]
  have ratio : StrictMonoOn (fun x => U.eval x/V.eval x) (Set.Ioo a z) := by
    intro x hx y hy hxy
    have ox : 0 < 1-x := sub_pos.mpr (hx.2.trans z1)
    have oy : 0 < 1-y := sub_pos.mpr (hy.2.trans z1)
    have zx : 0 < z-x := sub_pos.mpr hx.2
    have zy : 0 < z-y := sub_pos.mpr hy.2
    have h1 : x/(1-x)<y/(1-y) := by
      apply (div_lt_div_iff₀ ox oy).mpr
      apply sub_pos.mp
      calc
        0 < y-x := sub_pos.mpr hxy
        _ = y*(1-x)-x*(1-y) := by ring
    have h2 : (x-a)/(z-x)<(y-a)/(z-y) := by
      apply (div_lt_div_iff₀ zx zy).mpr
      apply sub_pos.mp
      calc
        0 < (z-a)*(y-x) := mul_pos (sub_pos.mpr az) (sub_pos.mpr hxy)
        _ = (y-a)*(z-x)-(x-a)*(z-y) := by ring
    change U.eval x / V.eval x < U.eval y / V.eval y
    rw [eqRatio x,eqRatio y]
    exact (mul_lt_mul_of_pos_right h1 (div_pos (sub_pos.mpr hx.1) zx)).trans
      (mul_lt_mul_of_pos_left h2 (div_pos (a0.trans hy.1) oy))
  have midGrid : 2≤gridVariation q a z :=
    grid_variation_of_monotone_ratio (P:=q) (U:=U) (V:=V)
      az qn small (by omega) (by omega) upos vpos
      (Or.inl ratio) umid vmid
  have hL := HasAlternationsOn.of_grid a0 leftGrid
  have hM := HasAlternationsOn.of_grid az midGrid
  have hR := HasAlternationsOn.of_grid z1 rightGrid
  have hLM := hL.add_open hM a0.le le_rfl az.le
  have all := hLM.add_open hR (a0.trans az).le le_rfl z1.le
  have impossible := all.le_natDegree
  omega

end
end RKCert.ReviewedNative.StrongCentered16
