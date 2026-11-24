module

public import RKCert.ReviewedNative.ERK19ZeroScalarInput
import RKCert.ReviewedNative.OneWeightOrderedSigns
import RKCert.ReviewedNative.TwoWeightOrderedSigns
import RKCert.ReviewedNative.OrderedAlternationDegree
import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Ordered opposed-window exclusion after exterior localization

Among the moment fields, only the twelve local moments are used. The first and last chronological clocks need not lie in (0,1).
-/
namespace RKCert.ReviewedNative.ERK19ZeroScalar

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def leftTwo (a : K) : K[X] := X * (X - C a)
private def leftThree (a b : K) : K[X] := leftTwo a * (X - C b)
private def rightTwo (d : K) : K[X] := (1 - X) * (X - C d)
private def rightThree (d c : K) : K[X] := rightTwo d * (X - C c)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rightOne_degree : (1 - (X : K[X])).natDegree = 1 := by
  rw [show (1 - (X : K[X])) = -(X - C (1 : K)) by simp,
    natDegree_neg, natDegree_X_sub_C]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem leftTwo_degree (a : K) : (leftTwo a).natDegree ≤ 2 := by
  unfold leftTwo
  exact natDegree_mul_le_of_le (natDegree_X (R := K)).le (natDegree_X_sub_C a).le

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rightTwo_degree (d : K) : (rightTwo d).natDegree ≤ 2 := by
  unfold rightTwo
  exact natDegree_mul_le_of_le (rightOne_degree (K := K)).le (natDegree_X_sub_C d).le

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem leftThree_degree (a b : K) : (leftThree a b).natDegree ≤ 3 := by
  change (leftTwo a * (X - C b)).natDegree ≤ 3
  apply natDegree_mul_le.trans
  have h := leftTwo_degree a
  rw [natDegree_X_sub_C]
  omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rightThree_degree (d c : K) : (rightThree d c).natDegree ≤ 3 := by
  change (rightTwo d * (X - C c)).natDegree ≤ 3
  apply natDegree_mul_le.trans
  have h := rightTwo_degree d
  rw [natDegree_X_sub_C]
  omega

private theorem addLinearMask {l r t : K} {M T : K[X]}
    (p0 : integral l r (M*T) = 0) (p1 : integral l r (M*T*X) = 0) :
    integral l r (M*(X-C t)*T) = 0 := by
  rw [show M*(X-C t)*T = M*T*X - t • (M*T) by
      rw [smul_eq_C_mul]
      ring,
    map_sub, map_smul, p1, p0, smul_zero, sub_zero]

private theorem extendMaskTwo {l r : K} {M P : K[X]}
    (paid : ∀ j : Fin 3, integral l r (M*P*X^j.val) = 0)
    (t : K) (k : Fin 2) : integral l r (M*(X-C t)*P*X^k.val) = 0 := by
  have hk := k.isLt
  have p0 : integral l r (M*(P*X^k.val)) = 0 := by
    simpa only [Fin.val_mk,mul_assoc] using paid ⟨k.val, by omega⟩
  have p1 : integral l r (M*(P*X^k.val)*X) = 0 := by
    simpa only [Fin.val_mk,pow_succ,mul_assoc] using paid ⟨k.val+1, by omega⟩
  simpa only [mul_assoc] using addLinearMask (t := t) p0 p1

private theorem extendMaskOne {l r : K} {M P : K[X]}
    (paid : ∀ j : Fin 2, integral l r (M*P*X^j.val) = 0)
    (t : K) : integral l r (M*(X-C t)*P) = 0 := by
  have p0 := paid ⟨0, by decide⟩
  have p1 := paid ⟨1, by decide⟩
  change integral l r (M*P*X^0) = 0 at p0
  change integral l r (M*P*X^1) = 0 at p1
  exact addLinearMask (t := t)
    (by simpa only [pow_zero,mul_one] using p0) (by simpa only [pow_one] using p1)

private theorem zeroWindowLeft {o l r : K} {B : K[X]}
    (L : integral o l B = 0) (R : integral o r B = 0) :
    integral l r B = 0 := by
  calc
    _ = integral o r B - integral o l B := by simp only [integral_apply]; ring
    _ = 0 := by rw [L,R,sub_zero]

private theorem zeroWindowRight {o l r : K} {B : K[X]}
    (L : integral l o B = 0) (R : integral r o B = 0) :
    integral l r B = 0 := by
  calc
    _ = integral l o B - integral r o B := by simp only [integral_apply]; ring
    _ = 0 := by rw [L,R,sub_zero]

private theorem variationsOfWeight {l r : K} {P W : K[X]} {m : ℕ}
    (pd : P.natDegree = 5) (lr : l < r) (wd : W.natDegree ≤ 3) (md : m ≤ 3)
    (signW : (∀ x ∈ Set.Ioo l r, 0 < W.eval x) ∨ (∀ x ∈ Set.Ioo l r, W.eval x < 0))
    (paid : ∀ k : Fin m, integral l r (W*P*X^k.val) = 0) :
    HasAlternationsOn P (Set.Ioo l r) m := by
  have pn : P ≠ 0 := by
    intro h
    simp [h] at pd
  have ps : P.natDegree < 19 := by omega
  have budget : W.natDegree + P.natDegree + (m-1) ≤ 19 := by omega
  rcases signW with pos | neg
  · exact HasAlternationsOn.of_grid lr
      (grid_variation_of_positive_moments lr pn ps budget pos paid)
  · refine HasAlternationsOn.of_grid lr (grid_variation_of_positive_moments
      (U := -W) lr pn ps (by simpa only [natDegree_neg] using budget) ?_ ?_)
    · intro x hx
      simpa only [eval_neg] using neg_pos.mpr (neg x hx)
    · intro k
      simp only [neg_mul,map_neg,paid k,neg_zero]

private theorem variationOfOneMoment {l r : K} {P W : K[X]}
    (pd : P.natDegree = 5) (lr : l < r) (wd : W.natDegree ≤ 3)
    (pos : ∀ x ∈ Set.Ioo l r, 0 < W.eval x) (paid : integral l r (W*P) = 0) :
    HasAlternationsOn P (Set.Ioo l r) 1 := by
  apply variationsOfWeight (m := 1) pd lr wd (by decide) (Or.inl pos)
  intro k
  have h : k.val = 0 := by have hk := k.isLt; omega
  simpa only [h,pow_zero,mul_one] using paid

private theorem variationsOfTwoWeights {l r : K} {P U V : K[X]}
    (pd : P.natDegree = 5) (lr : l < r) (ud : U.natDegree ≤ 3) (vd : V.natDegree ≤ 3)
    (up : ∀ x ∈ Set.Ioo l r, 0 < U.eval x) (vp : ∀ x ∈ Set.Ioo l r, 0 < V.eval x)
    (ratio : StrictMonoOn (fun x => U.eval x / V.eval x) (Set.Ioo l r) ∨
      StrictAntiOn (fun x => U.eval x / V.eval x) (Set.Ioo l r))
    (uz : integral l r (U*P) = 0) (vz : integral l r (V*P) = 0) :
    HasAlternationsOn P (Set.Ioo l r) 2 := by
  have pn : P ≠ 0 := by
    intro h
    simp [h] at pd
  exact HasAlternationsOn.of_grid lr (grid_variation_of_monotone_ratio
    lr pn (by omega) (by omega) (by omega) up vp ratio uz vz)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem risingRatio_eq (a b c d x : K) :
    (-leftThree a b).eval x / (-rightThree d c).eval x =
      x/(1-x) * ((x-b)/(x-d)) * ((a-x)/(c-x)) := by
  simp only [leftThree,leftTwo,rightThree,rightTwo,eval_neg,eval_mul,
    eval_sub,eval_X,eval_C,eval_one]
  rw [div_mul_div_comm,div_mul_div_comm]
  congr 1 <;> ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem fallingRatio_eq (a b c d x : K) :
    (leftThree a b).eval x / (rightThree d c).eval x =
      x/(x-c) * ((b-x)/(1-x)) * ((a-x)/(x-d)) := by
  simp only [leftThree,leftTwo,rightThree,rightTwo,eval_mul,eval_sub,eval_X,eval_C,eval_one]
  rw [div_mul_div_comm,div_mul_div_comm]
  congr 1 <;> ring

private theorem risingRatio {a b c d : K}
    (b0 : 0 < b) (c1 : c < 1) (db : d < b) (ca : c < a) :
    StrictMonoOn (fun x => (-leftThree a b).eval x / (-rightThree d c).eval x)
      (Set.Ioo b c) := by
  intro x hx y hy xy
  simp only [risingRatio_eq]
  have x1 := sub_pos.mpr (hx.2.trans c1)
  have y1 := sub_pos.mpr (hy.2.trans c1)
  have xd := sub_pos.mpr (db.trans hx.1)
  have yd := sub_pos.mpr (db.trans hy.1)
  have cx := sub_pos.mpr hx.2
  have cy := sub_pos.mpr hy.2
  have i : x/(1-x) < y/(1-y) :=
    (div_lt_div_iff₀ x1 y1).mpr (by nlinarith only [xy])
  have j : (x-b)/(x-d) < (y-b)/(y-d) :=
    (div_lt_div_iff₀ xd yd).mpr (by
      have p := mul_pos (sub_pos.mpr db) (sub_pos.mpr xy)
      nlinarith only [p])
  have k : (a-x)/(c-x) < (a-y)/(c-y) :=
    (div_lt_div_iff₀ cx cy).mpr (by
      have p := mul_pos (sub_pos.mpr ca) (sub_pos.mpr xy)
      nlinarith only [p])
  have ip : 0 < x/(1-x) := div_pos (b0.trans hx.1) x1
  have jp : 0 < (x-b)/(x-d) := div_pos (sub_pos.mpr hx.1) xd
  have jq : 0 < (y-b)/(y-d) := div_pos (sub_pos.mpr hy.1) yd
  have kq : 0 < (a-y)/(c-y) := div_pos (sub_pos.mpr (hy.2.trans ca)) cy
  exact mul_lt_mul_of_pos (mul_lt_mul_of_pos i j ip jq) k (mul_pos ip jp) kq

private theorem fallingRatio {a b c d : K}
    (c0 : 0 < c) (b1 : b < 1) (dc : d < c) (ba : b < a) :
    StrictAntiOn (fun x => (leftThree a b).eval x / (rightThree d c).eval x)
      (Set.Ioo c b) := by
  intro x hx y hy xy
  simp only [fallingRatio_eq]
  have xc := sub_pos.mpr hx.1
  have yc := sub_pos.mpr hy.1
  have x1 := sub_pos.mpr (hx.2.trans b1)
  have y1 := sub_pos.mpr (hy.2.trans b1)
  have xd := sub_pos.mpr (dc.trans hx.1)
  have yd := sub_pos.mpr (dc.trans hy.1)
  have da : d < a := dc.trans (hx.1.trans (hx.2.trans ba))
  have i : y/(y-c) < x/(x-c) :=
    (div_lt_div_iff₀ yc xc).mpr (by
      have p := mul_pos c0 (sub_pos.mpr xy)
      nlinarith only [p])
  have j : (b-y)/(1-y) < (b-x)/(1-x) :=
    (div_lt_div_iff₀ y1 x1).mpr (by
      have p := mul_pos (sub_pos.mpr b1) (sub_pos.mpr xy)
      nlinarith only [p])
  have k : (a-y)/(y-d) < (a-x)/(x-d) :=
    (div_lt_div_iff₀ yd xd).mpr (by
      have p := mul_pos (sub_pos.mpr da) (sub_pos.mpr xy)
      nlinarith only [p])
  have ip : 0 < y/(y-c) := div_pos (c0.trans hy.1) yc
  have jp : 0 < (b-y)/(1-y) := div_pos (sub_pos.mpr hy.2) y1
  have jq : 0 < (b-x)/(1-x) := div_pos (sub_pos.mpr hx.2) x1
  have kq : 0 < (a-x)/(x-d) := div_pos (sub_pos.mpr (hx.2.trans ba)) xd
  exact mul_lt_mul_of_pos (mul_lt_mul_of_pos i j ip jq) k (mul_pos ip jp) kq

set_option maxHeartbeats 450000 in
/-- Impossible local moments after localization; a>1 and d<0 are allowed.
This argument does not use global moments or the origin bit. -/
theorem OpposedQuinticWindows.local_impossible {P : K[X]} {z : Fin 4 → K} {e : ℕ}
    (h : OpposedQuinticWindows P z e)
    (ha : 0 < z 0) (hd : z 3 < 1)
    (hb : z 1 ∈ Set.Ioo (0:K) 1) (hc : z 2 ∈ Set.Ioo (0:K) 1) : False := by
  let a := z 0
  let b := z 1
  let c := z 2
  let d := z 3
  change 0 < a at ha
  change d < 1 at hd
  change b ∈ Set.Ioo (0:K) 1 at hb
  change c ∈ Set.Ioo (0:K) 1 at hc
  have abNe : a ≠ b := fun eq => (by decide : (0 : Fin 4) ≠ 1) (h.distinct eq)
  have cdNe : c ≠ d := fun eq => (by decide : (2 : Fin 4) ≠ 3) (h.distinct eq)
  have bcNe : b ≠ c := fun eq => (by decide : (1 : Fin 4) ≠ 2) (h.distinct eq)
  have impossible {l r : K} (alt : HasAlternationsOn P (Set.Ioo l r) 6) : False := by
    have low := alt.le_natDegree
    rw [h.degree] at low
    omega

  let LE2 := fun t : K => t=0 ∨ t=a ∨ t=b
  let RE2 := fun t : K => t=1 ∨ t=d ∨ t=c
  let LE3 := fun t : K => t=0 ∨ t=a ∨ t=b ∨ t=c
  let RE3 := fun t : K => t=1 ∨ t=d ∨ t=c ∨ t=b
  have L2a (k : Fin 2) : integral 0 a (leftTwo a*P*X^k.val)=0 := by
    simpa only [leftTwo] using (extendMaskTwo h.leftFirst a k)
  have R2d (k : Fin 2) : integral d 1 (rightTwo d*P*X^k.val)=0 := by
    simpa only [rightTwo] using (extendMaskTwo h.rightFirst d k)
  have L2at (t : K) (ht : LE2 t) (k : Fin 2) :
      integral 0 t (leftTwo a*P*X^k.val)=0 := by
    change t=0 ∨ t=a ∨ t=b at ht
    rcases ht with rfl | rfl | rfl
    · simp
    · exact L2a k
    · exact h.leftSecond k
  have R2at (t : K) (ht : RE2 t) (k : Fin 2) :
      integral t 1 (rightTwo d*P*X^k.val)=0 := by
    change t=1 ∨ t=d ∨ t=c at ht
    rcases ht with rfl | rfl | rfl
    · simp
    · exact R2d k
    · exact h.rightSecond k
  have L3at (t : K) (ht : LE3 t) : integral 0 t (leftThree a b*P)=0 := by
    change t=0 ∨ t=a ∨ t=b ∨ t=c at ht
    rcases ht with rfl | rfl | rfl | rfl
    · simp
    · exact extendMaskOne L2a b
    · exact extendMaskOne (L2at b (by simp [LE2])) b
    · exact h.leftThird
  have R3at (t : K) (ht : RE3 t) : integral t 1 (rightThree d c*P)=0 := by
    change t=1 ∨ t=d ∨ t=c ∨ t=b at ht
    rcases ht with rfl | rfl | rfl | rfl
    · simp
    · exact extendMaskOne R2d c
    · exact extendMaskOne (R2at c (by simp [RE2])) c
    · exact h.rightThird
  have L3 {l r : K} (hl : LE3 l) (hr : LE3 r) : integral l r (leftThree a b*P)=0 :=
    zeroWindowLeft (L3at l hl) (L3at r hr)
  have R3 {l r : K} (hl : RE3 l) (hr : RE3 r) : integral l r (rightThree d c*P)=0 :=
    zeroWindowRight (R3at l hl) (R3at r hr)

  have lFirst : HasAlternationsOn P (Set.Ioo 0 a) 3 := by
    refine variationsOfWeight (W := X) (m := 3) h.degree ha (by rw [natDegree_X]; decide)
      (by decide) (Or.inl ?_) h.leftFirst
    intro x hx
    simpa only [eval_X] using hx.1
  have rFirst : HasAlternationsOn P (Set.Ioo d 1) 3 := by
    refine variationsOfWeight (W := 1-X) (m := 3) h.degree hd (by rw [rightOne_degree]; decide)
      (by decide) (Or.inl ?_) h.rightFirst
    intro x hx
    simpa only [eval_sub,eval_one,eval_X] using sub_pos.mpr hx.2
  have lDouble {l r : K} (l0 : 0 ≤ l) (lr : l<r) (hl : LE2 l) (hr : LE2 r)
      (off : r≤a ∨ a≤l) : HasAlternationsOn P (Set.Ioo l r) 2 := by
    refine variationsOfWeight (W := leftTwo a) (m := 2) h.degree lr ((leftTwo_degree a).trans (by decide)) (by decide) ?_ ?_
    · rcases off with offL | offR
      · right
        intro x hx
        simp only [leftTwo,eval_mul,eval_sub,eval_X,eval_C]
        exact mul_neg_of_pos_of_neg (l0.trans_lt hx.1) (sub_neg.mpr (hx.2.trans_le offL))
      · left
        intro x hx
        simp only [leftTwo,eval_mul,eval_sub,eval_X,eval_C]
        exact mul_pos (l0.trans_lt hx.1) (sub_pos.mpr (offR.trans_lt hx.1))
    · intro k
      exact zeroWindowLeft (L2at l hl k) (L2at r hr k)
  have rDouble {l r : K} (r1 : r ≤ 1) (lr : l<r) (hl : RE2 l) (hr : RE2 r)
      (off : r≤d ∨ d≤l) : HasAlternationsOn P (Set.Ioo l r) 2 := by
    refine variationsOfWeight (W := rightTwo d) (m := 2) h.degree lr ((rightTwo_degree d).trans (by decide)) (by decide) ?_ ?_
    · rcases off with offL | offR
      · right
        intro x hx
        simp only [rightTwo,eval_mul,eval_sub,eval_one,eval_X,eval_C]
        exact mul_neg_of_pos_of_neg (sub_pos.mpr (hx.2.trans_le r1))
          (sub_neg.mpr (hx.2.trans_le offL))
      · left
        intro x hx
        simp only [rightTwo,eval_mul,eval_sub,eval_one,eval_X,eval_C]
        exact mul_pos (sub_pos.mpr (hx.2.trans_le r1)) (sub_pos.mpr (offR.trans_lt hx.1))
    · intro k
      exact zeroWindowRight (R2at l hl k) (R2at r hr k)

  let u := min a (min b c)
  let v := max b (max c d)
  have u0 : 0<u := lt_min ha (lt_min hb.1 hc.1)
  have ua : u≤a := min_le_left _ _
  have ub : u≤b := (min_le_right a (min b c)).trans (min_le_left b c)
  have uc : u≤c := (min_le_right a (min b c)).trans (min_le_right b c)
  have v1 : v<1 := max_lt hb.2 (max_lt hc.2 hd)
  have bv : b≤v := le_max_left _ _
  have cv : c≤v := (le_max_left c d).trans (le_max_right b (max c d))
  have dv : d≤v := (le_max_right c d).trans (le_max_right b (max c d))
  have uE : LE3 u := by
    rcases min_choice a (min b c) with hu | hu
    · exact Or.inr (Or.inl hu)
    · rcases min_choice b c with hb' | hc'
      · exact Or.inr (Or.inr (Or.inl (hu.trans hb')))
      · exact Or.inr (Or.inr (Or.inr (hu.trans hc')))
  have vE : RE3 v := by
    rcases max_choice b (max c d) with hv | hv
    · exact Or.inr (Or.inr (Or.inr hv))
    · rcases max_choice c d with hc' | hd'
      · exact Or.inr (Or.inr (Or.inl (hv.trans hc')))
      · exact Or.inr (Or.inl (hv.trans hd'))
  have lTail : HasAlternationsOn P (Set.Ioo 0 u) 1 := by
    refine variationOfOneMoment h.degree u0 (leftThree_degree a b) ?_ (L3at u uE)
    intro x hx
    simp only [leftThree,leftTwo,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hx.1 (sub_neg.mpr (hx.2.trans_le ua)))
      (sub_neg.mpr (hx.2.trans_le ub))
  have rTail : HasAlternationsOn P (Set.Ioo v 1) 1 := by
    refine variationOfOneMoment h.degree v1 (rightThree_degree d c) ?_ (R3at v vE)
    intro x hx
    simp only [rightThree,rightTwo,eval_mul,eval_sub,eval_X,eval_C,eval_one]
    exact mul_pos (mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr (dv.trans_lt hx.1)))
      (sub_pos.mpr (cv.trans_lt hx.1))

  -- Outward chronology would spend 3+2 on the same side, with 1 left over.
  have ba : b<a := by
    apply lt_of_not_ge
    intro ab
    have gap := lDouble ha.le (lt_of_le_of_ne ab abNe)
      (by simp [LE2]) (by simp [LE2]) (Or.inr le_rfl)
    have firstFive := lFirst.add_open gap ha.le le_rfl ab
    exact impossible (firstFive.add_open rTail hb.1.le bv v1.le)
  have dc : d<c := by
    apply lt_of_not_ge
    intro cd
    have gap := rDouble hd.le (lt_of_le_of_ne cd cdNe)
      (by simp [RE2]) (by simp [RE2]) (Or.inl le_rfl)
    have lastFive := gap.add_open rFirst cd le_rfl hd.le
    exact impossible (lTail.add_open lastFive u0.le uc hc.2.le)

  have l0b := lDouble (l:=0) le_rfl hb.1 (by simp [LE2]) (by simp [LE2]) (Or.inl ba.le)
  have lba := lDouble (r:=a) hb.1.le ba (by simp [LE2]) (by simp [LE2]) (Or.inl le_rfl)
  have rdc := rDouble (l:=d) hc.2.le dc (by simp [RE2]) (by simp [RE2]) (Or.inr le_rfl)
  have rc1 := rDouble (r:=1) le_rfl hc.2 (by simp [RE2]) (by simp [RE2]) (Or.inr dc.le)

  -- A disjoint 2+4 or 4+2 excludes the two separated middle layouts.
  have db : d<b := by
    apply lt_of_not_ge
    intro bd
    have rightFour := rdc.add_open rc1 dc.le le_rfl hc.2.le
    exact impossible (l0b.add_open rightFour hb.1.le bd hd.le)
  have ca : c<a := by
    apply lt_of_not_ge
    intro ac
    have leftFour := l0b.add_open lba hb.1.le le_rfl ba.le
    exact impossible (leftFour.add_open rc1 ha.le ac hc.2.le)

  rcases lt_or_gt_of_ne bcNe with bc | cb
  · -- b < c: both weights are negative before orientation; ratio increases.
    have lp := L3 (l:=b) (r:=c) (by simp [LE3]) (by simp [LE3])
    have rp := R3 (l:=b) (r:=c) (by simp [RE3]) (by simp [RE3])
    have middle : HasAlternationsOn P (Set.Ioo b c) 2 := by
      refine variationsOfTwoWeights (U := -leftThree a b) (V := -rightThree d c)
        h.degree bc (by simpa only [natDegree_neg] using leftThree_degree a b)
        (by simpa only [natDegree_neg] using rightThree_degree d c) ?_ ?_
        (Or.inl (risingRatio hb.1 hc.2 db ca)) ?_ ?_
      · intro x hx
        simp only [leftThree,leftTwo,eval_neg,eval_mul,eval_sub,eval_X,eval_C]
        exact neg_pos.mpr (mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (hb.1.trans hx.1) (sub_neg.mpr (hx.2.trans ca)))
          (sub_pos.mpr hx.1))
      · intro x hx
        simp only [rightThree,rightTwo,eval_neg,eval_mul,eval_sub,eval_X,eval_C,eval_one]
        exact neg_pos.mpr (mul_neg_of_pos_of_neg
          (mul_pos (sub_pos.mpr (hx.2.trans hc.2)) (sub_pos.mpr (db.trans hx.1)))
          (sub_neg.mpr hx.2))
      · rw [neg_mul,map_neg,lp,neg_zero]
      · rw [neg_mul,map_neg,rp,neg_zero]
    have leftFour := l0b.add_open middle hb.1.le le_rfl bc.le
    exact impossible (leftFour.add_open rc1 hc.1.le le_rfl hc.2.le)
  · -- c < b: both weights are positive; ratio decreases.
    have middle : HasAlternationsOn P (Set.Ioo c b) 2 := by
      refine variationsOfTwoWeights (U := leftThree a b) (V := rightThree d c)
        h.degree cb (leftThree_degree a b) (rightThree_degree d c) ?_ ?_
        (Or.inr (fallingRatio hc.1 hb.2 dc ba))
        (L3 (by simp [LE3]) (by simp [LE3])) (R3 (by simp [RE3]) (by simp [RE3]))
      · intro x hx
        simp only [leftThree,leftTwo,eval_mul,eval_sub,eval_X,eval_C]
        exact mul_pos_of_neg_of_neg
          (mul_neg_of_pos_of_neg (hc.1.trans hx.1) (sub_neg.mpr (hx.2.trans ba)))
          (sub_neg.mpr hx.2)
      · intro x hx
        simp only [rightThree,rightTwo,eval_mul,eval_sub,eval_X,eval_C,eval_one]
        exact mul_pos
          (mul_pos (sub_pos.mpr (hx.2.trans hb.2)) (sub_pos.mpr (dc.trans hx.1)))
          (sub_pos.mpr hx.1)
    have rightFour := rdc.add_open middle dc.le le_rfl cb.le
    exact impossible (rightFour.add_open lba (dc.trans cb).le le_rfl ba.le)

end
end RKCert.ReviewedNative.ERK19ZeroScalar
