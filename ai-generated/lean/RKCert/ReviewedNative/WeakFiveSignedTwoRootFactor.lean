module

public import RKCert.ReviewedNative.WeakFiveExteriorRootLayouts
public import RKCert.ReviewedNative.CrossedPositiveTailRoots

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact two-change factorization in one ordered field

The selected field fills gaps of its *own* mapped polynomial. This stronger
notion avoids any claim that the base image is order-dense or that positivity
proved only on the base automatically holds at algebraic samples.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.CrossedPositiveTailRoots
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def GapComplete (p : K[X]) : Prop :=
  ∀ {a b : K}, a < b → Opposite (p.eval a) (p.eval b) →
    ∃ x, a < x ∧ x < b ∧ p.IsRoot x

/-- Maximize the number of distinct real roots over ordered extensions.
If an opposite-sign gap in *that selected field* lacks a root, the same
single-gap factory increases this bounded count. -/
theorem self_gap_complete_extension (p : K[X]) :
    ∃ E : OrderedExtension K, GapComplete (p.map E.embed) := by
  classical
  let S := (Finset.range (p.natDegree+1)).filter
    (fun n => ∃ E : OrderedExtension K, (distinctRoots E p).card = n)
  have live (E : OrderedExtension K) : (distinctRoots E p).card ∈ S :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((distinctRoots_card_le E p).trans_lt (Nat.lt_succ_self _)), ⟨E,rfl⟩⟩
  have ne : S.Nonempty := ⟨_,live (identity K)⟩
  let n := S.max' ne
  obtain ⟨E, top⟩ := (Finset.mem_filter.mp (Finset.max'_mem S ne)).2
  refine ⟨E, ?_⟩
  intro a b ab opposite
  by_contra missing
  let I := identity E.carrier
  let Q := p.map E.embed
  have no : ¬ rootInGap I Q a b := by
    change ¬ ∃ x : E.carrier, a < x ∧ x < b ∧ (Q.map (RingHom.id _)).IsRoot x
    rw [Polynomial.map_id]
    exact missing
  obtain ⟨F, more⟩ := grow_distinctRoots
    RKCert.ReviewedNative.OrderedSingleGapRoot.singleGapFactory I Q a b ab opposite no
  have old : distinctRoots I Q = distinctRoots E p := by
    change (Q.map (RingHom.id _)).roots.toFinset = Q.roots.toFinset
    rw [Polynomial.map_id]
  have new : distinctRoots (followedBy E F) p = distinctRoots F Q := by
    simp [followedBy, Q, distinctRoots, map_map]
  have cap : (distinctRoots (followedBy E F) p).card ≤ n := Finset.le_max' S _ (live (followedBy E F))
  rw [old, ← new] at more
  change (distinctRoots E p).card = n at top
  exact (not_lt_of_ge cap) (top ▸ more)

theorem GapComplete.scale {p : K[X]} (base : GapComplete p) {v : K} (vn : v ≠ 0) :
    GapComplete (p*C v) := by
  intro a b ab opp
  have pr : (p.eval a*p.eval b) * (v*v) < 0 := by
    have eq : (p*C v).eval a * (p*C v).eval b = (p.eval a*p.eval b)*(v*v) := by
      simp only [eval_mul, eval_C]
      ring
    rw [← eq]
    exact mul_neg_iff.mpr opp
  have sg : Opposite (p.eval a) (p.eval b) := by
    apply mul_neg_iff.mp
    by_contra! nn
    exact (not_lt_of_ge (mul_nonneg nn (mul_self_nonneg v))) pr
  obtain ⟨x, al, br, rr⟩ := base ab sg
  exact ⟨x, al, br, by
    change (p*C v).eval x = 0
    rw [eval_mul, eval_C, show p.eval x=0 from rr, zero_mul]⟩

theorem alternations_scale_unit_iff {p : K[X]} {m : ℕ} {v : K} (vn : v ≠ 0) :
    HasAlternationsOn (p*C v) (Set.Ioo (0 : K) 1) m ↔
      HasAlternationsOn p (Set.Ioo (0 : K) 1) m := by
  have iffNeg (a b : K) :
      ((p*C v).eval a)*((p*C v).eval b)<0 ↔ p.eval a*p.eval b<0 := by
    have eq : (p*C v).eval a * (p*C v).eval b = (p.eval a*p.eval b)*(v*v) := by
      simp only [eval_mul, eval_C]
      ring
    rw [eq]
    constructor
    · intro h
      by_contra! nn
      exact (not_lt_of_ge (mul_nonneg nn (mul_self_nonneg v))) h
    · exact fun h => mul_neg_of_neg_of_pos h (mul_self_pos.mpr vn)
  constructor
  · intro h
    obtain ⟨xs, inc, inside, live, low⟩ := h.alternating_samples
    refine HasAlternationsOn.of_alternating_samples inc inside ⟨?_, ?_⟩ low
    · intro x hx qx
      exact live.nonzero x hx (by simp only [eval_mul, eval_C, qx, zero_mul])
    · exact live.jumps.imp (fun a b h => (iffNeg a b).mp h)
  · intro h
    obtain ⟨xs, inc, inside, live, low⟩ := h.alternating_samples
    refine HasAlternationsOn.of_alternating_samples inc inside ⟨?_, ?_⟩ low
    · intro x hx
      simp only [eval_mul, eval_C]
      exact mul_ne_zero (live.nonzero x hx) vn
    · exact live.jumps.imp (fun a b h => (iffNeg a b).mpr h)

structure SignedTwoRootFactor (p B : K[X]) (r s σ : K) : Prop where
  lo : 0 < r
  order : r < s
  hi : s < 1
  sign : σ = 1 ∨ σ = -1
  degree : B.natDegree = 2
  leading : B.leadingCoeff = σ
  algebra : p*C σ = B*((X-C r)*(X-C s))
  nonneg : ∀ x ∈ Set.Icc 0 1, 0 ≤ B.eval x

/-- Normalize the common sign of the two tails. The nonnegativity conclusion
is over the whole selected field, not just original sample images. -/
theorem signed_two_root_factor {p : K[X]} (mono : p.Monic) (deg : p.natDegree = 4)
    (gap : GapComplete p) (two : HasAlternationsOn p (Set.Ioo (0 : K) 1) 2)
    (noThree : ¬ HasAlternationsOn p (Set.Ioo (0 : K) 1) 3) :
    ∃ (B : K[X]) (r s σ : K), SignedTwoRootFactor p B r s σ := by
  classical
  obtain ⟨x, xo, xu, xp⟩ := finite_alternation_tuple (by decide) two
  let σ : K := if 0 < p.eval (x 0) then 1 else -1
  let Q := p * C σ
  have sg : σ=1 ∨ σ=(-1 : K) := by dsimp only [σ]; split <;> simp
  have sn : σ ≠ 0 := by
    rcases sg with h | h <;> rw [h] <;> norm_num
  have QG : GapComplete Q := gap.scale sn
  have Qnt : ¬ HasAlternationsOn Q (Set.Ioo (0 : K) 1) 3 :=
    fun a => noThree ((alternations_scale_unit_iff sn).mp a)
  have step0 : p.eval (x 0)*p.eval (x 1)<0 := xp 0
  have step1 : p.eval (x 1)*p.eval (x 2)<0 := xp 1
  have t0 : 0 < Q.eval (x 0) := by
    simp only [Q, eval_mul, eval_C, σ]
    rcases mul_neg_iff.mp step0 with h | h
    · simpa [h.1] using h.1
    · rw [if_neg (not_lt_of_ge h.1.le)]
      simpa only [mul_neg, mul_one, neg_pos] using h.1
  have step (a b : K) (h : p.eval a*p.eval b<0) : Q.eval a*Q.eval b<0 := by
    have alg : Q.eval a*Q.eval b = (p.eval a*p.eval b)*(σ*σ) := by
      simp only [Q, eval_mul, eval_C]
      ring
    rw [alg]
    exact mul_neg_of_neg_of_pos h (mul_self_pos.mpr sn)
  have t1 : Q.eval (x 1) < 0 := neg_of_mul_neg_right (step _ _ step0) t0.le
  have t2 : 0 < Q.eval (x 2) := pos_of_mul_neg_right (step _ _ step1) t1.le
  let A : Set K := {y | y ∈ Set.Ioo (0 : K) 1 ∧ y < x 1 ∧ 0 < Q.eval y}
  let N : Set K := {y | y ∈ Set.Ioo (0 : K) 1 ∧ Q.eval y < 0}
  let D : Set K := {y | y ∈ Set.Ioo (0 : K) 1 ∧ x 1 < y ∧ 0 < Q.eval y}
  have a0 : x 0 ∈ A := ⟨xu 0, xo (by decide), t0⟩
  have n1 : x 1 ∈ N := ⟨xu 1,t1⟩
  have d2 : x 2 ∈ D := ⟨xu 2, xo (by decide), t2⟩
  have left (a : K) (ha : a ∈ A) (b : K) (hb : b ∈ N) : a < b := by
    by_contra! le
    rcases le.lt_or_eq with less | eq
    · exact Qnt (three_changes_of_alternating_four Q hb.1 ha.1 (xu 1) (xu 2)
      less ha.2.1 d2.2.1 (Or.inr ⟨hb.2, ha.2.2⟩) (Or.inl ⟨ha.2.2,t1⟩) (Or.inr ⟨t1,t2⟩))
    · exact hb.2.not_ge (by simpa only [eq] using ha.2.2.le)
  have right (b : K) (hb : b ∈ N) (d : K) (hd : d ∈ D) : b < d := by
    by_contra! le
    rcases le.lt_or_eq with less | eq
    · exact Qnt (three_changes_of_alternating_four Q (xu 0) (xu 1) hd.1 hb.1
      a0.2.1 hd.2.1 less (Or.inl ⟨t0,t1⟩) (Or.inr ⟨t1,hd.2.2⟩) (Or.inl ⟨hd.2.2,hb.2⟩))
    · exact hb.2.not_ge (by simpa only [eq] using hd.2.2.le)
  let F := Q.roots.toFinset
  have qn : Q ≠ 0 := mul_ne_zero mono.ne_zero (C_ne_zero.mpr sn)
  have root {y : K} : y ∈ F ↔ Q.IsRoot y := by simp [F, Polynomial.mem_roots qn]
  obtain ⟨r, rr, low, ml⟩ := finite_strict_separator F A N id id ⟨_,a0⟩ ⟨_,n1⟩ (by
    intro a ha b hb
    obtain ⟨t,l,h,rt⟩ := QG (left a ha b hb) (Or.inl ⟨ha.2.2,hb.2⟩)
    exact ⟨t,root.mpr rt,l,h⟩)
  obtain ⟨s, sr, mr, high⟩ := finite_strict_separator F N D id id ⟨_,n1⟩ ⟨_,d2⟩ (by
    intro b hb d hd
    obtain ⟨t,l,h,rt⟩ := QG (right b hb d hd) (Or.inr ⟨hb.2,hd.2.2⟩)
    exact ⟨t,root.mpr rt,l,h⟩)
  have ord : r < s := (ml _ n1).trans (mr _ n1)
  have r0 : 0 < r := (xu 0).1.trans (low _ a0)
  have s1 : s < 1 := (high _ d2).trans (xu 2).2
  have pRoot {y : K} (h : Q.IsRoot y) : p.IsRoot y := by
    change Q.eval y = 0 at h
    simp only [Q, eval_mul, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_right sn
  obtain ⟨B₀, bm, bd, fac⟩ := monic_quadratic_of_two_roots p mono deg ord
    (pRoot (root.mp rr)) (pRoot (root.mp sr))
  let B := B₀*C σ
  have eq : Q = B*((X-C r)*(X-C s)) := by
    calc Q = (B₀*((X-C r)*(X-C s)))*C σ := congrArg (fun A => A*C σ) fac
         _ = _ := by dsimp only [B]; ring
  have val (y : K) : Q.eval y = B.eval y*((y-r)*(y-s)) := by
    simpa only [eval_mul, eval_sub, eval_X, eval_C] using congrArg (Polynomial.eval y) eq
  have openNonneg {y : K} (yi : y ∈ Set.Ioo 0 1) (yr : y≠r) (ys : y≠s) : 0 ≤ B.eval y := by
    by_contra! neg
    by_cases lr : y<r
    · have qv : Q.eval y<0 := (val y).trans_lt (mul_neg_of_neg_of_pos neg
        (mul_pos_of_neg_of_neg (sub_neg.mpr lr) (sub_neg.mpr (lr.trans ord))))
      exact (not_lt_of_ge lr.le) (ml y ⟨yi,qv⟩)
    · have ry : r<y := lt_of_le_of_ne (le_of_not_gt lr) yr.symm
      by_cases rs : y<s
      · have qv : 0<Q.eval y := (mul_pos_of_neg_of_neg neg
          (mul_neg_of_pos_of_neg (sub_pos.mpr ry) (sub_neg.mpr rs))).trans_eq (val y).symm
        rcases lt_trichotomy y (x 1) with lh | eh | rh
        · exact (not_lt_of_ge ry.le) (low y ⟨yi,lh,qv⟩)
        · exact (not_lt_of_ge qv.le) (by simpa only [eh] using t1)
        · exact (not_lt_of_ge rs.le) (high y ⟨yi,rh,qv⟩)
      · have sy : s<y := lt_of_le_of_ne (le_of_not_gt rs) ys.symm
        have qv : Q.eval y<0 := (val y).trans_lt (mul_neg_of_neg_of_pos neg
          (mul_pos (sub_pos.mpr ry) (sub_pos.mpr sy)))
        exact (not_lt_of_ge sy.le) (mr y ⟨yi,qv⟩)
  have allNonneg (y : K) (yi : y ∈ Set.Icc 0 1) : 0 ≤ B.eval y := by
    by_contra! b
    by_cases e0 : y=0
    · subst y
      obtain ⟨z,z0,zr,zz⟩ := eval_neg_somewhere_right B r0 b
      exact (not_lt_of_ge (openNonneg ⟨z0,zr.trans (ord.trans s1)⟩ zr.ne (zr.trans ord).ne)) zz
    by_cases e1 : y=1
    · subst y
      obtain ⟨z,sz,z1,zz⟩ := eval_neg_somewhere_left B s1 b
      exact (not_lt_of_ge (openNonneg ⟨(r0.trans ord).trans sz,z1⟩ (ord.trans sz).ne' sz.ne')) zz
    by_cases er : y=r
    · subst y
      obtain ⟨z,rz,zs,zz⟩ := eval_neg_somewhere_right B ord b
      exact (not_lt_of_ge (openNonneg ⟨r0.trans rz,zs.trans s1⟩ rz.ne' zs.ne)) zz
    by_cases es : y=s
    · subst y
      obtain ⟨z,sz,z1,zz⟩ := eval_neg_somewhere_right B s1 b
      exact (not_lt_of_ge (openNonneg ⟨(r0.trans ord).trans sz,z1⟩ (ord.trans sz).ne' sz.ne')) zz
    exact (not_lt_of_ge (openNonneg ⟨lt_of_le_of_ne yi.1 (Ne.symm e0),lt_of_le_of_ne yi.2 e1⟩ er es)) b
  refine ⟨B,r,s,σ,⟨r0,ord,s1,sg,(natDegree_mul_C sn).trans bd,?_ ,eq,allNonneg⟩⟩
  simp only [B,leadingCoeff_mul,leadingCoeff_C,bm.leadingCoeff,one_mul]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
