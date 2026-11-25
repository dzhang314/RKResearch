module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRationalCover
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Ratio receipts for the one-sided weak-four polynomial pencil

The ordinary, low-fitting and high-fitting cases share one signed axis box.
The exterior coordinate is projectivized before bounding it. These lemmas
consume only rational endpoint inequalities and the exact Vieta equality.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial Set
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.OrderedRootGapSaturation (OrderedExtension)
open RKCert.ReviewedNative.PolynomialCertificate
open scoped BigOperators

universe u

structure RatBand where
  lo : ℚ
  hi : ℚ

def RationalStripFrame.band {n : ℕ} (A : RationalStripFrame n) (i : Fin n) : RatBand :=
  ⟨A.lower i,A.upper i⟩

def RationalStripFrame.parameterBand {n : ℕ} (A : RationalStripFrame n) (den : ℕ) : RatBand :=
  ⟨gridCoord den A.span.1,gridCoord den A.span.2⟩

def AxisBox.band {m : ℕ} (B : AxisBox m) (i : Fin m) : RatBand :=
  ⟨B.lower i,B.upper i⟩

abbrev RatBand.Contains (C D : RatBand) : Prop := C.lo≤D.lo ∧ D.hi≤C.hi

def RatBand.compact (A R : RatBand) : RatBand :=
  ⟨R.lo/(A.hi+R.lo),R.hi/(A.lo+R.hi)⟩

abbrev RatBand.positiveCompact (A R : RatBand) : Prop :=
  0≤A.lo ∧ 0≤R.lo ∧ 0<A.hi+R.lo ∧ 0<A.lo+R.hi

def RatBand.nonnegativeMul (A R : RatBand) : RatBand :=
  ⟨A.lo*R.lo,A.hi*R.hi⟩

def RatBand.highRatio (V W R : RatBand) : RatBand :=
  ⟨V.lo*R.lo/W.hi,
    if 0<W.lo then min R.hi (V.hi*R.hi/W.lo) else R.hi⟩

def RatBand.unit : RatBand := ⟨1,1⟩

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def RatBand.Mem (R : RatBand) (r : K) : Prop := r∈Icc (R.lo:K) (R.hi:K)

theorem RatBand.Mem.of_containment {A B : RatBand} (h : A.Contains B) {r : K}
    (z : B.Mem r) : A.Mem r :=
  ⟨(Rat.cast_le.mpr h.1).trans z.1,z.2.trans (Rat.cast_le.mpr h.2)⟩

theorem RatBand.nonnegativeMul_mem {A B : RatBand} (a : 0≤A.lo) (b : 0≤B.lo)
    {x y : K} (hx : A.Mem x) (hy : B.Mem y) :
    (A.nonnegativeMul B).Mem (x*y) := by
  have ax : (0:K)≤x := (by exact_mod_cast a : (0:K)≤(A.lo:K)).trans hx.1
  have by' : (0:K)≤y := (by exact_mod_cast b : (0:K)≤(B.lo:K)).trans hy.1
  unfold RatBand.Mem RatBand.nonnegativeMul
  simp only [Rat.cast_mul]
  exact ⟨mul_le_mul hx.1 hy.1 (by exact_mod_cast b) ax,
    mul_le_mul hx.2 hy.2 by' (ax.trans hx.2)⟩

theorem RatBand.compact_mem {A R : RatBand} (D : A.positiveCompact R)
    {a r : K} (aR : 0<a+r) (ha : A.Mem a) (hr : R.Mem r) :
    (A.compact R).Mem (r/(a+r)) := by
  have a0 : (0:K)≤(A.lo:K) := by exact_mod_cast D.1
  have r0 : (0:K)≤(R.lo:K) := by exact_mod_cast D.2.1
  have d1 : (0:K)<(A.hi:K)+(R.lo:K) := by exact_mod_cast D.2.2.1
  have d2 : (0:K)<(A.lo:K)+(R.hi:K) := by exact_mod_cast D.2.2.2
  simpa only [RatBand.Mem,Set.mem_Icc,RatBand.compact,Rat.cast_div,Rat.cast_add] using
    compactRatio_bounds a0 r0 ha hr d1 d2 aR

theorem RatBand.highRatio_mem {V W R : RatBand} (v0 : 0≤V.lo) (r0 : 0≤R.lo)
    {v e r : K} (vp : 0<v) (he : 1≤e)
    (hv : V.Mem v) (hw : W.Mem (v*e)) (hr : R.Mem r) :
    (V.highRatio W R).Mem (r/e) := by
  have ep : 0<e := zero_lt_one.trans_le he
  have w : 0<v*e := mul_pos vp ep
  have wh : 0<(W.hi:K) := w.trans_le hw.2
  have nuc := RatBand.nonnegativeMul_mem v0 r0 hv hr
  have lo : (0:K)≤(V.lo:K)*(R.lo:K) := mul_nonneg (by exact_mod_cast v0) (by exact_mod_cast r0)
  have h1 : r/e = (v*r)/(v*e) := (mul_div_mul_left _ _ vp.ne').symm
  have h2 : r/e ≤ (R.hi:K) := by
    have rp : 0≤r := (by exact_mod_cast r0 : (0:K)≤(R.lo:K)).trans hr.1
    apply le_trans _ hr.2
    apply (div_le_iff₀ ep).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he rp
  change ((V.lo*R.lo/W.hi:ℚ):K)≤r/e ∧
    r/e≤((if 0<W.lo then min R.hi (V.hi*R.hi/W.lo) else R.hi : ℚ):K)
  constructor
  · rw [Rat.cast_div,Rat.cast_mul,h1]
    exact (div_le_div_of_nonneg_left lo w hw.2).trans
      ((div_le_div_iff_of_pos_right w).2 (by simpa only [RatBand.nonnegativeMul,Rat.cast_mul] using nuc.1))
  · by_cases p : 0<W.lo
    · rw [if_pos p,Rat.cast_min]
      refine le_min h2 ?_
      rw [Rat.cast_div,Rat.cast_mul,h1]
      have wp : 0<(W.lo:K) := by exact_mod_cast p
      have n : (v*r)≤(V.hi:K)*(R.hi:K) := by
        simpa only [RatBand.nonnegativeMul,Rat.cast_mul] using nuc.2
      exact ((div_le_div_iff_of_pos_right w).2 n).trans
        (div_le_div_of_nonneg_left (le_trans (mul_nonneg vp.le
          ((by exact_mod_cast r0 : (0:K)≤(R.lo:K)).trans hr.1)) n) wp hw.1)
    · simpa only [if_neg p] using h2

end

abbrev ordinaryCoordOK {m : ℕ} (B : AxisBox m) (i : Fin m) (A R : RatBand) : Prop :=
  B.forms i=.ordinary ∧ A.positiveCompact R ∧ (B.band i).Contains (A.compact R)

abbrev lowCoordOK {m : ℕ} (B : AxisBox m) (i : Fin m) (V A W : RatBand) : Prop :=
  let D := V.nonnegativeMul A
  B.forms i=.lowFit ∧ 0≤V.lo ∧ 0≤A.lo ∧ W.positiveCompact D ∧
    (B.band i).Contains (W.compact D)

abbrev highFitCoordOK {m : ℕ} (B : AxisBox m) (i : Fin m) (V A W : RatBand) : Prop :=
  B.forms i=.highFit ∧ 0≤V.lo ∧ 0≤A.lo ∧ (B.band i).Contains (V.highRatio W A)

abbrev highStopCoordOK {m : ℕ} (B : AxisBox m) (i : Fin m) (V R W : RatBand) : Prop :=
  let Z := V.highRatio W R
  B.forms i=.ordinary ∧ 0≤V.lo ∧ 0≤R.lo ∧ RatBand.unit.positiveCompact Z ∧
    (B.band i).Contains (RatBand.unit.compact Z)

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def RealizableCoord {m : ℕ} (B : AxisBox m) (i : Fin m) (a r : K) : Prop :=
  ∃ x scale : K, (B.band i).Mem x ∧ scale≠0 ∧
    C a*X-C r = C scale*(B.forms i).poly x

theorem ordinaryCoord_realizable {m : ℕ} {B : AxisBox m} {i : Fin m} {A R : RatBand}
    (ok : ordinaryCoordOK B i A R) {a r : K}
    (ha : A.Mem a) (hr : R.Mem r) (ap : 0<a) :
    RealizableCoord B i a r := by
  have rn : 0≤r := (by exact_mod_cast ok.2.1.2.1 : (0:K)≤(R.lo:K)).trans hr.1
  have d := add_pos_of_pos_of_nonneg ap rn
  refine ⟨r/(a+r),a+r,RatBand.Mem.of_containment ok.2.2 (RatBand.compact_mem ok.2.1 d ha hr),
    d.ne',?_⟩
  rw [ok.1,compactOrdinary_poly]
  exact ordinaryFactor_scale d.ne'

theorem lowCoord_realizable {m : ℕ} {B : AxisBox m} {i : Fin m} {V A W : RatBand}
    (ok : lowCoordOK B i V A W) {v a e : K} (vp : 0<v) (ap : 0<a) (ep : e≤0)
    (hv : V.Mem v) (ha : A.Mem a) (hw : W.Mem (-v*e)) :
    RealizableCoord B i a e := by
  have D := RatBand.nonnegativeMul_mem ok.2.1 ok.2.2.1 hv ha
  have d : 0<a-e := sub_pos.mpr (ep.trans_lt ap)
  have s : v*a+(-v*e)=v*(a-e) := by ring
  have sn : 0<(-v*e)+v*a := by rw [add_comm,s]; exact mul_pos vp d
  have h := RatBand.compact_mem ok.2.2.2.1 sn hw D
  have f : v*a/((-v*e)+v*a)=a/(a-e) := by
    rw [add_comm,s,mul_div_mul_left _ _ vp.ne']
  rw [f] at h
  refine ⟨a/(a-e),a-e,RatBand.Mem.of_containment ok.2.2.2.2 h,d.ne',?_⟩
  rw [ok.1,compactLowFit_poly]
  exact lowFitFactor_scale d.ne'

theorem highFitCoord_realizable {m : ℕ} {B : AxisBox m} {i : Fin m} {V A W : RatBand}
    (ok : highFitCoordOK B i V A W) {v a e : K} (vp : 0<v) (ep : 1≤e)
    (hv : V.Mem v) (ha : A.Mem a) (hw : W.Mem (v*e)) :
    RealizableCoord B i a e := by
  have en : e≠0 := (zero_lt_one.trans_le ep).ne'
  refine ⟨a/e,-e,RatBand.Mem.of_containment ok.2.2.2
    (RatBand.highRatio_mem ok.2.1 ok.2.2.1 vp ep hv hw ha),neg_ne_zero.mpr en,?_⟩
  rw [ok.1,compactHighFit_poly]
  exact highFitFactor_scale en

theorem highStopCoord_realizable {m : ℕ} {B : AxisBox m} {i : Fin m} {V R W : RatBand}
    (ok : highStopCoordOK B i V R W) {v e r : K} (vp : 0<v) (ep : 1≤e)
    (hv : V.Mem v) (hr : R.Mem r) (hw : W.Mem (v*e)) :
    RealizableCoord B i e r := by
  have pe : 0<e := zero_lt_one.trans_le ep
  have r0 : 0≤r := (by exact_mod_cast ok.2.2.1 : (0:K)≤(R.lo:K)).trans hr.1
  have d : 0<e+r := add_pos_of_pos_of_nonneg pe r0
  have rE := RatBand.highRatio_mem ok.2.1 ok.2.2.1 vp ep hv hw hr
  have one : RatBand.unit.Mem (1:K) := by simp [RatBand.Mem,RatBand.unit]
  have nz : 0<(1:K)+r/e := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg r0 pe.le)
  have box := RatBand.compact_mem ok.2.2.2.1 nz one rE
  have eq : (r/e)/(1+r/e) = r/(e+r) := by
    have h : 1+r/e=(e+r)/e := by rw [add_div,div_self pe.ne']
    rw [h,div_div_div_cancel_right₀ pe.ne' _ _]
  rw [eq] at box
  refine ⟨r/(e+r),e+r,RatBand.Mem.of_containment ok.2.2.2.2 box,d.ne',?_⟩
  rw [ok.1,compactOrdinary_poly]
  exact ordinaryFactor_scale d.ne'

theorem FitClaim.coordinates_of_ordinary_receipt {n m : ℕ} (C : FitClaim (Fin n) n m)
    (ok : ∀ i, ordinaryCoordOK C.box i (C.source.band C.rank.1) (C.source.band (C.order i)))
    {r : Fin n → K} (hr : C.source.nodes r) (ap : 0<r C.rank.1) : C.Coordinates r := by
  have a (i : Fin m) : RealizableCoord C.box i (r C.rank.1) (r (C.order i)) :=
    ordinaryCoord_realizable (ok i) (hr C.rank.1) (hr (C.order i)) ap
  choose x scale h using a
  exact ⟨x,scale,fun i => (h i).1,fun i => (h i).2.1,fun i => (h i).2.2⟩

end

end RKCert.ReviewedNative.WeakFourFirstOnly
