module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorDensityPencil
public import RKCert.ReviewedNative.PolynomialCertificateBernstein

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The literal finite rational root-strip obligation

The only unchecked input here is a finite condition on the existing rows:
ordered integer cages and sixteen rational coefficients per nonunit edge.
The two exact unit endpoint signs come from the actual roots, not the table.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial BigOperators

def edgeSense (upper : Bool) (i : Fin 7) : ℤ :=
  (if upper then -1 else 1)*(-1)^i.val

def edgeNumerator (row : ThreeInteriorCell) (upper : Bool) (i : Fin 7) : ℕ :=
  if upper then row.high i else row.low i

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def cellSL (r : ThreeInteriorCell) : K := gridCoord (2^r.rect.xDepth) r.rect.xIndex
def cellSU (r : ThreeInteriorCell) : K := gridCoord (2^r.rect.xDepth) (r.rect.xIndex+1)
def cellJL (r : ThreeInteriorCell) : K := gridCoord (2^r.rect.yDepth) r.rect.yIndex
def cellJU (r : ThreeInteriorCell) : K := gridCoord (2^r.rect.yDepth) (r.rect.yIndex+1)

def edgePoint (row : ThreeInteriorCell) (upper : Bool) (i : Fin 7) : K :=
  gridCoord 8192 (edgeNumerator row upper i)

def cellDefectEnd (row : ThreeInteriorCell) : Bool → K
  | false => defectBoxLow (cellSL row) (cellSU row) (cellJL row)
  | true => defectBoxHigh (cellSL row) (cellSU row) (cellJU row)

def signedDensityPencil (upper : Bool) (i : Fin 7) (x δ : K) : K[X] :=
  C (edgeSense upper i : K)*densityRootPencil x δ

def finiteStripCoefficient (row : ThreeInteriorCell) (edgeUpper : Bool) (i : Fin 7)
    (δUpper : Bool) (k : Fin 8) : ℚ :=
  bernsteinCoeff
    (intervalPullback
      (signedDensityPencil edgeUpper i (edgePoint row edgeUpper i) (cellDefectEnd row δUpper))
      (cellSL row) (cellSU row))
    7 k.val

/-- Literal finite statement needed from the 1212-row corpus. The
coefficients refer to the true polynomial determinants over ℚ, rather
than an arbitrary real-field sign assumption. -/
structure ThreeInteriorFiniteStripRows (rows : List ThreeInteriorCell) : Prop where
  densityIndex : ∀ r ∈ rows, r.rect.xIndex < 2^r.rect.xDepth
  defectIndex : ∀ r ∈ rows, r.rect.yIndex < 2^r.rect.yDepth
  strict : ∀ r ∈ rows, ∀ i, r.low i < r.high i
  top : ∀ r ∈ rows, ∀ i, r.high i ≤ 8192
  separated : ∀ r ∈ rows, ∀ ⦃i j⦄, i < j → r.high i < r.low j
  coefficients : ∀ r ∈ rows, ∀ (upper : Bool) (i : Fin 7),
    edgeNumerator r upper i ≠ 0 → edgeNumerator r upper i ≠ 8192 →
    ∀ (δUpper : Bool) (k : Fin 8), 0 < finiteStripCoefficient r upper i δUpper k

private theorem closedCoord {den i : ℕ} (dp : 0 < den) (bound : i ≤ den) :
    gridCoord (K := K) den i ∈ Set.Icc 0 1 := by
  unfold gridCoord
  have d : (0:K) < (den:K) := Nat.cast_pos.mpr dp
  refine ⟨div_nonneg (Nat.cast_nonneg _) d.le,(div_le_iff₀ d).2 ?_⟩
  rw [one_mul]
  exact Nat.cast_le.mpr bound

theorem ThreeInteriorFiniteStripRows.unit_bounds {rows : List ThreeInteriorCell}
    (A : ThreeInteriorFiniteStripRows rows) {r : ThreeInteriorCell} (hr : r ∈ rows) :
    cellSL (K := K) r ∈ Set.Icc 0 1 ∧ cellSU (K := K) r ∈ Set.Icc 0 1 ∧
      cellJL (K := K) r ∈ Set.Icc 0 1 ∧ cellJU (K := K) r ∈ Set.Icc 0 1 := by
  have px : 0 < (2:ℕ)^r.rect.xDepth := pow_pos (by decide) _
  have py : 0 < (2:ℕ)^r.rect.yDepth := pow_pos (by decide) _
  exact ⟨closedCoord px (A.densityIndex r hr).le,closedCoord px (A.densityIndex r hr),
    closedCoord py (A.defectIndex r hr).le,closedCoord py (A.defectIndex r hr)⟩

private theorem edge_zero_index {rows : List ThreeInteriorCell} (A : ThreeInteriorFiniteStripRows rows)
    {r : ThreeInteriorCell} (hr : r ∈ rows) {upper : Bool} {i : Fin 7}
    (h : edgeNumerator r upper i = 0) : upper = false ∧ i = 0 := by
  cases upper
  · refine ⟨rfl,?_⟩
    change r.low i = 0 at h
    by_contra! ni
    have first : (0:Fin 7) < i := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ni)
    have sep := A.separated r hr first
    rw [h] at sep
    exact (Nat.not_lt_zero _) sep
  · change r.high i = 0 at h
    have strict := A.strict r hr i
    omega

private theorem edge_one_index {rows : List ThreeInteriorCell} (A : ThreeInteriorFiniteStripRows rows)
    {r : ThreeInteriorCell} (hr : r ∈ rows) {upper : Bool} {i : Fin 7}
    (h : edgeNumerator r upper i = 8192) : upper = true ∧ i = Fin.last 6 := by
  cases upper
  · change r.low i = 8192 at h
    have strict := A.strict r hr i
    have top := A.top r hr i
    omega
  · refine ⟨rfl,?_⟩
    change r.high i = 8192 at h
    by_contra! ni
    have last : i < Fin.last 6 := lt_of_le_of_ne (Fin.le_last _) ni
    have sep := A.separated r hr last
    have strict := A.strict r hr (Fin.last 6)
    have top := A.top r hr (Fin.last 6)
    omega

private theorem alternatingSense (i : Fin 7) :
    (edgeSense false i = 1 ∧ edgeSense true i = -1) ∨
      (edgeSense false i = -1 ∧ edgeSense true i = 1) := by
  fin_cases i <;> decide

private theorem gridCoord_rat (d i : ℕ) :
    gridCoord (K := K) d i = ((gridCoord d i : ℚ) : K) := by
  simp [gridCoord]

private theorem cellSL_rat (r : ThreeInteriorCell) : cellSL (K := K) r = ((cellSL r : ℚ) : K) :=
  gridCoord_rat _ _
private theorem cellSU_rat (r : ThreeInteriorCell) : cellSU (K := K) r = ((cellSU r : ℚ) : K) :=
  gridCoord_rat _ _
private theorem cellJL_rat (r : ThreeInteriorCell) : cellJL (K := K) r = ((cellJL r : ℚ) : K) :=
  gridCoord_rat _ _
private theorem cellJU_rat (r : ThreeInteriorCell) : cellJU (K := K) r = ((cellJU r : ℚ) : K) :=
  gridCoord_rat _ _

private theorem edgePoint_rat (r : ThreeInteriorCell) (upper : Bool) (i : Fin 7) :
    edgePoint (K := K) r upper i = ((edgePoint r upper i : ℚ) : K) :=
  gridCoord_rat _ _

private theorem cellDefectEnd_rat (r : ThreeInteriorCell) (hi : Bool) :
    cellDefectEnd (K := K) r hi = ((cellDefectEnd r hi : ℚ) : K) := by
  cases hi
  · change defectBoxLow (cellSL r) (cellSU r) (cellJL r) =
      ((defectBoxLow (cellSL r) (cellSU r) (cellJL r) : ℚ) : K)
    rw [cellSL_rat,cellSU_rat,cellJL_rat,defectBoxLow_rat]
  · change defectBoxHigh (cellSL r) (cellSU r) (cellJU r) =
      ((defectBoxHigh (cellSL r) (cellSU r) (cellJU r) : ℚ) : K)
    rw [cellSL_rat,cellSU_rat,cellJU_rat,defectBoxHigh_rat]

private theorem pullback_rat (p : ℚ[X]) (l u : ℚ) :
    (intervalPullback p l u).map (Rat.castHom K) =
      intervalPullback (p.map (Rat.castHom K)) (l : K) (u : K) := by
  simp only [intervalPullback,Polynomial.map_comp,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_sub, _root_.map_sub] <;> rfl

private theorem coeff_rat (p : ℚ[X]) (N k : ℕ) :
    bernsteinCoeff (p.map (Rat.castHom K)) N k = ((bernsteinCoeff p N k : ℚ) : K) := by
  let f : ℚ →+* K := Rat.castHom K
  unfold bernsteinCoeff
  change (∑ j ∈ Finset.range (N+1), (p.map f).coeff j * ((k.choose j : K)/(N.choose j : K))) =
    f (∑ j ∈ Finset.range (N+1), p.coeff j * ((k.choose j : ℚ)/(N.choose j : ℚ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.coeff_map,_root_.map_mul,map_div₀,map_natCast]

private theorem signedDensityPencil_rat (upper : Bool) (i : Fin 7) (x δ : ℚ) :
    (signedDensityPencil upper i x δ).map (Rat.castHom K) =
      signedDensityPencil upper i (x : K) (δ : K) := by
  have h : (Rat.castHom K) (edgeSense upper i : ℚ) = (edgeSense upper i : K) :=
    Rat.cast_intCast _
  simp only [signedDensityPencil,Polynomial.map_mul,Polynomial.map_C,densityRootPencil_rat,h]

private theorem finite_coefficient_cast (row : ThreeInteriorCell) (edgeUpper : Bool)
    (i : Fin 7) (δUpper : Bool) (k : Fin 8) :
    bernsteinCoeff
      (intervalPullback
        (signedDensityPencil edgeUpper i (edgePoint (K := K) row edgeUpper i)
          (cellDefectEnd row δUpper))
        (cellSL row) (cellSU row)) 7 k.val =
      (finiteStripCoefficient row edgeUpper i δUpper k : K) := by
  have eq : (intervalPullback
      (signedDensityPencil edgeUpper i (edgePoint (K:=ℚ) row edgeUpper i) (cellDefectEnd row δUpper))
      (cellSL row) (cellSU row)).map (Rat.castHom K) =
        intervalPullback
          (signedDensityPencil edgeUpper i (edgePoint (K:=K) row edgeUpper i) (cellDefectEnd row δUpper))
          (cellSL row) (cellSU row) := by
    rw [pullback_rat,signedDensityPencil_rat,← edgePoint_rat,← cellDefectEnd_rat,
      ← cellSL_rat,← cellSU_rat]
  rw [← eq,coeff_rat] <;> rfl

open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.FiniteGaussianNodalLift

private theorem finite_edge_at_bias {rows : List ThreeInteriorCell}
    (A : ThreeInteriorFiniteStripRows rows) {r : ThreeInteriorCell} (hr : r ∈ rows)
    {s : K} (sc : s ∈ Set.Icc (cellSL r) (cellSU r))
    (edgeUpper : Bool) (i : Fin 7)
    (n0 : edgeNumerator r edgeUpper i ≠ 0) (n1 : edgeNumerator r edgeUpper i ≠ 8192)
    (bias : Bool) :
    0 < (edgeSense edgeUpper i : K) *
      (actualPencil s (cellDefectEnd r bias)).eval (edgePoint r edgeUpper i) := by
  let T := signedDensityPencil edgeUpper i (edgePoint (K:=K) r edgeUpper i) (cellDefectEnd r bias)
  have td : T.natDegree ≤ 7 :=
    (natDegree_C_mul_le _ _).trans (densityRootPencil_degree _ _)
  have ck (k : ℕ) (hk : k ≤ 7) :
      0 < bernsteinCoeff (intervalPullback T (cellSL r) (cellSU r)) 7 k := by
    let j : Fin 8 := ⟨k,Nat.lt_succ_of_le hk⟩
    have cmp : 0 < (finiteStripCoefficient r edgeUpper i bias j : K) :=
      Rat.cast_pos.mpr (A.coefficients r hr edgeUpper i n0 n1 bias j)
    have e := finite_coefficient_cast (K := K) r edgeUpper i bias j
    change bernsteinCoeff (intervalPullback T (cellSL r) (cellSU r)) 7 k =
      (finiteStripCoefficient r edgeUpper i bias j : K) at e
    rwa [← e] at cmp
  have h : 0 < T.eval s := interval_lt_eval_of_bernsteinCoeff td sc ck
  simpa only [T,signedDensityPencil,eval_mul,eval_C,densityRootPencil_eval] using h

/-- Strict alternating signs throughout the entire closed row.
Numerators 0 or 8192 use the forced first/last root order. -/
theorem actual_edge_signs_of_finite_row {rows : List ThreeInteriorCell}
    (A : ThreeInteriorFiniteStripRows rows) {r : ThreeInteriorCell} (hr : r ∈ rows)
    {s j δ : K} (ads : InDyadicRect r.rect s j)
    (δExpr : δ = mix (compactLower s) (compactUpper s) j)
    (leftEnd : 0 < (actualPencil s δ).eval 0)
    (rightEnd : (actualPencil s δ).eval 1 < 0) :
    ∀ (upper : Bool) (i : Fin 7),
      0 < (edgeSense upper i : K)*(actualPencil s δ).eval (edgePoint r upper i) := by
  have sc : s ∈ Set.Icc (cellSL r) (cellSU r) := ads.1
  have jc : j ∈ Set.Icc (cellJL r) (cellJU r) := ads.2
  have δRange : δ ∈ Set.Icc (cellDefectEnd r false) (cellDefectEnd r true) := by
    obtain ⟨sl,su,jl,ju⟩ := A.unit_bounds (K := K) hr
    rw [δExpr]
    exact defect_enclosed sc jc sl su jl ju
  intro upper i
  by_cases z : edgeNumerator r upper i = 0
  · obtain ⟨u,k⟩ := edge_zero_index A hr z
    have sig : edgeSense upper i = 1 := by rw [u,k] <;> decide
    have endp : edgePoint (K := K) r upper i = 0 := by simp [edgePoint,z,gridCoord]
    rw [endp,sig,Int.cast_one,one_mul]
    exact leftEnd
  by_cases one : edgeNumerator r upper i = 8192
  · obtain ⟨u,k⟩ := edge_one_index A hr one
    have sig : edgeSense upper i = -1 := by rw [u,k] <;> decide
    have endp : edgePoint (K := K) r upper i = 1 := by norm_num [edgePoint,one,gridCoord]
    rw [endp,sig,Int.cast_neg,Int.cast_one,neg_one_mul]
    exact neg_pos.mpr rightEnd
  let x := edgePoint (K:=K) r upper i
  let g (d : K) := (edgeSense upper i : K)*(actualPencil s d).eval x
  have affine (a b v : K) : g (mix a b v) = mix (g a) (g b) v := by
    simp only [g,actualPencil_eval]
    unfold mix
    ring
  have l : 0 < g (cellDefectEnd r false) := finite_edge_at_bias A hr sc upper i z one false
  have h : 0 < g (cellDefectEnd r true) := finite_edge_at_bias A hr sc upper i z one true
  obtain ⟨t,tc,eq⟩ := exists_unit_mix δRange
  change 0 < g δ
  rw [eq,affine]
  exact mixClosed_strictLower (0:K) tc.1 tc.2 l h

/-- The fixed strict alternating signs provide the reviewed strip interface. -/
theorem actual_strips_of_finite_row {rows : List ThreeInteriorCell}
    (A : ThreeInteriorFiniteStripRows rows) {r : ThreeInteriorCell} (hr : r ∈ rows)
    {s j δ : K} (ads : InDyadicRect r.rect s j)
    (δExpr : δ = mix (compactLower s) (compactUpper s) j)
    (leftEnd : 0 < (actualPencil s δ).eval 0)
    (rightEnd : (actualPencil s δ).eval 1 < 0) :
    SignStrips (actualPencil s δ) r.lowCoord r.highCoord := by
  let F := actualPencil s δ
  have edge := actual_edge_signs_of_finite_row A hr ads δExpr leftEnd rightEnd
  have ord : StrictMono (gridCoord (K := K) 8192) := gridCoord_strictMono (by decide)
  refine ⟨fun i => (ord (A.strict r hr i)).le,fun i j ij => ord (A.separated r hr ij),?_⟩
  intro i
  have lo : 0 < (edgeSense false i : K)*F.eval (r.lowCoord i) := edge false i
  have hi : 0 < (edgeSense true i : K)*F.eval (r.highCoord i) := edge true i
  rcases alternatingSense i with ⟨l,h⟩ | ⟨l,h⟩
  · rw [l,Int.cast_one,one_mul] at lo
    rw [h,Int.cast_neg,Int.cast_one,neg_one_mul] at hi
    exact Or.inr ⟨lo.le,(neg_pos.mp hi).le⟩
  · rw [l,Int.cast_neg,Int.cast_one,neg_one_mul] at lo
    rw [h,Int.cast_one,one_mul] at hi
    exact Or.inl ⟨(neg_pos.mp lo).le,hi.le⟩

/-- This is the exact pencil callback of the original ThreeInterior bridge.
No physical assumption is imported from a table; the only argument is
the finite rational strip receipt for the existing corpus. -/
theorem threeInterior_pencilReceipt_of_finite_rows {rows : List ThreeInteriorCell}
    (A : ThreeInteriorFiniteStripRows rows) : ThreeInteriorPencilReceipt (K := K) rows := by
  intro s r m w H wor μ μpos law
  obtain ⟨ω,wp,scaled⟩ := actual_sorted_scaled_rule w wor μpos law
  let β := w.sites r m
  have inside (i : Fin 7) : β i ∈ Set.Ioo 0 1 := H.sites_inside (w.labels i)
  have ss : s ∈ Set.Icc 0 1 := ⟨H.parameter.1,H.parameter.2.le⟩
  let δ := actualDefect s β ω
  let j := compactCoordinate s δ
  let F := actualPencil s δ
  have gap := actualDefect_strict ss wor.injective inside wp scaled
  have coords := compactCoordinate_spec ss gap.1 gap.2
  have signs := actualPencil_unit_end_signs wor.injective inside wp scaled
  have nonzero : F ≠ 0 := by
    intro e
    have z : 0 < F.eval 0 := signs.1
    rw [e,eval_zero] at z
    exact (lt_irrefl (0:K)) z
  refine ⟨j,F,coords.1,nonzero,actualPencil_degree scaled,actualPencil_roots scaled,?_⟩
  intro row hr hd
  exact actual_strips_of_finite_row A hr hd coords.2 signs.1 signs.2

end
end RKCert.ReviewedNative.ThreeInteriorPencil
