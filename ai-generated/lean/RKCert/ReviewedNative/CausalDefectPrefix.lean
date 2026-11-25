module

public import RKCert.ReviewedNative.OneOffDebut
public import RKCert.ReviewedNative.GradedPrimitives
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

import RKCert.NodalPrimitive
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.LinearAlgebra.Lagrange
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Causal localization of paid defect pivots

This is a local implication about a literal strict row and its unmodified
prefix. It makes no RK order, stage-count, or clean-row assumption. The
off portion of the clock receipt must be nonzero, and coherence is on
off copies only. Nonzero incoming residue and first physical occurrence
are kept separate: first occurrences certify the triangular columns.
-/
namespace RKResearch.Certified.Graded.DefectPrefix

open Polynomial OneOff RKCert.Endpoint
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {k : Fin s}

noncomputable def earlierOffRows (A : Matrix (Fin s) (Fin s) K) (k : Fin s) :
    Finset (Fin s) :=
  Finset.univ.filter fun i => i < k ∧ g A i ≠ 0

theorem mem_earlierOffRows {i : Fin s} :
    i ∈ earlierOffRows A k ↔ i < k ∧ g A i ≠ 0 := by
  simp [earlierOffRows]

noncomputable def earlierOffKnots (A : Matrix (Fin s) (Fin s) K) (k : Fin s) :
    Finset K :=
  (earlierOffRows A k).image (nodes A)

private noncomputable def offFibre (A : Matrix (Fin s) (Fin s) K) (k : Fin s)
    (x : K) : Finset (Fin s) :=
  (earlierOffRows A k).filter fun i => nodes A i = x

/-- The actual incoming quadratic-defect residue at an earlier off clock. -/
noncomputable def incomingOffResidue (A : Matrix (Fin s) (Fin s) K) (k : Fin s)
    (x : K) : K :=
  ∑ i ∈ (earlierOffRows A k).filter (fun i => nodes A i = x), A k i * g A i

noncomputable def activeOffKnots (A : Matrix (Fin s) (Fin s) K) (k : Fin s) :
    Finset K :=
  (earlierOffKnots A k).filter fun x => incomingOffResidue A k x ≠ 0

private theorem active_subset : activeOffKnots A k ⊆ earlierOffKnots A k :=
  Finset.filter_subset _ _

/-- Off copies of the same earlier clock carry the same defect. No condition
is placed on an earlier clean copy of that clock. -/
def FibreCoherent (A : Matrix (Fin s) (Fin s) K) (k : Fin s) : Prop :=
  ∀ {i l : Fin s}, i ∈ earlierOffRows A k → l ∈ earlierOffRows A k →
    nodes A i = nodes A l → g A i = g A l

noncomputable abbrev defectColumn (A : Matrix (Fin s) (Fin s) K) (P : K[X]) :
    Fin s → K :=
  diag (g A) (evalNodes A P)

/-- Polynomial form of the paid incoming clock-power probes through degree d. -/
abbrev PaidThrough (A : Matrix (Fin s) (Fin s) K) (k : Fin s) (d : ℕ) : Prop :=
  ∀ P : K[X], P.natDegree ≤ d → mat A (defectColumn A P) k = 0

/-- Restrict an actual strict row after dropping inputs on which its vector
is zero. This uses the same strict causal cut as prefixRestrict. -/
theorem mat_eq_off_sum (ha : ∀ i j, i ≤ j → A i j = 0) (v : Fin s → K)
    (z : ∀ i, i < k → g A i = 0 → v i = 0) :
    mat A v k = ∑ i ∈ earlierOffRows A k, A k i * v i := by
  rw [mat_apply, Matrix.mulVec, dotProduct]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  by_cases lt : i < k
  · have zi : g A i = 0 := by
      by_contra ni
      exact hi (mem_earlierOffRows.mpr ⟨lt,ni⟩)
    rw [z i lt zi,mul_zero]
  · rw [ha k i (le_of_not_gt lt),zero_mul]

private theorem sum_off_fibres (f : Fin s → K) :
    (∑ x ∈ earlierOffKnots A k, ∑ i ∈ offFibre A k x, f i) =
      ∑ i ∈ earlierOffRows A k, f i := by
  classical
  have maps : ∀ i ∈ earlierOffRows A k, nodes A i ∈ earlierOffKnots A k := by
    intro i hi
    change nodes A i ∈ (earlierOffRows A k).image (nodes A)
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  exact Finset.sum_fiberwise_of_maps_to (g := nodes A) maps f

private theorem mem_offFibre {i : Fin s} {x : K} :
    i ∈ offFibre A k x ↔ i ∈ earlierOffRows A k ∧ nodes A i = x := by
  simp only [offFibre,Finset.mem_filter]

private theorem row_defectColumn (ha : ∀ i j, i ≤ j → A i j = 0) (P : K[X]) :
    mat A (defectColumn A P) k =
      ∑ x ∈ earlierOffKnots A k, incomingOffResidue A k x * P.eval x := by
  calc
    _ = ∑ i ∈ earlierOffRows A k, A k i * defectColumn A P i :=
      mat_eq_off_sum ha _ (fun i _ z => by simp only [defectColumn,diag_apply,z,zero_mul])
    _ = ∑ x ∈ earlierOffKnots A k, ∑ i ∈ offFibre A k x,
        A k i * defectColumn A P i :=
      (sum_off_fibres (A := A) (k := k) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [incomingOffResidue,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [defectColumn,diag_apply,evalNodes_apply,(mem_offFibre.mp hi).2,mul_assoc]

private theorem off_clock_zero (coh : FibreCoherent A k)
    (hzero : ∀ x ∈ earlierOffKnots A k, incomingOffResidue A k x = 0) :
    (∑ i ∈ earlierOffRows A k, A k i * nodes A i) = 0 := by
  rw [←sum_off_fibres (A := A) (k := k) (fun i => A k i * nodes A i)]
  apply Finset.sum_eq_zero
  intro x hx
  have ximage : x ∈ (earlierOffRows A k).image (nodes A) := hx
  obtain ⟨l,hl,hlx⟩ := Finset.mem_image.mp ximage
  have factor : incomingOffResidue A k x =
      (∑ i ∈ offFibre A k x, A k i) * g A l := by
    rw [incomingOffResidue,Finset.sum_mul]
    refine Finset.sum_congr (f := fun i : Fin s => (A k i * g A i : K)) rfl ?_
    intro i hi
    obtain ⟨hi',hix⟩ := mem_offFibre.mp hi
    rw [coh hi' hl (hix.trans hlx.symm)]
  have z : (∑ i ∈ offFibre A k x, A k i) = 0 :=
    (mul_eq_zero.mp (factor.symm.trans (hzero x hx))).resolve_right
      (mem_earlierOffRows.mp hl).2
  calc
    _ = (∑ i ∈ offFibre A k x, A k i) * x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(mem_offFibre.mp hi).2]
    _ = 0 := by rw [z,zero_mul]

/-- Lagrange singleton testing for an arbitrary finite residue support. -/
private theorem residues_eq_zero {S : Finset K} {w : K → K} {d : ℕ}
    (cap : S.card ≤ d+1)
    (paid : ∀ V : K[X], V.natDegree ≤ d → ∑ x ∈ S, w x * V.eval x = 0) :
    ∀ x ∈ S, w x = 0 := by
  classical
  intro x hx
  let f : K → K := fun y => if y=x then 1 else 0
  let V := Lagrange.interpolate S id f
  have hd : V.natDegree ≤ d := by
    by_cases z : V=0
    · simp [z]
    · have t := (natDegree_lt_iff_degree_lt z).mpr
          (Lagrange.degree_interpolate_lt f (Set.injOn_id _) (s:=S))
      omega
  have he (y : K) (hy : y∈S) : V.eval y=f y := by
    exact Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hy
  have p := paid V hd
  rw [Finset.sum_eq_single x] at p
  · simpa [he x hx,f] using p
  · intro y hy hyx
    simp [he y hy,f,hyx]
  · intro e
    exact (e hx).elim

private theorem many_active {d : ℕ} (ha : ∀ i j, i ≤ j → A i j = 0)
    (paid : PaidThrough A k d) (coh : FibreCoherent A k)
    (offReceipt : (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0) :
    d+2 ≤ (activeOffKnots A k).card := by
  by_contra short
  have cap : (activeOffKnots A k).card ≤ d+1 := by omega
  have tests (P : K[X]) (hp : P.natDegree ≤ d) :
      ∑ x ∈ activeOffKnots A k, incomingOffResidue A k x * P.eval x = 0 := by
    have take := paid P hp
    rw [row_defectColumn ha] at take
    refine (Finset.sum_subset (active_subset (A := A) (k := k)) ?_).trans take
    intro x hx hx'
    have z : incomingOffResidue A k x = 0 := by
      by_contra nz
      exact hx' (Finset.mem_filter.mpr ⟨hx,nz⟩)
    rw [z,zero_mul]
  have zeroActive := residues_eq_zero cap tests
  apply offReceipt
  apply off_clock_zero coh
  intro x hx
  by_contra nz
  exact nz (zeroActive x (Finset.mem_filter.mpr ⟨hx,nz⟩))

/-- Actual triangular columns on the chronological prefix. The diagonal of
their restriction to the pivot rows is nonzero; in fact each column is
zero at all physical rows before its pivot. -/
structure TriangularPrefix (A : Matrix (Fin s) (Fin s) K) (k : Fin s) (n : ℕ) where
  pivot : Fin n → Fin s
  ordered : StrictMono pivot
  before : ∀ u, pivot u < k
  off : ∀ u, g A (pivot u) ≠ 0
  clocks : Function.Injective (fun u => nodes A (pivot u))
  polynomial : Fin n → K[X]
  degree : ∀ u, (polynomial u).natDegree ≤ u.val
  earlierZero : ∀ u i, i < pivot u → defectColumn A (polynomial u) i = 0
  atPivot : ∀ u, defectColumn A (polynomial u) (pivot u) ≠ 0
  independent : LinearIndependent K (fun u =>
    prefixRestrict k.isLt.le (defectColumn A (polynomial u)))

private noncomputable def firstOffRows (A : Matrix (Fin s) (Fin s) K) (k : Fin s) :
    Finset (Fin s) :=
  (earlierOffRows A k).filter
    fun i => ∀ l ∈ earlierOffRows A k, nodes A l = nodes A i → i ≤ l

private theorem firstOff_le_rep {i : Fin s} (hi : i ∈ earlierOffRows A k) :
    ∃ l ∈ firstOffRows A k, l ≤ i ∧ nodes A l = nodes A i := by
  classical
  let S := offFibre A k (nodes A i)
  have hiS : i ∈ S := mem_offFibre.mpr ⟨hi,rfl⟩
  let H : S.Nonempty := ⟨i,hiS⟩
  let u := S.min' H
  have hu : u ∈ S := Finset.min'_mem S H
  have Hf : u ∈ earlierOffRows A k ∧ nodes A u = nodes A i := mem_offFibre.mp hu
  refine ⟨u,Finset.mem_filter.mpr ⟨Hf.1,?_⟩,Finset.min'_le S i hiS,Hf.2⟩
  intro l hl hlc
  exact Finset.min'_le S l (mem_offFibre.mpr ⟨hl,hlc.trans Hf.2⟩)

private theorem firstOff_clock_inj :
    Set.InjOn (nodes A) (↑(firstOffRows A k) : Set (Fin s)) := by
  intro i hi l hl h
  have hI := Finset.mem_filter.mp (show i ∈ firstOffRows A k from hi)
  have hL := Finset.mem_filter.mp (show l ∈ firstOffRows A k from hl)
  exact le_antisymm (hI.2 l hL.1 h.symm) (hL.2 i hI.1 h)

private theorem firstOff_card : (firstOffRows A k).card = (earlierOffKnots A k).card := by
  classical
  have im : (firstOffRows A k).image (nodes A) = earlierOffKnots A k := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨i,(Finset.mem_filter.mp hi).1,rfl⟩
    · intro hx
      change x ∈ (earlierOffRows A k).image (nodes A) at hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨l,hl,_,hlc⟩ := firstOff_le_rep hi
      exact Finset.mem_image.mpr ⟨l,hl,hlc⟩
  rw [←im,Finset.card_image_of_injOn firstOff_clock_inj]

private theorem independent_of_causal_pivots {n : ℕ} (p : Fin n → Fin s)
    (v : Fin n → Fin s → K) (strict : StrictMono p) (before : ∀ u, p u < k)
    (zero : ∀ u i, i < p u → v u i = 0) (diagNe : ∀ u, v u (p u) ≠ 0) :
    LinearIndependent K (fun u => prefixRestrict k.isLt.le (v u)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro w e r
  by_contra hr
  let S : Finset (Fin n) := Finset.univ.filter fun u => w u ≠ 0
  let H : S.Nonempty := ⟨r,by simp [S,hr]⟩
  let m := S.min' H
  have hm : w m ≠ 0 := by
    have t : m ∈ S := Finset.min'_mem S H
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using t
  let a : Fin k.val := ⟨(p m).val,before m⟩
  have castA : Fin.castLE k.isLt.le a = p m := Fin.ext rfl
  have ev : (∑ u : Fin n, w u * v u (p m)) = 0 := by
    have t := congrFun e a
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      prefixRestrict_apply,castA,Pi.zero_apply] using t
  have one : (∑ u : Fin n, w u * v u (p m)) = w m * v m (p m) := by
    apply Finset.sum_eq_single m
    · intro u _ um
      by_cases wu : w u = 0
      · rw [wu,zero_mul]
      · have le : m ≤ u := Finset.min'_le S u (by simp [S,wu])
        have lt : m < u := lt_of_le_of_ne le (fun z => um z.symm)
        rw [zero u _ (strict lt),mul_zero]
    · intro no
      exact (no (Finset.mem_univ m)).elim
  exact (mul_ne_zero hm (diagNe m)) (one.symm.trans ev)

private theorem pivots_of_many {n : ℕ} (count : n ≤ (earlierOffKnots A k).card) :
    Nonempty (TriangularPrefix A k n) := by
  classical
  let F := firstOffRows A k
  have fits : n ≤ F.card := by simpa only [F,firstOff_card] using count
  let e : Fin F.card ↪o Fin s := F.orderEmbOfFin rfl
  let q (u : Fin n) : Fin F.card := ⟨u.val,u.isLt.trans_le fits⟩
  let p (u : Fin n) := e (q u)
  have ord : StrictMono p := by
    intro u v lt
    exact e.strictMono (show q u < q v from lt)
  have pm (u : Fin n) : p u ∈ F := F.orderEmbOfFin_mem rfl (q u)
  have pe (u : Fin n) : p u ∈ earlierOffRows A k := (Finset.mem_filter.mp (pm u)).1
  have before (u : Fin n) : p u < k := (mem_earlierOffRows.mp (pe u)).1
  have nz (u : Fin n) : g A (p u) ≠ 0 := (mem_earlierOffRows.mp (pe u)).2
  have ci : Function.Injective (fun u => nodes A (p u)) := by
    intro u v eq
    exact ord.injective (firstOff_clock_inj (pm u) (pm v) eq)
  let S (u : Fin n) := (Finset.Iio u).image (fun v => nodes A (p v))
  let P (u : Fin n) := nodalHull (S u)
  have deg (u : Fin n) : (P u).natDegree ≤ u.val := by
    rw [show P u = nodalHull (S u) from rfl,natDegree_nodalHull]
    exact Finset.card_image_le.trans_eq (Fin.card_Iio u)
  have diagNe (u : Fin n) : defectColumn A (P u) (p u) ≠ 0 := by
    have no : nodes A (p u) ∉ S u := by
      intro h
      obtain ⟨v,hv,z⟩ := Finset.mem_image.mp h
      exact (ne_of_lt (Finset.mem_Iio.mp hv)) (ci z)
    have polyNe : (P u).eval (nodes A (p u)) ≠ 0 := by
      rw [show P u = nodalHull (S u) from rfl,nodalHull,eval_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro x hx
      simp only [eval_sub,eval_X,eval_C]
      exact sub_ne_zero.mpr (fun z => no (z.symm ▸ hx))
    simpa only [defectColumn,diag_apply,evalNodes_apply] using mul_ne_zero (nz u) polyNe
  have lead (u : Fin n) (i : Fin s) (ilt : i < p u) : defectColumn A (P u) i = 0 := by
    by_cases g0 : g A i=0
    · simp only [defectColumn,diag_apply,g0,zero_mul]
    · have hi : i ∈ earlierOffRows A k := mem_earlierOffRows.mpr ⟨ilt.trans (before u),g0⟩
      obtain ⟨l,hl,le,clock⟩ := firstOff_le_rep hi
      have hrange : l ∈ Set.range e := by
        change l ∈ Set.range (F.orderEmbOfFin rfl)
        rw [Finset.range_orderEmbOfFin]
        exact hl
      obtain ⟨m,hm⟩ := hrange
      have mlt : m < q u := (e.lt_iff_lt).mp (by
        change e m < p u
        rw [hm]
        exact le.trans_lt ilt)
      have mval : m.val < u.val := mlt
      let v : Fin n := ⟨m.val,mval.trans u.isLt⟩
      have pv : p v = l := by
        change e (q v) = l
        have eq : q v = m := Fin.ext rfl
        rw [eq,hm]
      have pole : nodes A i ∈ S u :=
        Finset.mem_image.mpr ⟨v,Finset.mem_Iio.mpr (show v<u from mval),
          (congrArg (nodes A) pv).trans clock⟩
      have root : (P u).eval (nodes A i) = 0 := nodalHull_eval_of_mem pole
      simp only [defectColumn,diag_apply,evalNodes_apply,root,mul_zero]
  exact ⟨⟨p,ord,before,nz,ci,P,deg,lead,diagNe,
    independent_of_causal_pivots p (fun u => defectColumn A (P u)) ord before lead diagNe⟩⟩

/-- A strict row with nonzero clock receipt from its off predecessors earns
at least d+2 nonzero earlier residues and d+2 triangular prefix pivots
once all incoming off probes through d are paid and fibres are coherent. -/
theorem paid_prefix_pivots {d : ℕ}
    (ha : ∀ i j, i ≤ j → A i j = 0) (paid : PaidThrough A k d)
    (coh : FibreCoherent A k)
    (offReceipt : (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0) :
    d+2 ≤ (activeOffKnots A k).card ∧ Nonempty (TriangularPrefix A k (d+2)) := by
  have enough := many_active ha paid coh offReceipt
  exact ⟨enough,pivots_of_many
    (enough.trans (Finset.card_le_card (active_subset (A := A) (k := k))))⟩

end RKResearch.Certified.Graded.DefectPrefix
