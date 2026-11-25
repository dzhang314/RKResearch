module

public import RKCert.ReviewedNative.OrderedSingleGapRoot
public import RKCert.NodalPrimitive
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Closed polynomial sign strips over arbitrary ordered fields

An affine pencil keeps the endpoint signs on an entire parameter cell.
Finitely many applications of a single-gap factory give one ordered
extension filling the prescribed strips. Saturated factor recovery uses
coprime divisibility and finite-set cardinalities, not splitting or a
multiset enumeration of roots.
-/

namespace RKCert.ReviewedNative.OrderedPolynomialSignStrips

open Polynomial
open RKCert.Endpoint
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.OrderedRootGapSaturation
open scoped BigOperators

universe u
noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def pencil (P T : K[X]) (v : K) : K[X] :=
  C (1-v)*P + C v*T

theorem pencil_eval (P T : K[X]) (v x : K) :
    (pencil P T v).eval x = (1-v)*P.eval x+v*T.eval x := by
  simp only [pencil,eval_add,eval_mul,eval_C]

theorem pencil_coeff (P T : K[X]) (v : K) (k : ℕ) :
    (pencil P T v).coeff k = (1-v)*P.coeff k+v*T.coeff k := by
  simp only [pencil,coeff_add,coeff_C_mul]

theorem pencil_map {L : Type u} [Field L] (e : K →+* L) (P T : K[X]) (v : K) :
    (pencil P T v).map e = pencil (P.map e) (T.map e) (e v) := by
  simp only [pencil,C_sub,C_1,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_sub,Polynomial.map_one,map_C]

/-- An affine value of fixed sign at both cell ends has that sign throughout,
including degenerate cells. No division or Archimedean assumption is needed. -/
theorem affine_nonneg_between {A B l r v : K} (lv : l ≤ v) (vr : v ≤ r)
    (hl : 0 ≤ (1-l)*A+l*B) (hr : 0 ≤ (1-r)*A+r*B) :
    0 ≤ (1-v)*A+v*B := by
  by_cases e : l=r
  · have ev : v=l := le_antisymm (by simpa only [e] using vr) lv
    simpa only [ev] using hl
  · have d : 0 < r-l := sub_pos.mpr (lt_of_le_of_ne (lv.trans vr) e)
    have h := add_nonneg (mul_nonneg (sub_nonneg.mpr vr) hl)
      (mul_nonneg (sub_nonneg.mpr lv) hr)
    have eq : (r-v)*((1-l)*A+l*B)+(v-l)*((1-r)*A+r*B) =
        (r-l)*((1-v)*A+v*B) := by ring
    rw [eq] at h
    exact nonneg_of_mul_nonneg_right h d

theorem affine_nonpos_between {A B l r v : K} (lv : l ≤ v) (vr : v ≤ r)
    (hl : (1-l)*A+l*B ≤ 0) (hr : (1-r)*A+r*B ≤ 0) :
    (1-v)*A+v*B ≤ 0 := by
  have e (s : K) : (1-s)*(-A)+s*(-B) = -((1-s)*A+s*B) := by ring
  have h := affine_nonneg_between (A := -A) (B := -B) lv vr
    (by rw [e]; exact neg_nonneg.mpr hl) (by rw [e]; exact neg_nonneg.mpr hr)
  exact neg_nonneg.mp (by simpa only [e] using h)

structure SignStrips (p : K[X]) {n : ℕ} (lo hi : Fin n → K) : Prop where
  ordered : ∀ i, lo i ≤ hi i
  separated : ∀ ⦃i j⦄, i < j → hi i < lo j
  signs : ∀ i, ((p.eval (lo i) ≤ 0 ∧ 0 ≤ p.eval (hi i)) ∨
    (0 ≤ p.eval (lo i) ∧ p.eval (hi i) ≤ 0))

/-- Exactly the endpoint sign receipts a finite pencil leaf must supply.
The orientation is the same at the two parameter ends, but may depend
on the root index. -/
structure PencilCell (P T : K[X]) (l r : K) {n : ℕ} (lo hi : Fin n → K) : Prop where
  ordered : ∀ i, lo i ≤ hi i
  separated : ∀ ⦃i j⦄, i < j → hi i < lo j
  signs : ∀ i,
    (((pencil P T l).eval (lo i) ≤ 0 ∧ (pencil P T r).eval (lo i) ≤ 0) ∧
       (0 ≤ (pencil P T l).eval (hi i) ∧ 0 ≤ (pencil P T r).eval (hi i))) ∨
    (((0 ≤ (pencil P T l).eval (lo i) ∧ 0 ≤ (pencil P T r).eval (lo i))) ∧
       ((pencil P T l).eval (hi i) ≤ 0 ∧ (pencil P T r).eval (hi i) ≤ 0))

theorem PencilCell.at_param {P T : K[X]} {l r v : K} {n : ℕ} {lo hi : Fin n → K}
    (H : PencilCell P T l r lo hi) (lv : l ≤ v) (vr : v ≤ r) :
    SignStrips (pencil P T v) lo hi := by
  refine ⟨H.ordered,H.separated,?_⟩
  intro i
  have S := H.signs i
  simp only [pencil_eval] at S ⊢
  rcases S with ⟨⟨a,b⟩,⟨c,d⟩⟩ | ⟨⟨a,b⟩,⟨c,d⟩⟩
  · exact Or.inl ⟨affine_nonpos_between lv vr a b,affine_nonneg_between lv vr c d⟩
  · exact Or.inr ⟨affine_nonneg_between lv vr a b,affine_nonpos_between lv vr c d⟩

/-- An extension selected for one polynomial works for all strict base gaps,
not just those with endpoints strictly inside the unit interval. -/
def GapSource (E : OrderedExtension K) (p : K[X]) : Prop :=
  ∀ ⦃a b : K⦄, a < b → Opposite (p.eval a) (p.eval b) → rootInGap E p a b

theorem exists_gapSource (p : K[X]) :
    ∃ E : OrderedExtension K, GapSource E p := by
  classical
  let S := (Finset.range (p.natDegree+1)).filter
    (fun n => ∃ E : OrderedExtension K, (distinctRoots E p).card=n)
  have mem (E : OrderedExtension K) : (distinctRoots E p).card ∈ S :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (distinctRoots_card_le E p)),⟨E,rfl⟩⟩
  have Sne : S.Nonempty := ⟨_,mem (identity K)⟩
  let k := S.max' Sne
  obtain ⟨E,hE⟩ := (Finset.mem_filter.mp (Finset.max'_mem S Sne)).2
  refine ⟨E,?_⟩
  intro a b ab opp
  by_contra missing
  obtain ⟨D,larger⟩ := grow_distinctRoots
    RKCert.ReviewedNative.OrderedSingleGapRoot.singleGapFactory E p a b ab opp missing
  have leMax : (distinctRoots D p).card ≤ k := Finset.le_max' S _ (mem D)
  change (distinctRoots E p).card=k at hE
  omega

/-- A weak closed gap needs no extension when an endpoint itself is a
root. Otherwise it consumes exactly one use of the strict-gap factory. -/
theorem exists_closed_gap_of_singleGapFactory (factory : SingleGapFactory.{u})
    {p : K[X]} {l r : K} (lr : l ≤ r)
    (signs : (p.eval l ≤ 0 ∧ 0 ≤ p.eval r) ∨ (0 ≤ p.eval l ∧ p.eval r ≤ 0)) :
    ∃ (E : OrderedExtension K) (x : E.carrier),
      E.embed l ≤ x ∧ x ≤ E.embed r ∧ (p.map E.embed).IsRoot x := by
  by_cases zl : p.eval l = 0
  · refine ⟨identity K,l,le_rfl,lr,?_⟩
    change (p.map (RingHom.id K)).IsRoot l
    simpa only [Polynomial.map_id] using (show p.IsRoot l from zl)
  by_cases zr : p.eval r = 0
  · refine ⟨identity K,r,lr,le_rfl,?_⟩
    change (p.map (RingHom.id K)).IsRoot r
    simpa only [Polynomial.map_id] using (show p.IsRoot r from zr)
  have opp : Opposite (p.eval l) (p.eval r) := by
    rcases signs with ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inr ⟨lt_of_le_of_ne a zl,lt_of_le_of_ne b (Ne.symm zr)⟩
    · exact Or.inl ⟨lt_of_le_of_ne a (Ne.symm zl),lt_of_le_of_ne b zr⟩
  have lt : l < r := by
    refine lt_of_le_of_ne lr ?_
    intro eq
    subst r
    rcases opp with ⟨a,b⟩ | ⟨a,b⟩
    · exact (lt_asymm a b)
    · exact (lt_asymm a b)
  obtain ⟨E,x,hx,hy,hp⟩ := factory K p l r lt opp
  exact ⟨E,x,hx.le,hy.le,hp⟩

private theorem closed_signs_map (E : OrderedExtension K) {p : K[X]} {l r : K}
    (s : (p.eval l ≤ 0 ∧ 0 ≤ p.eval r) ∨ (0 ≤ p.eval l ∧ p.eval r ≤ 0)) :
    (((p.map E.embed).eval (E.embed l)≤0 ∧ 0≤(p.map E.embed).eval (E.embed r)) ∨
     (0≤(p.map E.embed).eval (E.embed l) ∧ (p.map E.embed).eval (E.embed r)≤0)) := by
  rw [eval_on_base,eval_on_base]
  rcases s with ⟨a,b⟩ | ⟨a,b⟩
  · exact Or.inl ⟨by simpa only [map_zero] using E.mono.monotone a,
      by simpa only [map_zero] using E.mono.monotone b⟩
  · exact Or.inr ⟨by simpa only [map_zero] using E.mono.monotone a,
      by simpa only [map_zero] using E.mono.monotone b⟩

/-- Fill only the given finite closed gaps. Neither distinctness nor
separation of the gaps is required at this stage. At each step the new
ordered map transports all previously chosen roots and their bounds. -/
theorem finite_closed_gaps_of_singleGapFactory (factory : SingleGapFactory.{u}) (p : K[X])
    {n : ℕ} (lo hi : Fin n → K) (ordered : ∀ i, lo i≤hi i)
    (signs : ∀ i, (p.eval (lo i)≤0 ∧ 0≤p.eval (hi i)) ∨
      (0≤p.eval (lo i) ∧ p.eval (hi i)≤0)) :
    ∃ (E : OrderedExtension K) (x : Fin n → E.carrier),
      ∀ i, E.embed (lo i)≤x i ∧ x i≤E.embed (hi i) ∧ (p.map E.embed).IsRoot (x i) := by
  induction n with
  | zero => exact ⟨identity K,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨E,x,hx⟩ := ih (fun i => lo i.castSucc) (fun i => hi i.castSucc)
      (fun i => ordered i.castSucc) (fun i => signs i.castSucc)
    let k : Fin (n+1) := Fin.last n
    obtain ⟨F,r,rl,rh,rr⟩ := exists_closed_gap_of_singleGapFactory factory
      (E.mono.monotone (ordered k)) (closed_signs_map E (signs k))
    let G := followedBy E F
    let y : Fin (n+1) → G.carrier := Fin.snoc (fun i => F.embed (x i)) r
    have hp : (p.map E.embed).map F.embed = p.map G.embed := by
      simp only [G,followedBy,map_map]
    refine ⟨G,y,fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change G.embed (lo k)≤y k ∧ y k≤G.embed (hi k) ∧ (p.map G.embed).IsRoot (y k)
      have hk : y k=r := by simp only [y,k,Fin.snoc_last]
      rw [hk,←hp]
      exact ⟨rl,rh,rr⟩
    · have hj := hx j
      have hy : y j.castSucc=F.embed (x j) := by simp only [y,Fin.snoc_castSucc]
      have root := hj.2.2
      have rootF : ((p.map E.embed).map F.embed).IsRoot (F.embed (x j)) := by
        change ((p.map E.embed).map F.embed).eval (F.embed (x j))=0
        rw [eval_on_base,show (p.map E.embed).eval (x j)=0 from root,map_zero]
      rw [hy,←hp]
      exact ⟨F.mono.monotone hj.1,F.mono.monotone hj.2.1,rootF⟩

theorem SignStrips.exists_roots_of_singleGapFactory (factory : SingleGapFactory.{u})
    {p : K[X]} {n : ℕ} {lo hi : Fin n → K} (H : SignStrips p lo hi) :
    ∃ (E : OrderedExtension K) (x : Fin n → E.carrier), StrictMono x ∧
      (∀ i, E.embed (lo i)≤x i ∧ x i≤E.embed (hi i)) ∧
      (∀ i, (p.map E.embed).IsRoot (x i)) := by
  obtain ⟨E,x,hx⟩ := finite_closed_gaps_of_singleGapFactory factory p lo hi H.ordered H.signs
  refine ⟨E,x,?_,fun i => ⟨(hx i).1,(hx i).2.1⟩,fun i => (hx i).2.2⟩
  intro i j ij
  exact lt_of_le_of_lt (hx i).2.1 (lt_of_lt_of_le (E.mono (H.separated ij)) (hx j).1)

theorem SignStrips.exists_roots {p : K[X]} {n : ℕ} {lo hi : Fin n → K}
    (H : SignStrips p lo hi) :
    ∃ (E : OrderedExtension K) (x : Fin n → E.carrier), StrictMono x ∧
      (∀ i, E.embed (lo i) ≤ x i ∧ x i ≤ E.embed (hi i)) ∧
      (∀ i, (p.map E.embed).IsRoot (x i)) :=
  H.exists_roots_of_singleGapFactory RKCert.ReviewedNative.OrderedSingleGapRoot.singleGapFactory

/-! The next statements use any finite index type. In particular an exterior
root can be put at the extra index of `Option (Fin n)` without pretending its
order is the same in both orientations. -/

def indexedHull {ι : Type*} (t : ι → K) (S : Finset ι) : K[X] :=
  ∏ i ∈ S, (X-C (t i))

theorem indexedHull_monic {ι : Type*} (t : ι → K) (S : Finset ι) :
    (indexedHull t S).Monic := monic_prod_X_sub_C t S

@[simp] theorem indexedHull_degree {ι : Type*} (t : ι → K) (S : Finset ι) :
    (indexedHull t S).natDegree = S.card :=
  natDegree_finsetProd_X_sub_C_eq_card S t

theorem indexedHull_eq_nodalHull {ι : Type*} (t : ι → K) (S : Finset ι)
    (h : Function.Injective t) [DecidableEq K] :
    indexedHull t S = nodalHull (S.image t) := by
  unfold indexedHull nodalHull
  exact (Finset.prod_image (s := S) (g := t)
    (f := fun x : K => (X : K[X])-C x) h.injOn).symm

theorem indexedHull_dvd {ι : Type*} (t : ι → K) (S : Finset ι) (hi : Function.Injective t)
    {p : K[X]} (h : ∀ i ∈ S, p.IsRoot (t i)) : indexedHull t S ∣ p := by
  unfold indexedHull
  refine Finset.prod_dvd_of_coprime
    (s := fun i : ι => (X : K[X])-C (t i)) (t := S) (z := p) ?_ ?_
  · intro i _ j _ ij
    exact pairwise_coprime_X_sub_C hi ij
  · intro i hi'
    exact (Polynomial.dvd_iff_isRoot (a := t i) (p := p)).mpr (h i hi')

theorem factor_eq_of_indexed_roots {ι : Type*} (t : ι → K) (S : Finset ι)
    (hi : Function.Injective t) {p : K[X]} (hp : ∀ i ∈ S, p.IsRoot (t i))
    (degree : p.natDegree ≤ S.card) :
    p = C p.leadingCoeff * indexedHull t S := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (indexedHull_monic t S)
    (indexedHull_dvd t S hi hp)
  simpa only [indexedHull_degree] using degree

theorem indexedHull_eval_ne_zero_iff {ι : Type*} (t : ι → K) (S : Finset ι) (x : K) :
    (indexedHull t S).eval x ≠ 0 ↔ ∀ i ∈ S, x ≠ t i := by
  simp only [indexedHull,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_ne_zero_iff,sub_ne_zero]

theorem indexedHull_isRoot_of_mem {ι : Type*} (t : ι → K) {S : Finset ι} {i : ι}
    (hi : i∈S) : (indexedHull t S).IsRoot (t i) := by
  change (indexedHull t S).eval (t i)=0
  rw [indexedHull,eval_prod]
  apply Finset.prod_eq_zero hi
  simp only [eval_sub,eval_X,eval_C,sub_self]

theorem indexedHull_root_index {ι : Type*} (t : ι → K) {S : Finset ι} {a : K}
    (root : (indexedHull t S).IsRoot a) : ∃ i∈S, t i=a := by
  change (indexedHull t S).eval a=0 at root
  rw [indexedHull,eval_prod] at root
  obtain ⟨i,hi,z⟩ := Finset.prod_eq_zero_iff.mp root
  simp only [eval_sub,eval_X,eval_C,sub_eq_zero] at z
  exact ⟨i,hi,z.symm⟩

/-- Recover indexed factors solely by divisibility.  At every known index
one of the two factors vanishes. Their cardinalities cannot sum to more
than the degree, so every index is assigned to exactly one factor. -/
theorem indexed_partition_of_saturated_roots {ι : Type*} [DecidableEq ι]
    (t : ι → K) (S : Finset ι)
    (ht : Function.Injective t) {Q Z : K[X]} (qne : Q ≠ 0) (zne : Z ≠ 0)
    (layout : Q*Z = C (Q*Z).leadingCoeff * indexedHull t S) :
    ∃ I J : Finset ι, I∪J=S ∧ Disjoint I J ∧
      I.card=Q.natDegree ∧ J.card=Z.natDegree ∧
      Q = C Q.leadingCoeff * indexedHull t I ∧
      Z = C Z.leadingCoeff * indexedHull t J := by
  classical
  let I := S.filter (fun i => Q.IsRoot (t i))
  let J := S.filter (fun i => Z.IsRoot (t i))
  have qmem (i : ι) : i∈I ↔ i∈S ∧ Q.IsRoot (t i) := Finset.mem_filter
  have zmem (i : ι) : i∈J ↔ i∈S ∧ Z.IsRoot (t i) := Finset.mem_filter
  have qroot (i : ι) (h : i∈I) : Q.IsRoot (t i) := ((qmem i).mp h).2
  have zroot (i : ι) (h : i∈J) : Z.IsRoot (t i) := ((zmem i).mp h).2
  have cover : I∪J=S := by
    ext i
    constructor
    · intro iU
      rcases Finset.mem_union.mp iU with h | h
      · exact ((qmem i).mp h).1
      · exact ((zmem i).mp h).1
    · intro iS
      have zz : (Q*Z).eval (t i)=0 := by
        have z : (indexedHull t S).eval (t i)=0 := indexedHull_isRoot_of_mem t iS
        rw [layout,eval_mul,z,mul_zero]
      rw [eval_mul] at zz
      rcases mul_eq_zero.mp zz with h | h
      · exact Finset.mem_union.mpr (Or.inl ((qmem i).mpr ⟨iS,h⟩))
      · exact Finset.mem_union.mpr (Or.inr ((zmem i).mpr ⟨iS,h⟩))
  have fne : Q*Z ≠ 0 := mul_ne_zero qne zne
  have lcne : (Q*Z).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fne
  have fs : (Q*Z).natDegree = S.card := by
    calc
      (Q*Z).natDegree = (C (Q*Z).leadingCoeff * indexedHull t S).natDegree :=
        congrArg Polynomial.natDegree layout
      _ = S.card := by rw [natDegree_C_mul lcne,indexedHull_degree]
  have sumd : Q.natDegree + Z.natDegree = S.card := (natDegree_mul qne zne).symm.trans fs
  have qle : I.card≤Q.natDegree := by
    simpa only [indexedHull_degree] using
      natDegree_le_of_dvd (indexedHull_dvd t I ht qroot) qne
  have zle : J.card≤Z.natDegree := by
    simpa only [indexedHull_degree] using
      natDegree_le_of_dvd (indexedHull_dvd t J ht zroot) zne
  have count := Finset.card_union_add_card_inter I J
  rw [cover] at count
  have qc : I.card=Q.natDegree := by omega
  have zc : J.card=Z.natDegree := by omega
  have ic : (I∩J).card=0 := by omega
  have d : Disjoint I J :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ic)
  exact ⟨I,J,cover,d,qc,zc,factor_eq_of_indexed_roots t I ht qroot qc.ge,
    factor_eq_of_indexed_roots t J ht zroot zc.ge⟩

/-- If only root evaluations and their cardinality are available, the total
layout is a conclusion, not a splitting premise. -/
theorem indexed_partition_of_root_evaluations {ι : Type*} [DecidableEq ι]
    (t : ι → K) (S : Finset ι) (ht : Function.Injective t) {Q Z : K[X]}
    (qne : Q≠0) (zne : Z≠0) (roots : ∀ i∈S, (Q*Z).IsRoot (t i))
    (count : Q.natDegree+Z.natDegree≤S.card) :
    ∃ I J : Finset ι, I∪J=S ∧ Disjoint I J ∧
      I.card=Q.natDegree ∧ J.card=Z.natDegree ∧
      Q=C Q.leadingCoeff*indexedHull t I ∧ Z=C Z.leadingCoeff*indexedHull t J :=
  indexed_partition_of_saturated_roots t S ht qne zne
    (factor_eq_of_indexed_roots t S ht roots (by simpa only [natDegree_mul qne zne] using count))

/-- Compatibility consumer for the marked stopped polynomial. In
particular, the given root of the arbitrary complementary factor cannot
also be an indexed root of the fitting polynomial. -/
theorem factors_of_saturated_roots {ι : Type*} (t : ι → K) (S : Finset ι)
    (ht : Function.Injective t) {Q Z : K[X]} (qne : Q ≠ 0) (zne : Z ≠ 0)
    (layout : Q*Z = C (Q*Z).leadingCoeff * indexedHull t S) :
    ∃ I : Finset ι, I ⊆ S ∧ I.card = Q.natDegree ∧
      Q = C Q.leadingCoeff * indexedHull t I ∧
      ∀ a : K, Z.IsRoot a → ∃ j ∈ S, t j = a ∧ j ∉ I := by
  classical
  obtain ⟨I,J,cover,d,qc,_,qF,zF⟩ :=
    indexed_partition_of_saturated_roots t S ht qne zne layout
  have qsub : I⊆S := by
    intro i hi
    rw [←cover]
    exact Finset.mem_union.mpr (Or.inl hi)
  refine ⟨I,qsub,qc,qF,?_⟩
  intro a za
  have rz : (indexedHull t J).IsRoot a := by
    change Z.eval a=0 at za
    rw [zF,eval_mul,eval_C] at za
    exact (mul_eq_zero.mp za).resolve_left (leadingCoeff_ne_zero.mpr zne)
  obtain ⟨j,hj,eq⟩ := indexedHull_root_index t rz
  have js : j∈S := by
    rw [←cover]
    exact Finset.mem_union.mpr (Or.inr hj)
  exact ⟨j,js,eq,fun ji => (Finset.disjoint_left.mp d) ji hj⟩

end
end RKCert.ReviewedNative.OrderedPolynomialSignStrips
