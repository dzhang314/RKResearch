module

public import RKCert.ReviewedNative.ERK10RationalSixteenData
public import RKCert.ReviewedNative.ERKNormalizedVectorCover
public import RKCert.ReviewedNative.FiniteScaledOrderCheck

import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact integer verification of the universal seventeen-stage method.
The closed receipts apply to the reviewed derivative recurrence rather
than to interval or numerical approximations. -/

namespace RKResearch.Certified.ERK10RationalSixteen
open RKResearch FiniteRootedTree
open scoped Matrix

def integerA : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of aNum

def sparseDot : List (Fin 16) → (Fin 16 → ℤ) → (Fin 16 → ℤ) → ℤ
  | [], _, _ => 0
  | j :: js, a, v => a j*v j+sparseDot js a v

theorem sparseDot_eq (ls : List (Fin 16)) (a v : Fin 16 → ℤ)
    (hn : ls.Nodup) (hz : ∀ j ∉ ls, a j=0) : sparseDot ls a v = a ⬝ᵥ v := by
  let f := fun j => a j*v j
  have hb : ∀ L : List (Fin 16), L.Nodup →
      sparseDot L a v = ∑ j ∈ L.toFinset, f j := by
    intro L hl
    induction L with
    | nil => simp [sparseDot]
    | cons j L ih =>
      obtain ⟨h1,h2⟩ := List.nodup_cons.mp hl
      have hj : j ∉ L.toFinset := by simpa using h1
      simp only [sparseDot,List.toFinset_cons,Finset.sum_insert hj,ih h2,f]
  rw [hb ls hn,dotProduct]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
    simp [f,hz j (by simpa using hj)]

def aSupportOK (i : Fin 16) : Bool :=
  decide (aSupport i).Nodup &&
    (List.finRange 16).all fun j => decide (j ∉ aSupport i → aNum i j=0)

def bSupportOK : Bool :=
  decide bSupport.Nodup &&
    (List.finRange 16).all fun j => decide (j ∉ bSupport → bNum j=0)

private theorem aSupport_cert (i : Fin 16) : aSupportOK i = true :=
  List.all_eq_true.mp (show (List.finRange 16).all aSupportOK = true by decide +kernel)
    i (List.mem_finRange i)
private theorem bSupport_cert : bSupportOK = true := by decide +kernel

theorem sparseA (i : Fin 16) (v : Fin 16 → ℤ) :
    sparseDot (aSupport i) (aNum i) v = (integerA *ᵥ v) i := by
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp (aSupport_cert i)
  exact sparseDot_eq _ _ _ (of_decide_eq_true h1) fun j hj =>
    of_decide_eq_true (List.all_eq_true.mp h2 j (List.mem_finRange j)) hj

theorem sparseB (v : Fin 16 → ℤ) :
    sparseDot bSupport bNum v = bNum ⬝ᵥ v := by
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp bSupport_cert
  exact sparseDot_eq _ _ _ (of_decide_eq_true h1) fun j hj =>
    of_decide_eq_true (List.all_eq_true.mp h2 j (List.mem_finRange j)) hj

def gradeOK (i : Fin Count) : Bool :=
  decide (0 < grade i) &&
    (List.range 11).all fun q => decide (grade i ≤ q → i.val < cut q)

def joinOK (i : Fin Count) : Bool :=
  (List.range (cut (10-grade i))).all fun n =>
    let j := tag n
    decide (grade (join i j) = grade i+grade j) &&
      (List.finRange 16).all fun z => decide (V (join i j) z = V i z * W j z)

def actOK (i : Fin Count) : Bool :=
  (List.finRange 16).all fun j =>
    decide (W i j = (grade i:ℤ)*sparseDot (aSupport j) (aNum j) (V i))
def payOK (i : Fin Count) : Bool := decide ((grade i:ℤ)*sparseDot bSupport bNum (V i)=D^grade i)

def checkBlock (f : Fin Count → Bool) (limit n len : ℕ) : Bool :=
  (List.range' (n*len) (min len (limit-n*len))).all fun k => f (tag k)

private theorem tag_id (i : Fin Count) : tag i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem checkBlock_covers {f : Fin Count → Bool} {limit len blocks : ℕ}
    (hpos : 0 < len) (hl : limit ≤ blocks*len)
    (hb : ∀ n < blocks, checkBlock f limit n len = true)
    (i : Fin Count) (hi : i.val < limit) : f i = true := by
  let q := i.val / len
  have hq : q < blocks := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  have he := Nat.mod_add_div i.val len
  have hm := Nat.mod_lt i.val hpos
  have hi' : i.val ∈ List.range' (q*len) (min len (limit-q*len)) := by
    rw [List.mem_range']
    have hq' : q*len = len*(i.val/len) := Nat.mul_comm _ _
    exact ⟨i.val%len,by omega,by omega⟩
  rw [← tag_id i]
  exact List.all_eq_true.mp (hb q hq) _ hi'

structure Receipts : Prop where
  grade : ∀ i, gradeOK i = true
  join : ∀ i : Fin Count, i.val < ActCount → joinOK i = true
  act : ∀ i : Fin Count, i.val < ActCount → actOK i = true
  pay : ∀ i, payOK i = true

private theorem grade_pos (r : Receipts) (i : Fin Count) : 0 < grade i :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (r.grade i)).1

private theorem grade_mono (r : Receipts) (i : Fin Count) {q : ℕ}
    (hq : q < 11) (hi : grade i ≤ q) : i.val < cut q :=
  of_decide_eq_true (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (r.grade i)).2 q (List.mem_range.mpr hq)) hi

private theorem act_cut (r : Receipts) (i : Fin Count) (hi : grade i < 10) : i.val < ActCount := by
  have H := grade_mono r i (q:=9) (by decide) (by omega)
  rwa [show cut 9=ActCount by decide +kernel] at H

theorem joins_correct (r : Receipts) (i j : Fin Count) (h : grade i+grade j≤10) :
    grade (join i j) = grade i+grade j ∧ V (join i j) = V i*W j := by
  have hp := grade_pos r j
  have hic := act_cut r i (by omega)
  have hjc := grade_mono r j (q:=10-grade i) (by omega) (by omega)
  have H := List.all_eq_true.mp (r.join i hic) _ (List.mem_range.mpr hjc)
  rw [tag_id] at H
  obtain ⟨HG,HV⟩ := Bool.and_eq_true_iff.mp H
  refine ⟨of_decide_eq_true HG, funext fun z => ?_⟩
  exact of_decide_eq_true (List.all_eq_true.mp HV z (List.mem_finRange z))

theorem action_correct (r : Receipts) (i : Fin Count) (hi : grade i<10) :
    W i = (grade i:ℤ) • (integerA *ᵥ V i) := by
  funext j
  have h := of_decide_eq_true
    (List.all_eq_true.mp (r.act i (act_cut r i hi)) j (List.mem_finRange j))
  rw [sparseA] at h
  exact h

theorem root_correct : grade (tag 0) = 1 ∧ V (tag 0) = 1 := by
  refine ⟨by decide +kernel, ?_⟩
  funext j
  have h : (List.finRange 16).all (fun s => decide (V (tag 0) s=1)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_finRange j))

theorem integer_moments (r : Receipts) (t : FiniteRootedTree) (ht : (t.order:ℕ)≤10) :
    (t.factorial:ℤ)*(bNum ⬝ᵥ Φ t integerA)=D^(t.order:ℕ) := by
  obtain ⟨i,hi,hv⟩ := ERKNormalizedVectorCover.cover
    root_correct (joins_correct r) (action_correct r) t ht
  rw [ERKNormalizedVectorCover.factorial_moment,← hi,← hv]
  have h := of_decide_eq_true (r.pay i)
  rwa [sparseB] at h

theorem clocks : integerA *ᵥ (1:Fin 16→ℤ)=cNum := by
  funext j
  have h : (List.finRange 16).all
      (fun i => decide (sparseDot (aSupport i) (aNum i) (fun _ => 1)=cNum i)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp h j (List.mem_finRange j))
  rwa [sparseA] at hh

variable {R : Type*} [CommRing R]

def A (d : R) : Matrix (Fin 16) (Fin 16) R := d • integerA.map (Int.castRingHom R)
def b (d : R) : Fin 16 → R := d • (Int.castRingHom R ∘ bNum)

theorem explicit (d : R) : ERK (A d) := by
  intro i j h
  change d*((aNum i j:ℤ):R)=0
  simp [aNum,Fin.not_lt.mpr h]

theorem order_from_receipts (r : Receipts) (d : R) (hd : (D:R)*d=1) :
    HasOrder 10 (A d) (b d) := by
  let f := Int.castRingHom R
  have hfd : f D*d=1 := hd
  have hA : integerA.map f = f D • A d := by
    change integerA.map f = f D • (d • integerA.map f)
    rw [smul_smul,hfd,one_smul]
  have hb : f ∘ bNum = f D • b d := by
    change f ∘ bNum = f D • (d • (f ∘ bNum))
    rw [smul_smul,hfd,one_smul]
  have hu : IsUnit (f D) := IsUnit.of_mul_eq_one _ hd
  apply hasOrder_of_scaled_moments f hA hb hu hu
  intro t ht
  rw [integer_moments r t ht]
  have hpos := t.order.pos
  conv_lhs => rw [show (t.order:ℕ)=(t.order:ℕ)-1+1 by omega,pow_succ,mul_comm]

end RKResearch.Certified.ERK10RationalSixteen
