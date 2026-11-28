module

public import RKCert.ReviewedNative.ERK10SixteenF11Data
public import RKCert.ReviewedNative.ERKNormalizedVectorCover
public import RKResearch.ERK

@[expose] public section

/-! Small natural-modulus receipts checked against the actual normalized
ordinary rooted-tree recurrence. -/
namespace RKResearch.Certified.ERK10SixteenF11
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 30000

abbrev K := ZMod 11

def tag (i : ℕ) : Fin Count := ⟨i%Count,Nat.mod_lt _ (by decide)⟩
def grade (i : Fin Count) : ℕ := gradeTable[i.val]!
def cut (q : ℕ) : ℕ := cuts[q]!
def aNum (i j : Fin 16) : ℕ := if j < i then (aRows[i.val]!)[j.val]! else 0
def bNum (i : Fin 16) : ℕ := bRow[i.val]!
def vNum (i : Fin Count) (j : Fin 16) : ℕ :=
  ((vBuckets (i.val/16))[i.val%16]!)[j.val]!
def wNum (i : Fin Count) (j : Fin 16) : ℕ :=
  ((wBuckets (i.val/16))[i.val%16]!)[j.val]!
def V (i : Fin Count) (j : Fin 16) : K := vNum i j
def W (i : Fin Count) (j : Fin 16) : K := wNum i j
def A : Matrix (Fin 16) (Fin 16) K := fun i j => aNum i j
def b (i : Fin 16) : K := bNum i
def join (i j : Fin Count) : Fin Count := tag ((joins[i.val]!)[j.val]!)

def gradeOK (i : Fin Count) : Bool :=
  decide (0<grade i) && (List.range 11).all fun q => decide (grade i≤q → i.val<cut q)
def joinPoint (i : Fin Count) (jval : ℕ) : Bool :=
  let j := tag jval
  decide (grade (join i j)=grade i+grade j) &&
    (List.finRange 16).all fun z => decide (vNum (join i j) z=(vNum i z*wNum j z)%11)
def joinOK (i : Fin Count) : Bool :=
  (List.range (cut (10-grade i))).all (joinPoint i)
def joinSlice (i : Fin Count) (start count : ℕ) : Bool :=
  (List.range' start count).all (joinPoint i)
def actOK (i : Fin Count) : Bool :=
  (List.finRange 16).all fun j =>
    decide (wNum i j=(grade i*(∑ k : Fin 16, aNum j k*vNum i k))%11)
def payOK (i : Fin Count) : Bool :=
  decide ((grade i*(∑ k : Fin 16, bNum k*vNum i k))%11=1)

theorem glueJoin {i : Fin Count} {s m n : ℕ}
    (h₀ : joinSlice i s m = true)
    (h₁ : joinSlice i (s+m) n = true) :
    joinSlice i s (m+n) = true := by
  unfold joinSlice at h₀ h₁ ⊢
  simp only [←List.range'_append_1,List.all_append,h₀,h₁,Bool.and_self]

theorem finishJoin {i : Fin Count} {m : ℕ}
    (hm : cut (10-grade i)=m) (h : joinSlice i 0 m=true) : joinOK i=true := by
  simpa only [joinOK,hm,List.range_eq_range',joinSlice] using h

def block (f : Fin Count → Bool) (limit n len : ℕ) : Bool :=
  (List.range' (n*len) (min len (limit-n*len))).all fun k => f (tag k)

private theorem tag_id (i : Fin Count) : tag i.val=i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem block_covers {f : Fin Count → Bool} {limit len blocks : ℕ}
    (hpos : 0<len) (hl : limit≤blocks*len)
    (hb : ∀ n<blocks, block f limit n len=true)
    (i : Fin Count) (hi : i.val<limit) : f i=true := by
  let q := i.val/len
  have hq : q<blocks := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  have he := Nat.mod_add_div i.val len
  have hm := Nat.mod_lt i.val hpos
  have hi' : i.val ∈ List.range' (q*len) (min len (limit-q*len)) := by
    rw [List.mem_range']
    have hq' : q*len=len*(i.val/len) := Nat.mul_comm _ _
    exact ⟨i.val%len,by omega,by omega⟩
  rw [←tag_id i]
  exact List.all_eq_true.mp (hb q hq) _ hi'

structure Receipts : Prop where
  grade : ∀ i, gradeOK i=true
  join : ∀ i : Fin Count, i.val<ActCount → joinOK i=true
  act : ∀ i : Fin Count, i.val<ActCount → actOK i=true
  pay : ∀ i, payOK i=true

private theorem grade_pos (r : Receipts) (i : Fin Count) : 0<grade i :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (r.grade i)).1

private theorem grade_mono (r : Receipts) (i : Fin Count) {q : ℕ}
    (hq : q<11) (hi : grade i≤q) : i.val<cut q :=
  of_decide_eq_true (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (r.grade i)).2 q (List.mem_range.mpr hq)) hi

private theorem act_cut (r : Receipts) (i : Fin Count) (hi : grade i<10) : i.val<ActCount := by
  have H := grade_mono r i (q:=9) (by decide) (by omega)
  rwa [show cut 9=ActCount by decide +kernel] at H

theorem joins_correct (r : Receipts) (i j : Fin Count) (h : grade i+grade j≤10) :
    grade (join i j)=grade i+grade j ∧ V (join i j)=V i*W j := by
  have hp := grade_pos r j
  have hic := act_cut r i (by omega)
  have hjc := grade_mono r j (q:=10-grade i) (by omega) (by omega)
  have H := List.all_eq_true.mp (r.join i hic) _ (List.mem_range.mpr hjc)
  simp only [joinPoint,tag_id] at H
  obtain ⟨HG,HV⟩ := Bool.and_eq_true_iff.mp H
  refine ⟨of_decide_eq_true HG, funext fun z => ?_⟩
  have h0 := of_decide_eq_true (List.all_eq_true.mp HV z (List.mem_finRange z))
  have hc := congrArg (fun a : ℕ => (a:K)) h0
  simpa only [ZMod.natCast_mod,Nat.cast_mul,V,W,Pi.mul_apply] using hc

theorem action_correct (r : Receipts) (i : Fin Count) (hi : grade i<10) :
    W i = (grade i:K) • (A *ᵥ V i) := by
  funext j
  have h := of_decide_eq_true
    (List.all_eq_true.mp (r.act i (act_cut r i hi)) j (List.mem_finRange j))
  have hc := congrArg (fun a : ℕ => (a:K)) h
  simpa only [ZMod.natCast_mod,Nat.cast_mul,Nat.cast_sum,W,V,A,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct] using hc

theorem root_correct : grade (tag 0)=1 ∧ V (tag 0)=1 := by
  refine ⟨by decide +kernel, ?_⟩
  funext j
  have h : (List.finRange 16).all (fun s => decide (vNum (tag 0) s=1)) = true := by decide +kernel
  have hc := of_decide_eq_true (List.all_eq_true.mp h j (List.mem_finRange j))
  change (vNum (tag 0) j:K)=1
  rw [hc,Nat.cast_one]

theorem order_from_receipts (r : Receipts) : HasOrder 10 A b := by
  intro t ht
  obtain ⟨i,hi,hv⟩ := ERKNormalizedVectorCover.cover
    root_correct (joins_correct r) (action_correct r) t ht
  rw [ERKNormalizedVectorCover.factorial_moment,←hi,←hv]
  have h := of_decide_eq_true (r.pay i)
  have hc := congrArg (fun a : ℕ => (a:K)) h
  simpa only [ZMod.natCast_mod,Nat.cast_mul,Nat.cast_sum,Nat.cast_one,b,V,dotProduct] using hc

theorem explicit : ERK A := by
  intro i j h
  change (aNum i j:K)=0
  rw [aNum,ite_eq_right (not_lt_of_ge h),Nat.cast_zero]

def nextTree : FiniteRootedTree := bushyTree 11
theorem next_size : (nextTree.order:ℕ)≤11 := by decide +kernel

theorem next_value : ((nextTree.factorial:ℕ):K)*(b ⬝ᵥ Φ nextTree A)=0 := by
  rw [show (nextTree.factorial:ℕ)=11 by decide +kernel]
  simp only [nextTree,Φ_bushyTree]
  decide +kernel

end RKResearch.Certified.ERK10SixteenF11
