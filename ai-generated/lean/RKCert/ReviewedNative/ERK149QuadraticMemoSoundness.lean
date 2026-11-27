module

public import RKCert.ReviewedNative.ERK149QuadraticMemoData
public import RKCert.ReviewedNative.FiniteScaledOrderCheck

import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149QuadraticMemo

open CanonicalStageMemo ERKQuadraticIntegerReplay ERK149QuadraticMemoData
open RKResearch FiniteRootedTree
open scoped Matrix

def packedProd : List (Fin Count) → Fin 14 → Pair
  | [], _ => pack 1
  | [i], s => numAct i s
  | i :: j :: js, s => mul 15 (numAct i s) (packedProd (j :: js) s)

def stage (i : Fin Count) : Fin 14 → Pair := packedProd (key i).children

def gradeOK (i : Fin Count) : Bool :=
  decide (0 < (key i).order) &&
    (List.range 10).all fun q => decide ((key i).order ≤ q → i.val < cutoff q)

def joinOK (i : Fin Count) : Bool :=
  (List.range (cutoff (9 - (key i).order))).all fun n =>
    let j := tag n
    decide (key (join i j) = merged (key i) (key j) j)

def derivOK (i : Fin Count) : Bool :=
  (List.finRange 14).all fun j =>
    decide (numAct i j = ERKQuadraticIntegerReplay.dot 15 14 (aNum j) (stage i))

def payOK (i : Fin Count) : Bool :=
  decide (mul 15 (pack (((key i).order * (key i).forest : ℕ):ℤ))
    (ERKQuadraticIntegerReplay.dot 15 14 bNum (stage i)) =
      pack (den ^ (key i).order))

def checkBlock (f : Fin Count → Bool) (limit b len : ℕ) : Bool :=
  (List.range' (b*len) (min len (limit-b*len))).all fun i => f (tag i)

theorem checkBlock_covers {f : Fin Count → Bool} {limit len blocks : ℕ}
    (hpos : 0 < len) (hl : limit ≤ blocks*len)
    (hb : ∀ n < blocks, checkBlock f limit n len = true)
    (i : Fin Count) (hi : i.val < limit) : f i = true := by
  let b := i.val / len
  have hb' : b < blocks := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  have hir := Nat.mod_add_div i.val len
  have hmod := Nat.mod_lt i.val hpos
  have htag : tag i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hi' : i.val ∈ List.range' (b*len) (min len (limit-b*len)) := by
    rw [List.mem_range']
    have hbmul : b*len = len*(i.val/len) := Nat.mul_comm _ _
    exact ⟨i.val % len, by omega, by omega⟩
  rw [← htag]
  exact List.all_eq_true.mp (hb b hb') _ hi'

structure Receipts : Prop where
  root : key (tag 0) = ⟨1, 1, []⟩
  grade : ∀ i : Fin Count, gradeOK i = true
  join : ∀ i : Fin Count, i.val < cutoff 8 → joinOK i = true
  deriv : ∀ i : Fin Count, i.val < cutoff 8 → derivOK i = true
  payment : ∀ i : Fin Count, payOK i = true

variable {R : Type*} [CommRing R]

def rawA (s : R) : Matrix (Fin 14) (Fin 14) R :=
  Matrix.of fun i j => val s (aNum i j)
def rawB (s : R) : Fin 14 → R :=
  fun i => val s (bNum i)

def A (s d : R) : Matrix (Fin 14) (Fin 14) R := d • rawA s
def b (s d : R) : Fin 14 → R := d • rawB s

theorem explicit (s d : R) : ERK (A s d) := by
  intro i j hij
  change d * val s (aNum i j) = 0
  simp [aNum, Fin.not_lt.mpr hij, val_pack]

private theorem packedProd_val {s : R} (h : s*s = ((15:ℤ):R))
    (ls : List (Fin Count)) :
    (fun j => val s (packedProd ls j)) =
      (ls.map (fun i j => val s (numAct i j))).prod := by
  induction ls with
  | nil =>
    funext j
    simp [packedProd,val_pack]
  | cons i ls ih =>
    cases ls with
    | nil => simp [packedProd]
    | cons k ks =>
      funext j
      change val s (mul 15 (numAct i j) (packedProd (k::ks) j)) =
        val s (numAct i j) * (List.map (fun i j => val s (numAct i j)) (k::ks)).prod j
      rw [val_mul (δ := 15) h, ← congrFun ih j]

theorem stage_val {s : R} (h : s*s = ((15:ℤ):R)) (i : Fin Count) :
    (fun j => val s (stage i j)) =
      decode (key i) (fun i j => val s (numAct i j)) := packedProd_val h _

private theorem grade_pos (r : Receipts) (i : Fin Count) : 0 < (key i).order :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (r.grade i)).1

private theorem grade_cut (r : Receipts) (i : Fin Count) {q : ℕ} (hq : q < 10)
    (hi : (key i).order ≤ q) : i.val < cutoff q := by
  have hc := (Bool.and_eq_true_iff.mp (r.grade i)).2
  exact of_decide_eq_true (List.all_eq_true.mp hc q (List.mem_range.mpr hq)) hi

private theorem deriv_cut (r : Receipts) (i : Fin Count) (hi : (key i).order < 9) :
    i.val < cutoff 8 := grade_cut r i (q:=8) (by decide) (by omega)

theorem joins_correct (r : Receipts) (i j : Fin Count)
    (hij : (key i).order + (key j).order ≤ 9) :
    key (join i j) = merged (key i) (key j) j := by
  have hz := grade_pos r j
  have hi := deriv_cut r i (by omega)
  have hj := grade_cut r j (q := 9 - (key i).order) (by omega) (by omega)
  have h := List.all_eq_true.mp (r.join i hi) j.val (List.mem_range.mpr hj)
  have ht : tag j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simpa only [ht, decide_eq_true_eq] using h

theorem deriv_correct (r : Receipts) {s : R} (h : s*s = ((15:ℤ):R))
    (i : Fin Count) (hi : (key i).order < 9) :
    (fun j => val s (numAct i j)) =
      rawA s *ᵥ decode (key i) (fun i j => val s (numAct i j)) := by
  funext j
  have hc := of_decide_eq_true (List.all_eq_true.mp (r.deriv i (deriv_cut r i hi)) j
    (List.mem_finRange j))
  have ha := congrArg (val s) hc
  rw [val_dot (δ := 15) h] at ha
  change val s (numAct i j) = (fun z => val s (aNum j z)) ⬝ᵥ _
  rw [← stage_val h i]
  exact ha

theorem raw_moments (r : Receipts) {s : R} (h : s*s = ((15:ℤ):R))
    (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 9) :
    (t.factorial : R) * (rawB s ⬝ᵥ Φ t (rawA s)) = (den:R)^(t.order : ℕ) := by
  obtain ⟨i, horder, hforest, hstage⟩ :=
    cover r.root (joins_correct r) (deriv_correct r h) t ht
  have hc := congrArg (val s) (of_decide_eq_true (r.payment i))
  rw [val_mul (δ := 15) h,val_pack,val_dot (δ := 15) h,val_pack,stage_val h, ← hstage] at hc
  have hf : ((t.factorial:ℕ):R) = (((key i).order * (key i).forest : ℕ):R) := by
    rw [horder,hforest]
    rfl
  simp only [Int.cast_natCast, Int.cast_pow] at hc
  rw [← hf, horder] at hc
  exact hc

theorem normalize {s d : R} (t : FiniteRootedTree) :
    (t.factorial:R) * (b s d ⬝ᵥ Φ t (A s d)) =
      ((t.factorial:R)*(rawB s ⬝ᵥ Φ t (rawA s))) * d^(t.order:ℕ) := by
  have ho := t.order.pos
  have hp : (t.order : ℕ) = (t.order:ℕ)-1+1 := by omega
  simp only [A,b,Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  conv_rhs => rw [hp, pow_succ]
  ring

theorem order_from_receipts (r : Receipts) {s d : R}
    (h : s*s = ((15:ℤ):R)) (hd : (den:R)*d = 1) : HasOrder 9 (A s d) (b s d) := by
  intro t ht
  rw [normalize, raw_moments r h t ht, ← mul_pow, hd, one_pow]

end RKResearch.Certified.ERK149QuadraticMemo
