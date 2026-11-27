module

public import RKCert.ReviewedNative.ERK10StepanovKeys
public import RKCert.ReviewedNative.ERK10StepanovDerivatives
public import RKCert.ReviewedNative.FiniteScaledOrderCheck
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Reflection of the 15-stage exact integer cache into the reviewed order
conditions. Neither the Python generator nor a pre-assumed order identity
is trusted: the closed receipts are proved in the separate checks module. -/

namespace RKResearch.Certified.ERK10Stepanov
open ERKNestedRadicalReplay CanonicalStageMemo
open FiniteRootedTree
open scoped Matrix

def packedProd : List (Fin Count) → Fin 15 → C8
  | [], _ => pack 1
  | [i], s => deriv i s
  | i :: j :: js, s => mul (deriv i s) (packedProd (j :: js) s)

def stage (i : Fin Count) : Fin 15 → C8 := packedProd (keys i).children

def gradeOK (i : Fin Count) : Bool :=
  decide (0 < (keys i).order) &&
    (List.range 11).all fun q => decide ((keys i).order ≤ q → i.val < cutoff q)

def joinOK (i : Fin Count) : Bool :=
  (List.range (cutoff (10 - (keys i).order))).all fun n =>
    let j := tag n
    decide (keys (join i j) = merged (keys i) (keys j) j)

def derivOK (i : Fin Count) : Bool :=
  (List.finRange 15).all fun j =>
    decide (deriv i j = ERKNestedRadicalReplay.dot 15 (Anum j) (stage i))

def payOK (i : Fin Count) : Bool :=
  decide (content ((Nat.cast ((keys i).order * (keys i).forest)) : ℤ)
    (ERKNestedRadicalReplay.dot 15 Bnum (stage i)) = pack (D ^ (keys i).order))

def clockOK (j : Fin 15) : Bool :=
  decide (Cnum j = ERKNestedRadicalReplay.dot 15 (Anum j) (fun _ => pack 1))

def bushOK : Bool :=
  decide (content (11 * bushMult)
    (ERKNestedRadicalReplay.dot 15 Bnum
      (fun j => ERKNestedRadicalReplay.pow (Cnum j) 10)) =
      pack ((bushMult + bushResid) * D^11))

/-- Cover the benchmark catalogue in fixed-size bounded ranges. Padding
a block does not incur a proof obligation outside the declared limit. -/
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
  have htag : tag i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hi' : i.val ∈ List.range' (b*len) (min len (limit-b*len)) := by
    rw [List.mem_range']
    have hbmul : b*len = len*(i.val/len) := Nat.mul_comm _ _
    exact ⟨i.val % len, by omega, by omega⟩
  rw [← htag]
  exact List.all_eq_true.mp (hb b hb') _ hi'

structure Receipts : Prop where
  root : keys leafId = ⟨1, 1, []⟩
  grade : ∀ i : Fin Count, gradeOK i = true
  join : ∀ i : Fin Count, i.val < DerivCount → joinOK i = true
  deriv : ∀ i : Fin Count, i.val < DerivCount → derivOK i = true
  payment : ∀ i : Fin Count, payOK i = true
  clock : ∀ j : Fin 15, clockOK j = true
  bush : bushOK = true

variable {R : Type*} [CommRing R]

def rawA (x y z : R) : Matrix (Fin 15) (Fin 15) R :=
  Matrix.of fun i j => val x y z (Anum i j)
def rawB (x y z : R) : Fin 15 → R :=
  fun i => val x y z (Bnum i)

def A (x y z d : R) : Matrix (Fin 15) (Fin 15) R := d • rawA x y z
def b (x y z d : R) : Fin 15 → R := d • rawB x y z

theorem explicit (x y z d : R) : ERK (A x y z d) := by
  intro i j hij
  change d * val x y z (Anum i j) = 0
  simp [Anum, Fin.not_lt.mpr hij, val_pack]

theorem val_content (x y z : R) (e : ℤ) (a : C8) :
    val x y z (content e a) = (e:R)*val x y z a := by
  simp only [val,val4,withVal,ERKQuadraticIntegerReplay.val,content,scale4,scale2,Int.cast_mul]
  ring

private theorem packedProd_val {x y z : R} (h : Roots x y z)
    (ls : List (Fin Count)) :
    (fun j => val x y z (packedProd ls j)) =
      (ls.map (fun i j => val x y z (deriv i j))).prod := by
  induction ls with
  | nil =>
    funext j
    simp [packedProd,val_pack]
  | cons i ls ih =>
    cases ls with
    | nil => simp [packedProd]
    | cons k ks =>
      funext j
      change val x y z (mul (deriv i j) (packedProd (k::ks) j)) =
        val x y z (deriv i j) * (List.map (fun i j => val x y z (deriv i j)) (k::ks)).prod j
      rw [val_mul h, ← congrFun ih j]

theorem stage_val {x y z : R} (h : Roots x y z) (i : Fin Count) :
    (fun j => val x y z (stage i j)) =
      decode (keys i) (fun i j => val x y z (deriv i j)) :=
  packedProd_val h _

private theorem grade_pos (r : Receipts) (i : Fin Count) : 0 < (keys i).order :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (r.grade i)).1

private theorem grade_cut (r : Receipts) (i : Fin Count) {q : ℕ} (hq : q < 11)
    (hi : (keys i).order ≤ q) : i.val < cutoff q := by
  have hc := (Bool.and_eq_true_iff.mp (r.grade i)).2
  exact of_decide_eq_true (List.all_eq_true.mp hc q (List.mem_range.mpr hq)) hi

private theorem deriv_cut (r : Receipts) (i : Fin Count) (hi : (keys i).order < 10) :
    i.val < DerivCount := by
  have H := grade_cut r i (q:=9) (by decide) (by omega)
  rwa [show cutoff 9 = DerivCount by decide +kernel] at H

theorem joins_correct (r : Receipts) (i j : Fin Count)
    (hij : (keys i).order + (keys j).order ≤ 10) :
    keys (join i j) = merged (keys i) (keys j) j := by
  have hz := grade_pos r j
  have hi := deriv_cut r i (by omega)
  have hj := grade_cut r j (q := 10 - (keys i).order) (by omega) (by omega)
  have h := List.all_eq_true.mp (r.join i hi) j.val (List.mem_range.mpr hj)
  have ht : tag j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simpa only [ht, decide_eq_true_eq] using h

theorem deriv_correct (r : Receipts) {x y z : R} (h : Roots x y z)
    (i : Fin Count) (hi : (keys i).order < 10) :
    (fun j => val x y z (deriv i j)) =
      rawA x y z *ᵥ decode (keys i) (fun i j => val x y z (deriv i j)) := by
  funext j
  have hc := of_decide_eq_true (List.all_eq_true.mp (r.deriv i (deriv_cut r i hi)) j
    (List.mem_finRange j))
  have ha := congrArg (val x y z) hc
  rw [val_dot h] at ha
  change val x y z (deriv i j) = (fun s => val x y z (Anum j s)) ⬝ᵥ _
  rw [← stage_val h i]
  exact ha

theorem raw_moments (r : Receipts) {x y z : R} (h : Roots x y z)
    (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 10) :
    (t.factorial : R) * (rawB x y z ⬝ᵥ Φ t (rawA x y z)) = (D:R)^(t.order : ℕ) := by
  obtain ⟨i, horder, hforest, hstage⟩ :=
    cover r.root (joins_correct r) (deriv_correct r h) t ht
  have hc := congrArg (val x y z) (of_decide_eq_true (r.payment i))
  rw [val_content,val_dot h,val_pack,stage_val h, ← hstage] at hc
  have hf : ((t.factorial:ℕ):R) = (((keys i).order * (keys i).forest : ℕ):R) := by
    rw [horder,hforest]
    rfl
  simp only [Int.cast_natCast, Int.cast_pow] at hc
  rw [← hf, horder] at hc
  exact hc

theorem rawClocks (r : Receipts) {x y z : R} (h : Roots x y z) :
    rawA x y z *ᵥ (1 : Fin 15 → R) = fun j => val x y z (Cnum j) := by
  funext j
  have hc := congrArg (val x y z) (of_decide_eq_true (r.clock j))
  rw [val_dot h] at hc
  simp only [val_pack,Int.cast_one] at hc
  exact hc.symm

theorem eleventh_bush_raw (r : Receipts) {x y z : R} (h : Roots x y z) :
    (bushMult:R) * (((bushyTree 11).factorial:R) *
      (rawB x y z ⬝ᵥ Φ (bushyTree 11) (rawA x y z))) =
      ((bushMult:R)+(bushResid:R))*(D:R)^11 := by
  have hc := congrArg (val x y z) (of_decide_eq_true r.bush)
  rw [val_content, val_dot h, val_pack] at hc
  simp only [val_pow h, Int.cast_mul,Int.cast_ofNat,Int.cast_add,Int.cast_pow] at hc
  rw [factorial_bushyTree, Φ_bushyTree,rawClocks r h]
  change (bushMult:R)*(11*((fun i => val x y z (Bnum i)) ⬝ᵥ
    (fun j => val x y z (Cnum j)^10))) = _
  rw [← mul_assoc, mul_comm (bushMult:R)]
  exact hc

theorem normalize {x y z d : R} (t : FiniteRootedTree) :
    (t.factorial:R) * (b x y z d ⬝ᵥ Φ t (A x y z d)) =
      ((t.factorial:R)*(rawB x y z ⬝ᵥ Φ t (rawA x y z))) * d^(t.order:ℕ) := by
  have ho := t.order.pos
  have hp : (t.order : ℕ) = (t.order:ℕ)-1+1 := by omega
  simp only [A,b,Φ_matrix_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  conv_rhs => rw [hp, pow_succ]
  ring

theorem order_from_receipts (r : Receipts) {x y z d : R}
    (h : Roots x y z) (hd : (D:R)*d = 1) : HasOrder 10 (A x y z d) (b x y z d) := by
  intro t ht
  rw [normalize, raw_moments r h t ht, ← mul_pow, hd, one_pow]

theorem eleventh_bush_defect (r : Receipts) {x y z d : R}
    (h : Roots x y z) (hd : (D:R)*d = 1) :
    (bushMult:R)*(((bushyTree 11).factorial:R)*(b x y z d ⬝ᵥ Φ (bushyTree 11) (A x y z d))-1) =
      (bushResid:R) := by
  rw [normalize]
  have horder : ((bushyTree 11).order:ℕ) = 11 := by decide
  rw [horder]
  calc
    _ = ((bushMult:R)*(((bushyTree 11).factorial:R)*
        (rawB x y z ⬝ᵥ Φ (bushyTree 11) (rawA x y z)))) * d^11-(bushMult:R) := by ring
    _ = _ := by rw [eleventh_bush_raw r h, mul_assoc, ← mul_pow, hd]; ring

end RKResearch.Certified.ERK10Stepanov
