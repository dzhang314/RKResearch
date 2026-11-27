module

public import RKCert.ReviewedNative.ERK10StepanovClassData
public import RKCert.ReviewedNative.ERK10StepanovMemo
public import RKCert.ReviewedNative.ERKNormalizedVectorCover

@[expose] public section

/-! The closed checker for the 582 distinct normalized stage profiles
uses materialized entries: a row receipt never recursively recomputes a
different elementary vector. Strictly zero taps are skipped on the
checked sparse support lists. -/

namespace RKResearch.Certified.ERK10Stepanov
open ERKNestedRadicalReplay FiniteRootedTree
open scoped Matrix

def sparseMul (u v : C8) : C8 :=
  if u = pack 0 ∨ v = pack 0 then pack 0
  else if u = pack 1 then v
  else if v = pack 1 then u
  else mul u v

theorem val_sparseMul {R : Type*} [CommRing R] {x y z : R} (h : Roots x y z) (u v : C8) :
    val x y z (sparseMul u v) = val x y z u * val x y z v := by
  unfold sparseMul
  split
  next H =>
    rcases H with H | H <;> simp [H,val_pack]
  next _ =>
    split
    next H => simp [H,val_pack]
    next _ =>
      split
      next H => simp [H,val_pack]
      next _ => exact val_mul h _ _

def sparseDot : List (Fin 15) → (Fin 15 → C8) → (Fin 15 → C8) → C8
  | [], _, _ => pack 0
  | j :: js, a, v => add (sparseMul (a j) (v j)) (sparseDot js a v)

def cGradeOK (i : Fin ClassCount) : Bool :=
  decide (0 < cgrade i) &&
    (List.range 11).all fun q => decide (cgrade i ≤ q → i.val < classCut q)

def cJoinOK (i : Fin ClassCount) : Bool :=
  (List.range (classCut (10-cgrade i))).all fun jval =>
    let j := ctag jval
    let k := cjoin i j
    decide (cgrade k = cgrade i + cgrade j) &&
      (List.finRange 15).all fun c => decide (cprofile k c = sparseMul (cprofile i c) (caction j c))

def cActionOK (i : Fin ClassCount) : Bool :=
  (List.finRange 15).all fun c =>
    decide (caction i c = content (cgrade i : ℤ) (sparseDot (aSupport c) (Anum c) (cprofile i)))

def cPayOK (i : Fin ClassCount) : Bool :=
  decide (content (cgrade i : ℤ) (sparseDot bSupport Bnum (cprofile i)) = pack (D^cgrade i))

def cClockReceipt (c : Fin 15) : Bool :=
  decide (Cnum c = sparseDot (aSupport c) (Anum c) (fun _ => pack 1))

def cBushReceipt : Bool :=
  decide (content (11*bushMult) (sparseDot bSupport Bnum (fun i =>
      ERKNestedRadicalReplay.pow (Cnum i) 10)) =
    pack ((bushMult+bushResid)*D^11))

def aSupportOK (c : Fin 15) : Bool :=
  decide (aSupport c).Nodup &&
    (List.finRange 15).all fun j => decide (j ∉ aSupport c → Anum c j = pack 0)
def bSupportOK : Bool :=
  decide bSupport.Nodup &&
    (List.finRange 15).all fun j => decide (j ∉ bSupport → Bnum j = pack 0)

theorem ctag_eq (i : Fin ClassCount) : ctag i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

def cBlock (f : Fin ClassCount → Bool) (limit b len : ℕ) : Bool :=
  (List.range' (b*len) (min len (limit-b*len))).all fun i => f (ctag i)

theorem cBlock_covers {f : Fin ClassCount → Bool} {limit len blocks : ℕ}
    (hpos : 0 < len) (hl : limit ≤ blocks*len)
    (hb : ∀ n < blocks, cBlock f limit n len = true)
    (i : Fin ClassCount) (hi : i.val < limit) : f i = true := by
  let q := i.val / len
  have hq : q < blocks := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  have hir := Nat.mod_add_div i.val len
  have hmod := Nat.mod_lt i.val hpos
  have hi' : i.val ∈ List.range' (q*len) (min len (limit-q*len)) := by
    rw [List.mem_range']
    have hprod : q*len = len*(i.val/len) := Nat.mul_comm _ _
    exact ⟨i.val % len, by omega, by omega⟩
  rw [← ctag_eq i]
  exact List.all_eq_true.mp (hb q hq) _ hi'

structure ClassReceipts : Prop where
  rootGrade : cgrade (ctag 0) = 1
  rootProfile : ∀ j, cprofile (ctag 0) j = pack 1
  grade : ∀ i, cGradeOK i = true
  join : ∀ i : Fin ClassCount, i.val < ActionCount → cJoinOK i = true
  action : ∀ i : Fin ClassCount, i.val < ActionCount → cActionOK i = true
  pay : ∀ i, cPayOK i = true
  aSupportCert : ∀ j, aSupportOK j = true
  bSupportCert : bSupportOK = true
  clock : ∀ j, cClockReceipt j = true
  bush : cBushReceipt = true

variable {R : Type*} [CommRing R]

theorem val_sparseDot {x y z : R} (h : Roots x y z) (ls : List (Fin 15))
    (a v : Fin 15 → C8) (hn : ls.Nodup)
    (hz : ∀ j ∉ ls, a j = pack 0) :
    val x y z (sparseDot ls a v) =
      (fun j => val x y z (a j)) ⬝ᵥ (fun j => val x y z (v j)) := by
  let f := fun j => val x y z (a j)*val x y z (v j)
  have hsum : ∀ Q : List (Fin 15), Q.Nodup →
      val x y z (sparseDot Q a v) = ∑ j ∈ Q.toFinset, f j := by
    intro Q hQ
    induction Q with
    | nil => simp [sparseDot,val_pack]
    | cons k ks ih =>
      have hnd := List.nodup_cons.mp hQ
      have hnot : k ∉ ks.toFinset := by simpa using hnd.1
      simp only [sparseDot,val_add,val_sparseMul h,List.toFinset_cons,Finset.sum_insert hnot,ih hnd.2,f]
  rw [hsum ls hn,dotProduct]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
    simp [f,hz j (by simpa using hj),val_pack]

private theorem oneSupport (r : ClassReceipts) (j : Fin 15) :
    (aSupport j).Nodup ∧ (∀ k ∉ aSupport j, Anum j k = pack 0) := by
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp (r.aSupportCert j)
  exact ⟨of_decide_eq_true h1,fun k hk =>
    of_decide_eq_true (List.all_eq_true.mp h2 k (List.mem_finRange k)) hk⟩

private theorem outSupport (r : ClassReceipts) :
    bSupport.Nodup ∧ (∀ k ∉ bSupport, Bnum k = pack 0) := by
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp r.bSupportCert
  exact ⟨of_decide_eq_true h1,fun k hk =>
    of_decide_eq_true (List.all_eq_true.mp h2 k (List.mem_finRange k)) hk⟩

private theorem grade_pos' (r : ClassReceipts) (i : Fin ClassCount) : 0 < cgrade i :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (r.grade i)).1

private theorem grade_cut' (r : ClassReceipts) (i : Fin ClassCount) {q : ℕ}
    (hq : q < 11) (hi : cgrade i ≤ q) : i.val < classCut q :=
  of_decide_eq_true
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (r.grade i)).2 q (List.mem_range.mpr hq)) hi

private theorem action_cut (r : ClassReceipts) (i : Fin ClassCount)
    (hi : cgrade i < 10) : i.val < ActionCount := by
  have H := grade_cut' r i (q:=9) (by decide) (by omega)
  rwa [show classCut 9 = ActionCount by decide +kernel] at H

theorem class_joins (r : ClassReceipts) {x y z : R} (h : Roots x y z)
    (i j : Fin ClassCount) (hij : cgrade i+cgrade j ≤ 10) :
    cgrade (cjoin i j) = cgrade i+cgrade j ∧
      (fun k => val x y z (cprofile (cjoin i j) k)) =
        (fun k => val x y z (cprofile i k))*(fun k => val x y z (caction j k)) := by
  have gz := grade_pos' r j
  have hj := grade_cut' r j (q:=10-cgrade i) (by omega) (by omega)
  have hi := action_cut r i (by omega)
  have hh := List.all_eq_true.mp (r.join i hi) j.val (List.mem_range.mpr hj)
  rw [ctag_eq] at hh
  obtain ⟨g0, v0⟩ := Bool.and_eq_true_iff.mp hh
  refine ⟨of_decide_eq_true g0, ?_⟩
  funext k
  have hv := of_decide_eq_true (List.all_eq_true.mp v0 k (List.mem_finRange k))
  simp only [hv, val_sparseMul h, Pi.mul_apply]

theorem class_action (r : ClassReceipts) {x y z : R} (h : Roots x y z)
    (i : Fin ClassCount) (hi : cgrade i < 10) :
    (fun j => val x y z (caction i j)) =
      ((cgrade i):R) • (rawA x y z *ᵥ (fun j => val x y z (cprofile i j))) := by
  funext j
  have hv := congrArg (val x y z) (of_decide_eq_true
    (List.all_eq_true.mp (r.action i (action_cut r i hi)) j (List.mem_finRange j)))
  obtain ⟨hn,hz⟩ := oneSupport r j
  rw [val_content, val_sparseDot h _ _ _ hn hz, Int.cast_natCast] at hv
  exact hv

theorem class_raw_moments (r : ClassReceipts) {x y z : R} (h : Roots x y z)
    (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 10) :
    (t.factorial:R)*(rawB x y z ⬝ᵥ Φ t (rawA x y z)) = (D:R)^(t.order:ℕ) := by
  have hr : (fun j => val x y z (cprofile (ctag 0) j)) = (1 : Fin 15 → R) := by
    funext j
    simp only [r.rootProfile, val_pack, Int.cast_one, Pi.one_apply]
  obtain ⟨i,gi,vi⟩ := ERKNormalizedVectorCover.cover ⟨r.rootGrade,hr⟩
    (class_joins r h) (class_action r h) t ht
  have hb := congrArg (val x y z) (of_decide_eq_true (r.pay i))
  obtain ⟨hn,hz⟩ := outSupport r
  rw [val_content,val_sparseDot h _ _ _ hn hz,val_pack,Int.cast_natCast, Int.cast_pow, gi,vi] at hb
  rw [ERKNormalizedVectorCover.factorial_moment]
  exact hb

theorem class_order (r : ClassReceipts) {x y z d : R}
    (h : Roots x y z) (hd : (D:R)*d=1) : HasOrder 10 (A x y z d) (b x y z d) := by
  intro t ht
  rw [normalize,class_raw_moments r h t ht,← mul_pow,hd,one_pow]

theorem class_clock (r : ClassReceipts) {x y z : R} (h : Roots x y z) :
    rawA x y z *ᵥ (1 : Fin 15 → R) = fun j => val x y z (Cnum j) := by
  funext j
  have hc := congrArg (val x y z) (of_decide_eq_true (r.clock j))
  obtain ⟨hn,hz⟩ := oneSupport r j
  rw [val_sparseDot h _ _ _ hn hz] at hc
  simp only [val_pack,Int.cast_one] at hc
  exact hc.symm

theorem class_bush_defect (r : ClassReceipts) {x y z d : R}
    (h : Roots x y z) (hd : (D:R)*d=1) :
    (bushMult:R)*(((bushyTree 11).factorial:R)*(b x y z d ⬝ᵥ Φ (bushyTree 11) (A x y z d))-1) =
      (bushResid:R) := by
  have hraw : (bushMult:R)*(((bushyTree 11).factorial:R)*
    (rawB x y z ⬝ᵥ Φ (bushyTree 11) (rawA x y z))) =
      ((bushMult:R)+(bushResid:R))*(D:R)^11 := by
    have hc := congrArg (val x y z) (of_decide_eq_true r.bush)
    obtain ⟨hn,hz⟩ := outSupport r
    rw [val_content,val_sparseDot h _ _ _ hn hz,val_pack] at hc
    simp only [val_pow h,Int.cast_mul,Int.cast_ofNat,Int.cast_add,Int.cast_pow] at hc
    rw [factorial_bushyTree,Φ_bushyTree,class_clock r h]
    change (bushMult:R)*(11*((fun i => val x y z (Bnum i)) ⬝ᵥ
      (fun j => val x y z (Cnum j)^10)))=_
    rw [← mul_assoc,mul_comm (bushMult:R)]
    exact hc
  rw [normalize, show ((bushyTree 11).order:ℕ)=11 by decide]
  calc
    _ = ((bushMult:R)*(((bushyTree 11).factorial:R)*
        (rawB x y z ⬝ᵥ Φ (bushyTree 11) (rawA x y z)))) * d^11-(bushMult:R) := by ring
    _ = _ := by rw [hraw,mul_assoc,←mul_pow,hd]; ring

end RKResearch.Certified.ERK10Stepanov
