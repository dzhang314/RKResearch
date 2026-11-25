module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortSchema
public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords

import Mathlib.Data.List.Sort
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 24000
set_option maxHeartbeats 16000000

/-- Exact chronological position words; root slots are increasing. -/
def retainedWords : List PortWord :=
  [
   ⟨[0, 1, 3, 6], 4, 7, 5, 2⟩,
   ⟨[0, 1, 3, 6], 5, 7, 4, 2⟩,
   ⟨[0, 1, 3, 6], 7, 4, 5, 2⟩,
   ⟨[0, 1, 3, 6], 7, 5, 4, 2⟩,
   ⟨[0, 1, 4, 6], 2, 7, 5, 3⟩,
   ⟨[0, 1, 4, 6], 3, 7, 5, 2⟩,
   ⟨[0, 1, 4, 6], 7, 2, 5, 3⟩,
   ⟨[0, 1, 4, 6], 7, 3, 5, 2⟩,
   ⟨[0, 1, 4, 7], 2, 5, 6, 3⟩,
   ⟨[0, 1, 4, 7], 2, 6, 5, 3⟩,
   ⟨[0, 1, 4, 7], 3, 5, 6, 2⟩,
   ⟨[0, 1, 4, 7], 3, 6, 5, 2⟩,
   ⟨[0, 1, 4, 7], 5, 2, 6, 3⟩,
   ⟨[0, 1, 4, 7], 5, 3, 6, 2⟩,
   ⟨[0, 1, 4, 7], 6, 2, 5, 3⟩,
   ⟨[0, 1, 4, 7], 6, 3, 5, 2⟩,
   ⟨[0, 2, 3, 6], 4, 7, 5, 1⟩,
   ⟨[0, 2, 3, 6], 5, 7, 4, 1⟩,
   ⟨[0, 2, 3, 6], 7, 4, 5, 1⟩,
   ⟨[0, 2, 3, 6], 7, 5, 4, 1⟩,
   ⟨[0, 2, 4, 6], 3, 7, 5, 1⟩,
   ⟨[0, 2, 4, 6], 5, 7, 1, 3⟩,
   ⟨[0, 2, 4, 6], 5, 7, 3, 1⟩,
   ⟨[0, 2, 4, 6], 7, 1, 5, 3⟩,
   ⟨[0, 2, 4, 6], 7, 3, 5, 1⟩,
   ⟨[0, 2, 4, 6], 7, 5, 1, 3⟩,
   ⟨[0, 2, 4, 6], 7, 5, 3, 1⟩,
   ⟨[0, 2, 4, 7], 3, 5, 6, 1⟩,
   ⟨[0, 2, 4, 7], 3, 6, 5, 1⟩,
   ⟨[0, 2, 4, 7], 5, 1, 6, 3⟩,
   ⟨[0, 2, 4, 7], 5, 3, 6, 1⟩,
   ⟨[0, 2, 4, 7], 6, 1, 5, 3⟩,
   ⟨[0, 2, 4, 7], 6, 3, 5, 1⟩,
   ⟨[0, 2, 5, 6], 3, 7, 1, 4⟩,
   ⟨[0, 2, 5, 6], 3, 7, 4, 1⟩,
   ⟨[0, 2, 5, 6], 4, 7, 1, 3⟩,
   ⟨[0, 2, 5, 6], 4, 7, 3, 1⟩,
   ⟨[0, 2, 5, 6], 7, 3, 1, 4⟩,
   ⟨[0, 2, 5, 6], 7, 3, 4, 1⟩,
   ⟨[0, 2, 5, 6], 7, 4, 1, 3⟩,
   ⟨[0, 2, 5, 6], 7, 4, 3, 1⟩,
   ⟨[0, 2, 5, 7], 3, 1, 6, 4⟩,
   ⟨[0, 2, 5, 7], 3, 6, 1, 4⟩,
   ⟨[0, 2, 5, 7], 3, 6, 4, 1⟩,
   ⟨[0, 2, 5, 7], 4, 1, 6, 3⟩,
   ⟨[0, 2, 5, 7], 4, 6, 1, 3⟩,
   ⟨[0, 2, 5, 7], 4, 6, 3, 1⟩,
   ⟨[0, 2, 5, 7], 6, 3, 1, 4⟩,
   ⟨[0, 2, 5, 7], 6, 3, 4, 1⟩,
   ⟨[0, 2, 5, 7], 6, 4, 1, 3⟩,
   ⟨[0, 2, 5, 7], 6, 4, 3, 1⟩,
   ⟨[0, 3, 4, 6], 7, 1, 5, 2⟩,
   ⟨[0, 3, 4, 6], 7, 2, 5, 1⟩,
   ⟨[0, 3, 4, 7], 5, 1, 6, 2⟩,
   ⟨[0, 3, 4, 7], 5, 2, 6, 1⟩,
   ⟨[0, 3, 4, 7], 6, 1, 5, 2⟩,
   ⟨[0, 3, 4, 7], 6, 2, 5, 1⟩,
   ⟨[0, 3, 5, 6], 7, 1, 2, 4⟩,
   ⟨[0, 3, 5, 6], 7, 1, 4, 2⟩,
   ⟨[0, 3, 5, 6], 7, 2, 1, 4⟩,
   ⟨[0, 3, 5, 6], 7, 2, 4, 1⟩,
   ⟨[0, 3, 5, 7], 4, 1, 6, 2⟩,
   ⟨[0, 3, 5, 7], 4, 2, 6, 1⟩,
   ⟨[0, 3, 5, 7], 6, 1, 2, 4⟩,
   ⟨[0, 3, 5, 7], 6, 1, 4, 2⟩,
   ⟨[0, 3, 5, 7], 6, 2, 1, 4⟩,
   ⟨[0, 3, 5, 7], 6, 2, 4, 1⟩,
   ⟨[0, 3, 6, 7], 4, 1, 2, 5⟩,
   ⟨[0, 3, 6, 7], 4, 1, 5, 2⟩,
   ⟨[0, 3, 6, 7], 4, 2, 1, 5⟩,
   ⟨[0, 3, 6, 7], 4, 2, 5, 1⟩,
   ⟨[0, 3, 6, 7], 5, 1, 2, 4⟩,
   ⟨[0, 3, 6, 7], 5, 1, 4, 2⟩,
   ⟨[0, 3, 6, 7], 5, 2, 1, 4⟩,
   ⟨[0, 3, 6, 7], 5, 2, 4, 1⟩,
   ⟨[1, 2, 3, 6], 4, 7, 5, 0⟩,
   ⟨[1, 2, 3, 6], 5, 7, 4, 0⟩,
   ⟨[1, 2, 3, 6], 7, 4, 5, 0⟩,
   ⟨[1, 2, 3, 6], 7, 5, 4, 0⟩,
   ⟨[1, 2, 4, 6], 3, 7, 5, 0⟩,
   ⟨[1, 2, 4, 6], 5, 7, 0, 3⟩,
   ⟨[1, 2, 4, 6], 5, 7, 3, 0⟩,
   ⟨[1, 2, 4, 6], 7, 3, 5, 0⟩,
   ⟨[1, 2, 4, 6], 7, 5, 0, 3⟩,
   ⟨[1, 2, 4, 6], 7, 5, 3, 0⟩,
   ⟨[1, 2, 4, 7], 3, 5, 6, 0⟩,
   ⟨[1, 2, 4, 7], 3, 6, 5, 0⟩,
   ⟨[1, 2, 4, 7], 5, 3, 6, 0⟩,
   ⟨[1, 2, 4, 7], 6, 3, 5, 0⟩,
   ⟨[1, 2, 5, 6], 3, 7, 0, 4⟩,
   ⟨[1, 2, 5, 6], 3, 7, 4, 0⟩,
   ⟨[1, 2, 5, 6], 4, 7, 0, 3⟩,
   ⟨[1, 2, 5, 6], 4, 7, 3, 0⟩,
   ⟨[1, 2, 5, 6], 7, 3, 0, 4⟩,
   ⟨[1, 2, 5, 6], 7, 3, 4, 0⟩,
   ⟨[1, 2, 5, 6], 7, 4, 0, 3⟩,
   ⟨[1, 2, 5, 6], 7, 4, 3, 0⟩,
   ⟨[1, 2, 5, 7], 3, 6, 0, 4⟩,
   ⟨[1, 2, 5, 7], 3, 6, 4, 0⟩,
   ⟨[1, 2, 5, 7], 4, 6, 0, 3⟩,
   ⟨[1, 2, 5, 7], 4, 6, 3, 0⟩,
   ⟨[1, 2, 5, 7], 6, 3, 0, 4⟩,
   ⟨[1, 2, 5, 7], 6, 3, 4, 0⟩,
   ⟨[1, 2, 5, 7], 6, 4, 0, 3⟩,
   ⟨[1, 2, 5, 7], 6, 4, 3, 0⟩,
   ⟨[1, 3, 4, 6], 5, 7, 0, 2⟩,
   ⟨[1, 3, 4, 6], 5, 7, 2, 0⟩,
   ⟨[1, 3, 4, 6], 7, 2, 5, 0⟩,
   ⟨[1, 3, 4, 6], 7, 5, 0, 2⟩,
   ⟨[1, 3, 4, 6], 7, 5, 2, 0⟩,
   ⟨[1, 3, 4, 7], 5, 2, 6, 0⟩,
   ⟨[1, 3, 4, 7], 6, 2, 5, 0⟩,
   ⟨[1, 3, 5, 6], 4, 7, 0, 2⟩,
   ⟨[1, 3, 5, 6], 4, 7, 2, 0⟩,
   ⟨[1, 3, 5, 6], 7, 2, 0, 4⟩,
   ⟨[1, 3, 5, 6], 7, 2, 4, 0⟩,
   ⟨[1, 3, 5, 6], 7, 4, 0, 2⟩,
   ⟨[1, 3, 5, 6], 7, 4, 2, 0⟩,
   ⟨[1, 3, 5, 7], 4, 2, 6, 0⟩,
   ⟨[1, 3, 5, 7], 4, 6, 0, 2⟩,
   ⟨[1, 3, 5, 7], 4, 6, 2, 0⟩,
   ⟨[1, 3, 5, 7], 6, 2, 0, 4⟩,
   ⟨[1, 3, 5, 7], 6, 2, 4, 0⟩,
   ⟨[1, 3, 5, 7], 6, 4, 0, 2⟩,
   ⟨[1, 3, 5, 7], 6, 4, 2, 0⟩,
   ⟨[1, 3, 6, 7], 4, 2, 0, 5⟩,
   ⟨[1, 3, 6, 7], 4, 2, 5, 0⟩,
   ⟨[1, 3, 6, 7], 5, 2, 0, 4⟩,
   ⟨[1, 3, 6, 7], 5, 2, 4, 0⟩,
   ⟨[1, 4, 5, 6], 7, 2, 0, 3⟩,
   ⟨[1, 4, 5, 6], 7, 2, 3, 0⟩,
   ⟨[1, 4, 5, 6], 7, 3, 0, 2⟩,
   ⟨[1, 4, 5, 6], 7, 3, 2, 0⟩,
   ⟨[1, 4, 5, 7], 6, 2, 0, 3⟩,
   ⟨[1, 4, 5, 7], 6, 2, 3, 0⟩,
   ⟨[1, 4, 5, 7], 6, 3, 0, 2⟩,
   ⟨[1, 4, 5, 7], 6, 3, 2, 0⟩,
   ⟨[1, 4, 6, 7], 5, 2, 0, 3⟩,
   ⟨[1, 4, 6, 7], 5, 2, 3, 0⟩,
   ⟨[1, 4, 6, 7], 5, 3, 0, 2⟩,
   ⟨[1, 4, 6, 7], 5, 3, 2, 0⟩]

theorem retained_words_count : retainedWords.length = 141 := by decide +kernel
theorem retained_words_nodup : retainedWords.Nodup := by decide +kernel
theorem retained_words_permitted : retainedWords.all PortWord.permitted = true := by decide +kernel

/-- Only these four entries are read from the tail.  This length lemma
avoids any enumeration of the actual values at those positions. -/
private theorem wordTail_eq_four {l : List (Fin 8)} (len : l.length = 4) :
    [l[0]?.getD 0, l[1]?.getD 0, l[2]?.getD 0, l[3]?.getD 0] = l := by
  cases l with
  | nil => simp at len
  | cons x l =>
    cases l with
    | nil => simp at len
    | cons y l =>
      cases l with
      | nil => simp at len
      | cons u l =>
        cases l with
        | nil => simp at len
        | cons v l =>
          cases l with
          | nil => rfl
          | cons j l =>
            simp only [List.length_cons] at len
            omega

private theorem decodeWord_parts {σ : List (Fin 8)} (len : σ.length = 8) :
    (decodeWord σ).roots ++
      [(decodeWord σ).u, (decodeWord σ).a, (decodeWord σ).h, (decodeWord σ).z] = σ := by
  have sl : (σ.drop 4).length = 4 := by
    rw [List.length_drop, len]
  have tail :
      [(decodeWord σ).u, (decodeWord σ).a, (decodeWord σ).h, (decodeWord σ).z] = σ.drop 4 := by
    simpa only [decodeWord, List.getElem?_drop] using wordTail_eq_four sl
  change σ.take 4 ++ _ = σ
  rw [tail, List.take_append_drop]

private theorem word_eq_of_canonical_roots (w : PortWord)
    (h : w.roots = (wordOfMarks w.u w.a w.h w.z).roots) :
    w = wordOfMarks w.u w.a w.h w.z := by
  cases w with
  | mk r u a h' z =>
    exact congrArg (fun l : List (Fin 8) => PortWord.mk l u a h' z) h

/-- Permutation admissibility plus the increasing-root test forces the
exact canonical word of the four marks, not just the same word count. -/
private theorem permitted_decode_mem_markGroups {σ : List (Fin 8)}
    (perm : σ.Perm (List.finRange 8)) (good : (decodeWord σ).permitted = true) :
    decodeWord σ ∈ allMarkGroups.flatten := by
  let w := decodeWord σ
  let marks := [w.u, w.a, w.h, w.z]
  have len : σ.length = 8 := by simpa only [List.length_finRange] using perm.length_eq
  have split : w.roots ++ marks = σ := decodeWord_parts len
  have nd : (w.roots ++ marks).Nodup := by
    rw [split]
    exact perm.symm.nodup (List.nodup_finRange 8)
  have parts := List.nodup_append.mp nd
  have sorted : w.roots.Pairwise (· < ·) := by
    unfold PortWord.permitted at good
    exact (of_decide_eq_true good).1
  have sorted' : (wordOfMarks w.u w.a w.h w.z).roots.Pairwise (· < ·) :=
    List.Pairwise.filter _ (List.sortedLT_finRange 8).pairwise
  have unmarked (j : Fin 8) : j ∉ marks ↔ j ≠ w.u ∧ j ≠ w.a ∧ j ≠ w.h ∧ j ≠ w.z := by
    simp [marks]
  have same (j : Fin 8) : j ∈ w.roots ↔ j ∈ (wordOfMarks w.u w.a w.h w.z).roots := by
    rw [markWord_roots_iff, ← unmarked]
    constructor
    · intro jr jm
      exact parts.2.2 j jr j jm rfl
    · intro hx
      have full : j ∈ σ := perm.mem_iff.mpr (by simp)
      rw [← split] at full
      exact (List.mem_append.mp full).resolve_right hx
  have rootPerm : w.roots.Perm (wordOfMarks w.u w.a w.h w.z).roots :=
    (List.perm_ext_iff_of_nodup parts.1 (markWord_roots_nodup w.u w.a w.h w.z)).mpr same
  have rootEq : w.roots = (wordOfMarks w.u w.a w.h w.z).roots :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => False.elim (lt_asymm ab ba))
      sorted sorted' rootPerm
  change w ∈ allMarkGroups.flatten
  have member := (all_mark_word_spec w.u w.a w.h w.z parts.2.1).2
  exact (word_eq_of_canonical_roots w rootEq).symm ▸ member

private def coveredMarkWord (w : PortWord) : Bool :=
  decide (w.permitted = false ∨ w ∈ retainedWords)

/- Retaining group barriers is important: each kernel decision sees only
its own 24 existing words, never 1,680 or 40,320 words at once. -/
private theorem markGroup00_covered : markWords00.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup01_covered : markWords01.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup02_covered : markWords02.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup03_covered : markWords03.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup04_covered : markWords04.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup05_covered : markWords05.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup06_covered : markWords06.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup07_covered : markWords07.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup08_covered : markWords08.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup09_covered : markWords09.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup10_covered : markWords10.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup11_covered : markWords11.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup12_covered : markWords12.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup13_covered : markWords13.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup14_covered : markWords14.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup15_covered : markWords15.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup16_covered : markWords16.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup17_covered : markWords17.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup18_covered : markWords18.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup19_covered : markWords19.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup20_covered : markWords20.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup21_covered : markWords21.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup22_covered : markWords22.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup23_covered : markWords23.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup24_covered : markWords24.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup25_covered : markWords25.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup26_covered : markWords26.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup27_covered : markWords27.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup28_covered : markWords28.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup29_covered : markWords29.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup30_covered : markWords30.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup31_covered : markWords31.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup32_covered : markWords32.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup33_covered : markWords33.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup34_covered : markWords34.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup35_covered : markWords35.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup36_covered : markWords36.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup37_covered : markWords37.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup38_covered : markWords38.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup39_covered : markWords39.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup40_covered : markWords40.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup41_covered : markWords41.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup42_covered : markWords42.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup43_covered : markWords43.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup44_covered : markWords44.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup45_covered : markWords45.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup46_covered : markWords46.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup47_covered : markWords47.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup48_covered : markWords48.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup49_covered : markWords49.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup50_covered : markWords50.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup51_covered : markWords51.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup52_covered : markWords52.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup53_covered : markWords53.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup54_covered : markWords54.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup55_covered : markWords55.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup56_covered : markWords56.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup57_covered : markWords57.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup58_covered : markWords58.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup59_covered : markWords59.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup60_covered : markWords60.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup61_covered : markWords61.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup62_covered : markWords62.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup63_covered : markWords63.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup64_covered : markWords64.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup65_covered : markWords65.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup66_covered : markWords66.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup67_covered : markWords67.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup68_covered : markWords68.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroup69_covered : markWords69.all coveredMarkWord = true := by
  decide +kernel

private theorem markGroups_covered :
    allMarkGroups.all (fun g => g.all coveredMarkWord) = true := by
  simp only [allMarkGroups, List.all_cons, List.all_nil, Bool.true_and,
    markGroup00_covered, markGroup01_covered, markGroup02_covered, markGroup03_covered,
    markGroup04_covered, markGroup05_covered, markGroup06_covered, markGroup07_covered,
    markGroup08_covered, markGroup09_covered, markGroup10_covered, markGroup11_covered,
    markGroup12_covered, markGroup13_covered, markGroup14_covered, markGroup15_covered,
    markGroup16_covered, markGroup17_covered, markGroup18_covered, markGroup19_covered,
    markGroup20_covered, markGroup21_covered, markGroup22_covered, markGroup23_covered,
    markGroup24_covered, markGroup25_covered, markGroup26_covered, markGroup27_covered,
    markGroup28_covered, markGroup29_covered, markGroup30_covered, markGroup31_covered,
    markGroup32_covered, markGroup33_covered, markGroup34_covered, markGroup35_covered,
    markGroup36_covered, markGroup37_covered, markGroup38_covered, markGroup39_covered,
    markGroup40_covered, markGroup41_covered, markGroup42_covered, markGroup43_covered,
    markGroup44_covered, markGroup45_covered, markGroup46_covered, markGroup47_covered,
    markGroup48_covered, markGroup49_covered, markGroup50_covered, markGroup51_covered,
    markGroup52_covered, markGroup53_covered, markGroup54_covered, markGroup55_covered,
    markGroup56_covered, markGroup57_covered, markGroup58_covered, markGroup59_covered,
    markGroup60_covered, markGroup61_covered, markGroup62_covered, markGroup63_covered,
    markGroup64_covered, markGroup65_covered, markGroup66_covered, markGroup67_covered,
    markGroup68_covered, markGroup69_covered]

/-- The public exhaustive check now follows structurally from every
permutation's canonical sorted complement, and the bounded mark groups. -/
theorem permutations_covered : (List.finRange 8).permutations.all (fun σ =>
    decide ((decodeWord σ).permitted = false ∨ decodeWord σ ∈ retainedWords)) = true := by
  apply List.all_eq_true.mpr
  intro σ hσ
  change coveredMarkWord (decodeWord σ) = true
  cases hgood : (decodeWord σ).permitted
  · exact decide_eq_true (Or.inl hgood)
  · have hw := permitted_decode_mem_markGroups (List.mem_permutations.mp hσ) hgood
    obtain ⟨group, hg, wmem⟩ := List.mem_flatten.mp hw
    exact List.all_eq_true.mp (List.all_eq_true.mp markGroups_covered group hg) (decodeWord σ) wmem

theorem retained_of_permitted {σ : List (Fin 8)} (perm : σ.Perm (List.finRange 8))
    (good : (decodeWord σ).permitted = true) : decodeWord σ ∈ retainedWords := by
  have h := List.all_eq_true.mp permutations_covered σ (List.mem_permutations.mpr perm)
  exact (of_decide_eq_true h).resolve_left (by simp [good])

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
