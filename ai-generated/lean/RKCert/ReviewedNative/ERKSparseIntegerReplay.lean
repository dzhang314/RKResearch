module

public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay

@[expose] public section

/-! Skip a zero tableau tap before evaluating its child profile. This is
important in exact integer kernel replay for tall trees and large
denominators: strict triangularity becomes an actual reduction shortcut.
The checked result is unchanged from the existing integer recurrence. -/

namespace RKResearch.Certified.ERKSparseIntegerReplay

open ERKQuadraticIntegerReplay FiniteRootedTree

def dot (δ : Int) : (n : Nat) → (Fin n → Pair) → (Fin n → Pair) → Pair
  | 0, _, _ => pack 0
  | n+1, a, b =>
    add (if a 0 = pack 0 then pack 0 else mul δ (a 0) (b 0))
      (dot δ n (a ∘ Fin.succ) (b ∘ Fin.succ))

theorem dot_eq (δ : Int) (n : Nat) (a b : Fin n → Pair) :
    dot δ n a b = ERKQuadraticIntegerReplay.dot δ n a b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dot, ERKQuadraticIntegerReplay.dot, ih]
    by_cases h : a 0 = pack 0
    · rw [if_pos h,h]; simp [mul,pack]
    · rw [if_neg h]

def profile (δ : Int) {n : Nat} (M : Fin n → Fin n → Pair) :
    FiniteRootedTree → Fin n → Pair
  | .leaf => fun _ => pack 1
  | .butcherProduct u v => fun i =>
    mul δ (profile δ M u i) (dot δ n (M i) (profile δ M v))

theorem profile_eq (δ : Int) {n : Nat} (M : Fin n → Fin n → Pair)
    (t : FiniteRootedTree) : profile δ M t = ERKQuadraticIntegerReplay.profile δ M t := by
  induction t with
  | leaf => rfl
  | butcherProduct u v iu iv =>
    simp only [profile,ERKQuadraticIntegerReplay.profile,dot_eq,iu,iv]

def numer (δ : Int) {n : Nat} (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (t : FiniteRootedTree) : Pair :=
  mul δ (pack (t.factorial : Nat)) (dot δ n w (profile δ M t))

theorem numer_eq (δ : Int) {n : Nat} (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (t : FiniteRootedTree) : numer δ M w t = ERKQuadraticIntegerReplay.numer δ M w t := by
  simp only [numer, ERKQuadraticIntegerReplay.numer, dot_eq, profile_eq]

def checkOn (δ : Int) {n : Nat} (D : Int) (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (k : Nat) : Bool :=
  (treesOfOrderSucc k).all fun t => decide (numer δ M w t = pack (D * scale D t))

theorem checkOn_eq (δ : Int) {n : Nat} (D : Int) (M : Fin n → Fin n → Pair) (w : Fin n → Pair)
    (k : Nat) : checkOn δ D M w k = ERKQuadraticIntegerReplay.checkOn δ D M w k := by
  simp only [checkOn, ERKQuadraticIntegerReplay.checkOn, numer_eq]

end RKResearch.Certified.ERKSparseIntegerReplay
