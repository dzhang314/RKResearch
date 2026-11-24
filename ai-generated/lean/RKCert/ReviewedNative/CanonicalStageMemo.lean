module

public import RKCert.ReviewedNative.FiniteOrderCheck

@[expose] public section

/-! # Checked multiset cache for the reviewed stage recurrence

A record stores a root's child IDs, order, and forest factorial. A
certificate proves only the joins between cache IDs, not a list of all
ordered binary trees. Induction on the reviewed constructors checks
that every tree of the requested order is represented. -/

namespace RKResearch.Certified.CanonicalStageMemo

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

structure Key (n : ℕ) where
  order : ℕ
  forest : ℕ
  children : List (Fin n)
  deriving DecidableEq

def insert {n : ℕ} (j : Fin n) : List (Fin n) → List (Fin n)
  | [] => [j]
  | a :: as => if j ≤ a then j :: a :: as else a :: insert j as

def merged {n : ℕ} (a b : Key n) (j : Fin n) : Key n :=
  ⟨a.order + b.order, a.forest * (b.order * b.forest), insert j a.children⟩

def decode {n : ℕ} {X : Type*} [Monoid X] (k : Key n) (d : Fin n → X) : X :=
  (k.children.map d).prod

private theorem prod_insert {n : ℕ} {X : Type*} [CommMonoid X]
    (d : Fin n → X) (j : Fin n) (as : List (Fin n)) :
    ((insert j as).map d).prod = (as.map d).prod * d j := by
  induction as with
  | nil => simp [insert]
  | cons a as ih =>
    simp only [insert]
    split
    · simp only [List.map_cons, List.prod_cons]
      ac_rfl
    · simp only [List.map_cons, List.prod_cons, ih, mul_assoc]

/-- Only joins of grades at most `p` and derivative products of grades
strictly below `p` are needed to cover all the reviewed binary trees. -/
theorem cover {n p : ℕ} {ι R : Type*} [Fintype ι] [CommSemiring R]
    {A : Matrix ι ι R} {keys : Fin n → Key n} {d : Fin n → ι → R}
    {root : Fin n} {join : Fin n → Fin n → Fin n}
    (hroot : keys root = ⟨1, 1, []⟩)
    (hjoin : ∀ i j, (keys i).order + (keys j).order ≤ p →
      keys (join i j) = merged (keys i) (keys j) j)
    (hact : ∀ i, (keys i).order < p → d i = A *ᵥ decode (keys i) d)
    (t : FiniteRootedTree) (ht : (t.order:ℕ) ≤ p) :
    ∃ i, (keys i).order = (t.order:ℕ) ∧
      (keys i).forest = (t.forestFactorial:ℕ) ∧ Φ t A = decode (keys i) d := by
  induction t with
  | leaf => exact ⟨root, by rw [hroot]; rfl, by rw [hroot]; rfl,
      by rw [hroot]; rfl⟩
  | butcherProduct u v ihu ihv =>
    have hs : (u.order:ℕ) + (v.order:ℕ) ≤ p := by simpa only [order, PNat.add_coe] using ht
    have hup := u.order.pos
    obtain ⟨i, hi, fi, ui⟩ := ihu (by omega)
    obtain ⟨j, hj, fj, vj⟩ := ihv (by omega)
    have hb := hjoin i j (by rwa [hi, hj])
    have ha := hact j (by rw [hj]; omega)
    refine ⟨join i j, ?_, ?_, ?_⟩
    · simp only [hb, merged, hi, hj, order, PNat.add_coe]
    · simp only [hb, merged, fi, fj, hj, forestFactorial, PNat.mul_coe]
    · change Φ u A * (A *ᵥ Φ v A) = _
      rw [ui, vj, ← ha, hb]
      simp only [decode, merged, prod_insert]

end RKResearch.Certified.CanonicalStageMemo
