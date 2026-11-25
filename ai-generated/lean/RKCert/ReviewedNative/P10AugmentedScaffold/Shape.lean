module

public import RKCert.ReviewedNative.NativeIntegerBlock4

@[expose] public section

/-! Fixed p10 ABI with arbitrary typed data. No arithmetic payload is supplied. -/
namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerSpanClearing NativeIntegerAugmentedChecker NativeIntegerBlock4

/-- Grade ten is a destination only and deliberately has no stored basis. -/
def rank : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 8
  | 6 => 12
  | 7 => 17
  | 8 => 24
  | 9 => 26
  | _ => 0

structure Ops where
  act : ZVec 27 → ZVec 27
  out : ZVec 27 → ℤ
  d : ℤ
  e : ℤ

structure Header where
  rows : (n : ℕ) → Fin (rank n) → ZFeature 27
  leaf : Clearing (rank 1)
  actions : (l : ℕ) → Fin (rank l) → ZVec 27

/-- Literal membership data only. Every live ordered split/row/half-open
window is populated independently of a proof that it passes. -/
structure LowerPayload where
  window (k l : ℕ) (_ : 0 < k) (_ : 0 < l) (_ : k + l ≤ 9)
    (i : Fin (rank k)) (b : Block (rank l)) (j : Fin (rank l))
    (_ : lo b ≤ j.val) (_ : j.val < hi b) : Clearing (rank (k+l))

def unusedClearing {r : ℕ} : Clearing r := ⟨1, []⟩

def base (H : Header) : Candidate 27 :=
  ⟨rank, H.rows, H.leaf, H.actions, fun _ _ _ _ => unusedClearing⟩

def dispatch (L : LowerPayload) (k l : ℕ) (i : Fin (rank k)) (j : Fin (rank l)) :
    Clearing (rank (k+l)) :=
  if h : 0 < k ∧ 0 < l ∧ k + l ≤ 9 then
    L.window k l h.1 h.2.1 h.2.2 i (atIndex j) j (at_lo j) (at_hi j)
  else unusedClearing

def candidate (H : Header) (L : LowerPayload) : Candidate 27 :=
  ⟨rank, H.rows, H.leaf, H.actions, dispatch L⟩

theorem dispatch_eq_window (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k + l ≤ 9)
    (i : Fin (rank k)) (b : Block (rank l)) (j : Fin (rank l))
    (hlo : lo b ≤ j.val) (hhi : j.val < hi b) :
    dispatch L k l i j = L.window k l hk hl hp i b j hlo hhi := by
  have hd : 0 < k ∧ 0 < l ∧ k + l ≤ 9 := ⟨hk,hl,hp⟩
  have hblock : b = atIndex j := (at_eq_of_bounds b j hlo hhi).symm
  subst b
  rw [dispatch, dif_pos hd]

def checkLocalLowerPoint (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k + l ≤ 9)
    (i : Fin (rank k)) (b : Block (rank l)) (q : Fin (len b)) : Bool :=
  checkClearing (H.rows (k+l)) (joinedZ O.d (base H) k l i (index b q))
    (L.window k l hk hl hp i b (index b q) (index_lo b q) (index_hi b q))

def checkLocalLowerWindow (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k + l ≤ 9)
    (i : Fin (rank k)) (b : Block (rank l)) : Bool :=
  checkIndices (checkLocalLowerPoint O H L k l hk hl hp i b)

/-- Numerical window producers can import only the header and their <=4
clearing records, not the global dispatcher or other membership payloads. -/
def checkGivenLowerWindow (O : Ops) (H : Header) (k l : ℕ)
    (i : Fin (rank k)) (b : Block (rank l)) (P : Fin (len b) → Clearing (rank (k+l))) : Bool :=
  checkIndices fun q =>
    checkClearing (H.rows (k+l)) (joinedZ O.d (base H) k l i (index b q)) (P q)

/-- Proof-only handoff from a local checked record window into the global
declarative payload. The exact index projection is the sole extra premise. -/
theorem checkLocalLowerWindow_of_given (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k+l ≤ 9)
    (i : Fin (rank k)) (b : Block (rank l)) (P : Fin (len b) → Clearing (rank (k+l)))
    (same : ∀ q, P q = L.window k l hk hl hp i b (index b q) (index_lo b q) (index_hi b q))
    (h : checkGivenLowerWindow O H k l i b P = true) :
    checkLocalLowerWindow O H L k l hk hl hp i b = true := by
  have he :
      (fun q : Fin (len b) =>
          checkClearing (H.rows (k+l)) (joinedZ O.d (base H) k l i (index b q)) (P q)) =
        checkLocalLowerPoint O H L k l hk hl hp i b := by
    funext q
    unfold checkLocalLowerPoint
    rw [same q]
  change checkIndices (fun q : Fin (len b) =>
    checkClearing (H.rows (k+l)) (joinedZ O.d (base H) k l i (index b q)) (P q)) = true at h
  rw [he] at h
  exact h

theorem checkLocalLowerPoint_eq_product (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k+l ≤ 9)
    (i : Fin (rank k)) (b : Block (rank l)) (q : Fin (len b)) :
    checkLocalLowerPoint O H L k l hk hl hp i b q =
      checkProduct O.d (candidate H L) k l i (index b q) := by
  change checkClearing (H.rows (k+l)) (joinedZ O.d (base H) k l i (index b q))
    (L.window k l hk hl hp i b (index b q) (index_lo b q) (index_hi b q)) =
      checkClearing (H.rows (k+l)) (joinedZ O.d (base H) k l i (index b q))
        (dispatch L k l i (index b q))
  rw [dispatch_eq_window L k l hk hl hp i b (index b q) (index_lo b q) (index_hi b q)]

def ActionWindows (O : Ops) (H : Header) (l : ℕ) : Prop :=
  AllWindows (checkAction O.act (base H) l)

def PayWindows (O : Ops) (H : Header) (n : ℕ) : Prop :=
  AllWindows (fun j : Fin (rank n) => checkPayment O.out O.e n (H.rows n j))

def LowerSplitWindows (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k+l ≤ 9) : Prop :=
  ∀ (i : Fin (rank k)) (b : Block (rank l)),
    checkLocalLowerWindow O H L k l hk hl hp i b = true

/-- It is a scalar test on a joined incoming pair at grade ten, not a
clearing into a supplied terminal basis. -/
def TopSplitWindows (O : Ops) (H : Header) (k l : ℕ) : Prop :=
  ∀ i : Fin (rank k), AllWindows fun j : Fin (rank l) =>
    checkPayment O.out O.e 10 (joinedZ O.d (base H) k l i j)

theorem ActionWindows.get (O : Ops) (H : Header) (L : LowerPayload) (l : ℕ)
    (h : ActionWindows O H l) (j : Fin (rank l)) :
    checkAction O.act (candidate H L) l j = true := by
  change checkAction O.act (base H) l j = true
  exact AllWindows.get h j

theorem PayWindows.get (O : Ops) (H : Header) (L : LowerPayload) (n : ℕ)
    (h : PayWindows O H n) (j : Fin (rank n)) :
    checkPayment O.out O.e n ((candidate H L).rows n j) = true := by
  change checkPayment O.out O.e n (H.rows n j) = true
  exact AllWindows.get h j

theorem LowerSplitWindows.get (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hp : k+l ≤ 9)
    (h : LowerSplitWindows O H L k l hk hl hp) (i : Fin (rank k)) (j : Fin (rank l)) :
    checkProduct O.d (candidate H L) k l i j = true := by
  let b : Block (rank l) := atIndex j
  let q : Fin (len b) := offset b j (at_lo j) (at_hi j)
  have hw : checkIndices (checkLocalLowerPoint O H L k l hk hl hp i b) = true := h i b
  have hp' := checkIndices_get hw q
  rw [checkLocalLowerPoint_eq_product] at hp'
  have hj : index b q = j := index_offset b j _ _
  exact (congrArg (fun j₀ : Fin (rank l) =>
    checkProduct O.d (candidate H L) k l i j₀ = true) hj).mp hp'

theorem TopSplitWindows.get (O : Ops) (H : Header) (L : LowerPayload) (k l : ℕ)
    (h : TopSplitWindows O H k l) (i : Fin (rank k)) (j : Fin (rank l)) :
    checkPayment O.out O.e 10 (joinedZ O.d (candidate H L) k l i j) = true := by
  change checkPayment O.out O.e 10 (joinedZ O.d (base H) k l i j) = true
  exact AllWindows.get (h i) j

end RKResearch.Certified.P10AugmentedScaffold
