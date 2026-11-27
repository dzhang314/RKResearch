module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Exact rooted-tree order via integer Gram matrices

The last coordinate carries the stage denominator raised to the tree's grade.
At each grade the integer sum of squared defects vanishes exactly when
every tree of that grade pays the reviewed order condition.
-/

namespace RKResearch.Certified.RootedTreeGram

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

abbrev Cov (s : ℕ) := Matrix (Fin (s+1)) (Fin (s+1)) ℤ

variable {s : ℕ}

/-- Integer numerator profile with an extra coordinate for stage homogeneity. -/
def feature (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (t : FiniteRootedTree) :
    Fin (s+1) → ℤ :=
  Fin.snoc (fun i => (t.forestFactorial : ℤ) * Φ t M i) (d^((t.order : ℕ)-1))

/-- Block diagonal join action: `l M` on stages, and multiplication by `d` on the added coordinate. -/
def branch (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (l : ℕ) : Cov s :=
  fun i => Fin.lastCases (Fin.snoc 0 d)
    (fun j => Fin.snoc (fun k => (l : ℤ) * M j k) 0) i

/-- Entrywise product of covariance matrices. -/
def entryMul (A B : Cov s) : Cov s :=
  fun i j => A i j * B i j

theorem entryMul_zero (A : Cov s) : entryMul A 0 = 0 := by
  ext i j; simp [entryMul]
theorem zero_entryMul (A : Cov s) : entryMul 0 A = 0 := by
  ext i j; simp [entryMul]
theorem entryMul_add (A B C : Cov s) : entryMul A (B+C) = entryMul A B + entryMul A C := by
  ext i j; simp [entryMul, mul_add]
theorem add_entryMul (A B C : Cov s) : entryMul (A+B) C = entryMul A C + entryMul B C := by
  ext i j; simp [entryMul, add_mul]

/-- The feature of a root attachment is an entrywise product of the two
smaller features after the right feature's linear action. -/
theorem feature_join (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ)
    (t u : FiniteRootedTree) :
    feature M d (t ◂ u) =
      feature M d t * (branch M d u.order *ᵥ feature M d u) := by
  funext a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have ht := t.order.pos
    have hu := u.order.pos
    have he : ((t ◂ u).order : ℕ)-1 =
        ((t.order : ℕ)-1) + (1 + ((u.order : ℕ)-1)) := by
      simp only [order, PNat.add_coe]
      omega
    simp only [feature, Pi.mul_apply, branch, Matrix.mulVec, dotProduct,
      Fin.lastCases_last, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, he, pow_add, pow_one]
  · simp only [feature, Pi.mul_apply, branch, Matrix.mulVec, dotProduct,
      Fin.lastCases_castSucc, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      zero_mul, add_zero, forestFactorial, PNat.mul_coe, Nat.cast_mul, Φ,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Outer product of a real integer feature with itself. -/
def outer (v : Fin (s+1) → ℤ) : Cov s := Matrix.vecMulVec v v

/-- Bilinearity separates independent choices of the two rooted subtrees. -/
theorem outer_join (U : Cov s) (v w : Fin (s+1) → ℤ) :
    outer (v * (U *ᵥ w)) = entryMul (outer v) (U * outer w * Uᵀ) := by
  simp only [outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  ext i j
  simp only [Matrix.vecMulVec_apply, entryMul, Pi.mul_apply]
  ring

/-- Covariance aggregated over any list of tree expressions. -/
def covList (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (ts : List FiniteRootedTree) : Cov s :=
  (ts.map (outer ∘ feature M d)).sum

@[simp] theorem cov_nil (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) :
    covList M d [] = 0 := rfl

@[simp] theorem cov_cons (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ)
    (t : FiniteRootedTree) (ts : List FiniteRootedTree) :
    covList M d (t :: ts) = outer (feature M d t) + covList M d ts := rfl

@[simp] theorem cov_append (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ)
    (ts us : List FiniteRootedTree) :
    covList M d (ts ++ us) = covList M d ts + covList M d us := by
  simp [covList, List.sum_append]

theorem cov_map_join (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ)
    (t : FiniteRootedTree) (us : List FiniteRootedTree) (l : ℕ)
    (hl : ∀ u ∈ us, (u.order : ℕ) = l) :
    covList M d (us.map (butcherProduct t)) =
      entryMul (outer (feature M d t)) (branch M d l * covList M d us * (branch M d l)ᵀ) := by
  induction us with
  | nil => simp [entryMul_zero]
  | cons u us ih =>
    simp only [List.map_cons, cov_cons, Matrix.mul_add, Matrix.add_mul, entryMul_add,
      feature_join, outer_join, hl u List.mem_cons_self]
    rw [ih (fun v hv => hl v (List.mem_cons_of_mem u hv))]

theorem cov_flatMap_join (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ)
    (ts us : List FiniteRootedTree) (l : ℕ)
    (hl : ∀ u ∈ us, (u.order : ℕ) = l) :
    covList M d (ts.flatMap (fun t => us.map (butcherProduct t))) =
      entryMul (covList M d ts) (branch M d l * covList M d us * (branch M d l)ᵀ) := by
  induction ts with
  | nil => simp [zero_entryMul]
  | cons t ts ih =>
    simp only [List.flatMap_cons, cov_append, cov_map_join M d t us l hl, ih,
      cov_cons, add_entryMul]

/-- Covariance at grade `n`, where the tree order is `n+1`. -/
def covTrees (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (n : ℕ) : Cov s :=
  covList M d (treesOfOrderSucc n)

theorem covTrees_zero (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) :
    covTrees M d 0 = outer 1 := by
  simp only [covTrees, treesOfOrderSucc, cov_cons, cov_nil, add_zero]
  congr 1
  funext a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [feature, order]
  · simp [feature, forestFactorial, Φ]

/-- The degree iteration only combines two already-computed covariances.
The branch sizes in `step` are determined by the grade split. -/
def step (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (C : ℕ → Cov s) (n : ℕ) :
    Cov s :=
  ((List.finRange (n+1)).map fun i =>
    let B := branch M d (n-i.val+1)
    entryMul (C i.val) (B * C (n-i.val) * Bᵀ)).sum

theorem covTrees_succ (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (n : ℕ) :
    covTrees M d (n+1) = step M d (covTrees M d) n := by
  unfold covTrees
  rw [treesOfOrderSucc]
  unfold step
  generalize List.finRange (n+1) = is
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons, cov_append, List.map_cons, List.sum_cons, ih]
    rw [cov_flatMap_join M d _ _ (n-i.val+1)]
    intro u hu
    exact (mem_treesOfOrderSucc _ _).mp hu

/-- A separately supplied, finite covariance trace is valid if it starts
at the all-ones matrix and pays the dynamic recurrence. -/
structure Trace (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (p : ℕ) where
  cov : ℕ → Cov s
  base : cov 0 = outer 1
  next : ∀ n, n+1 < p → cov (n+1) = step M d cov n

theorem Trace.correct {M : Matrix (Fin s) (Fin s) ℤ} {d : ℤ} {p : ℕ}
    (C : Trace M d p) (n : ℕ) (hn : n < p) :
    C.cov n = covTrees M d n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [C.base, covTrees_zero]
    | succ n =>
      rw [C.next n hn, covTrees_succ]
      unfold step
      congr 1
      apply List.map_congr_left
      intro i _
      rw [ih i.val (by have := i.isLt; omega) (by have := i.isLt; omega),
        ih (n-i.val) (by omega) (by omega)]

/-- The tested linear form for order `n` on the augmented numerator feature. -/
def output (w : Fin s → ℤ) (e : ℤ) (n : ℕ) : Fin (s+1) → ℤ :=
  Fin.snoc (fun i => (n : ℤ) * w i) (-e)

/-- Sum-of-squares readout of the covariance. -/
def energy (C : Cov s) (v : Fin (s+1) → ℤ) : ℤ :=
  v ⬝ᵥ (C *ᵥ v)

theorem energy_outer (v x : Fin (s+1) → ℤ) :
    energy (outer x) v = (v ⬝ᵥ x)^2 := by
  simp only [energy, outer, Matrix.vecMulVec_mulVec, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm x v, pow_two]

theorem output_feature (M : Matrix (Fin s) (Fin s) ℤ) (w : Fin s → ℤ) (d e : ℤ)
    (t : FiniteRootedTree) :
    output w e t.order ⬝ᵥ feature M d t =
      (t.factorial : ℤ) * (w ⬝ᵥ Φ t M) - e*d^((t.order : ℕ)-1) := by
  simp only [dotProduct, output, feature, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, factorial, PNat.mul_coe, Nat.cast_mul]
  rw [sub_eq_add_neg, neg_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem energy_covList (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ)
    (ts : List FiniteRootedTree) (v : Fin (s+1) → ℤ) :
    energy (covList M d ts) v = (ts.map fun t => (v ⬝ᵥ feature M d t)^2).sum := by
  induction ts with
  | nil => simp [energy]
  | cons t ts ih =>
    simp only [cov_cons, List.map_cons, List.sum_cons]
    have h : ∀ C D : Cov s, energy (C+D) v = energy C v + energy D v := by
      intro C D
      simp only [energy, Matrix.add_mulVec, dotProduct_add]
    rw [h, energy_outer, ih]

private theorem sum_squares_eq_zero_iff {α : Type*} (u : α → ℤ) (ts : List α) :
    (ts.map fun t => (u t)^2).sum = 0 ↔ ∀ t ∈ ts, u t = 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have htail : 0 ≤ (ts.map fun t => (u t)^2).sum := by
      apply List.sum_nonneg
      intro i hi
      obtain ⟨y,-,rfl⟩ := List.mem_map.mp hi
      exact sq_nonneg (u y)
    constructor
    · intro h
      simp only [List.map_cons, List.sum_cons] at h
      have ha : (u t)^2 = 0 := by have := sq_nonneg (u t); omega
      have hb : (ts.map fun t => (u t)^2).sum = 0 := by omega
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ha
      · exact ih.mp hb _ hx
    · intro h
      have hh := h t List.mem_cons_self
      have hh' := ih.mpr (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp [hh, hh']

/-- The integer Gram recurrence certifies every reviewed rooted-tree
equation, without needing to evaluate any tree features in the check. -/
theorem Trace.paid {M : Matrix (Fin s) (Fin s) ℤ} {w : Fin s → ℤ}
    {d e : ℤ} {p : ℕ} (C : Trace M d p)
    (h : ∀ n < p, energy (C.cov n) (output w e (n+1)) = 0) :
    ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
      (t.factorial : ℤ) * (w ⬝ᵥ Φ t M) = e*d^((t.order : ℕ)-1) := by
  intro t ht
  have hpos := t.order.pos
  have hgrade : (t.order : ℕ)-1 < p := by omega
  have hmember := (mem_treesOfOrderSucc ((t.order : ℕ)-1) t).mpr (by omega)
  have hz := h _ hgrade
  rw [C.correct _ hgrade, covTrees, energy_covList] at hz
  have hp := (sum_squares_eq_zero_iff _ _).mp hz _ hmember
  rw [show ((t.order : ℕ)-1)+1 = t.order by omega, output_feature] at hp
  exact sub_eq_zero.mp hp

/-- Transfer a paid integer Gram trace to the reviewed coefficients.
The target ring need only make the two scales units. -/
theorem Trace.hasOrder {R : Type*} [CommRing R] {M : Matrix (Fin s) (Fin s) ℤ}
    {w : Fin s → ℤ} {d e : ℤ} {p : ℕ} (C : Trace M d p)
    (h : ∀ n < p, energy (C.cov n) (output w e (n+1)) = 0)
    (f : ℤ →+* R) (U : Matrix (Fin s) (Fin s) R) (b : Fin s → R)
    (hA : M.map f = f d • U) (hb : f ∘ w = f e • b)
    (hd : IsUnit (f d)) (he : IsUnit (f e)) :
    HasOrder p U b :=
  hasOrder_of_scaled_moments f hA hb hd he (C.paid h)


/-- Only the stage coordinates are multiplied by the right tree order.
The augmented coordinate carries its own denominator block. -/
def factors (s l : ℕ) : Fin (s+1) → ℤ := Fin.snoc (fun _ => (l : ℤ)) 1

def reweight (l : ℕ) (C : Cov s) : Cov s :=
  fun i j => factors s l i * factors s l j * C i j

theorem reweight_smul (l : ℕ) (a : ℤ) (C : Cov s) :
    reweight l (a • C) = a • reweight l C := by
  ext i j
  simp only [reweight, Matrix.smul_apply, smul_eq_mul]
  ring

theorem entryMul_smul (a b : ℤ) (C D : Cov s) :
    entryMul (a • C) (b • D) = (a*b) • entryMul C D := by
  ext i j
  simp only [entryMul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem split_branch (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (l : ℕ) :
    branch M d l = Matrix.diagonal (factors s l) * branch M d 1 := by
  ext i j
  rw [Matrix.diagonal_mul]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [branch, factors]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [branch, factors]
    · simp [branch, factors]

theorem branch_reweight (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (l : ℕ) (C : Cov s) :
    branch M d l * C * (branch M d l)ᵀ =
      reweight l (branch M d 1 * C * (branch M d 1)ᵀ) := by
  rw [split_branch M d l, Matrix.transpose_mul, Matrix.diagonal_transpose]
  have hr : Matrix.diagonal (factors s l) * branch M d 1 * C *
        ((branch M d 1)ᵀ * Matrix.diagonal (factors s l)) =
      Matrix.diagonal (factors s l) * (branch M d 1 * C * (branch M d 1)ᵀ) *
        Matrix.diagonal (factors s l) := by simp only [mul_assoc]
  rw [hr]
  ext i j
  simp only [reweight, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

private theorem sum_smul_list {α : Type*} (a : ℤ) (f : α → Cov s) (xs : List α) :
    ((xs.map fun i => a • f i).sum : Cov s) = a • (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- Factorization of a covariance trace by integer contents.
This representation reduces certificate sizes without using division:
the supplied multipliers may be checked as ordinary integer equalities. -/
structure FactoredTrace (M : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) (p : ℕ) where
  cov : ℕ → Cov s
  left : ℕ → Cov s
  right : ℕ → Cov s
  covScale : ℕ → ℤ
  leftScale : ℕ → ℤ
  rightScale : ℕ → ℤ
  common : ℕ → ℤ
  lhs : ℕ → ℤ
  coeff : ℕ → ℕ → ℤ
  base : covScale 0 • cov 0 = outer 1
  hleft : ∀ n, n+1 < p → branch M d 1 * cov n = leftScale n • left n
  hright : ∀ n, n+1 < p → left n * (branch M d 1)ᵀ = rightScale n • right n
  hlhs : ∀ n, n+1 < p → covScale (n+1) = common n * lhs n
  hcoeff : ∀ n, n+1 < p → ∀ i : Fin (n+1),
    covScale i.val * (covScale (n-i.val) * leftScale (n-i.val) * rightScale (n-i.val)) =
      common n * coeff n i.val
  next : ∀ n, n+1 < p → lhs n • cov (n+1) =
    ((List.finRange (n+1)).map fun i => coeff n i.val •
      entryMul (cov i.val) (reweight (n-i.val+1) (right (n-i.val)))).sum

theorem FactoredTrace.conjugate {M : Matrix (Fin s) (Fin s) ℤ} {d : ℤ} {p : ℕ}
    (F : FactoredTrace M d p) (k : ℕ) (hk : k+1 < p) :
    branch M d 1 * (F.covScale k • F.cov k) * (branch M d 1)ᵀ =
      (F.covScale k * F.leftScale k * F.rightScale k) • F.right k := by
  rw [Matrix.mul_smul, F.hleft k hk, Matrix.smul_mul, Matrix.smul_mul, F.hright k hk]
  simp only [← mul_smul, mul_assoc]

/-- Convert factored arithmetic receipts to an ordinary exact Gram trace. -/
def FactoredTrace.toTrace {M : Matrix (Fin s) (Fin s) ℤ} {d : ℤ} {p : ℕ}
    (F : FactoredTrace M d p) : Trace M d p where
  cov n := F.covScale n • F.cov n
  base := F.base
  next n hn := by
    simp only [step, F.hlhs n hn, mul_smul, F.next n hn, ← sum_smul_list]
    congr 1
    apply List.map_congr_left
    intro i _
    have hi := i.isLt
    rw [branch_reweight M d (n-i.val+1), F.conjugate _ (by omega), reweight_smul,
      entryMul_smul, F.hcoeff n hn i, mul_smul]

theorem FactoredTrace.hasOrder {R : Type*} [CommRing R] {M : Matrix (Fin s) (Fin s) ℤ}
    {w : Fin s → ℤ} {d e : ℤ} {p : ℕ} (F : FactoredTrace M d p)
    (h : ∀ n < p, energy (F.cov n) (output w e (n+1)) = 0)
    (f : ℤ →+* R) (U : Matrix (Fin s) (Fin s) R) (b : Fin s → R)
    (hA : M.map f = f d • U) (hb : f ∘ w = f e • b)
    (hd : IsUnit (f d)) (he : IsUnit (f e)) :
    HasOrder p U b := by
  apply F.toTrace.hasOrder _ f U b hA hb hd he
  intro n hn
  change energy (F.covScale n • F.cov n) _ = 0
  unfold energy
  rw [Matrix.smul_mulVec, dotProduct_smul]
  change F.covScale n * energy (F.cov n) _ = 0
  rw [h n hn, mul_zero]

#print axioms FactoredTrace.hasOrder
end RKResearch.Certified.RootedTreeGram
