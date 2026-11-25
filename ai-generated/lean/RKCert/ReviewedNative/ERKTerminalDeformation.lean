module

public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Source-only candidate: weighted terminal row deformation.
The core uses literal ordered trees and a finite mixed-moment recurrence. -/

namespace RKResearch.Certified.Graded.TerminalDeformation

open RKResearch FiniteRootedTree
open scoped BigOperators FiniteRootedTree Matrix

variable {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ]
variable {K : Type*} [CommRing K]

abbrev ord (t : FiniteRootedTree) : ℕ := (t.order : ℕ)

private theorem ord_graft (u v : FiniteRootedTree) : ord (u ◂ v) = ord u + ord v := by
  simp only [ord, FiniteRootedTree.order, PNat.add_coe]

theorem normTree_graft (A : Matrix ι ι K) (u v : FiniteRootedTree) :
    normTree A (u ◂ v) =
      normTree A u * ((ord v : K) • mat A (normTree A v)) := by
  change normTree A (u # (.leaf ◂ v)) = _
  rw [normTree_rootedSum, normTree_unary]

/-- The appended rows see only the original physical rows. -/
def attach (A : Matrix ι ι K) (D : Matrix σ ι K) : Matrix (ι ⊕ σ) (ι ⊕ σ) K :=
  Matrix.fromBlocks A (0 : Matrix ι σ K) D (0 : Matrix σ σ K)

theorem attach_mulVec_inl (A : Matrix ι ι K) (D : Matrix σ ι K) (v : ι ⊕ σ → K) (i : ι) :
    (attach A D *ᵥ v) (Sum.inl i) = (A *ᵥ (v ∘ Sum.inl)) i := by
  simp [attach, Matrix.fromBlocks_mulVec]

theorem attach_mulVec_inr (A : Matrix ι ι K) (D : Matrix σ ι K) (v : ι ⊕ σ → K) (i : σ) :
    (attach A D *ᵥ v) (Sum.inr i) = (D *ᵥ (v ∘ Sum.inl)) i := by
  simp [attach, Matrix.fromBlocks_mulVec]

theorem Φ_attach_inl (A : Matrix ι ι K) (D : Matrix σ ι K) (t : FiniteRootedTree) :
    Φ t (attach A D) ∘ Sum.inl = Φ t A := by
  induction t with
  | leaf => rfl
  | butcherProduct u v ihu ihv =>
    funext i
    have eu : Φ u (attach A D) (Sum.inl i) = Φ u A i := congrFun ihu i
    change Φ u (attach A D) (Sum.inl i) * (attach A D *ᵥ Φ v (attach A D)) (Sum.inl i) =
      Φ u A i * (A *ᵥ Φ v A) i
    rw [eu, attach_mulVec_inl, ihv]

theorem normTree_attach_inl (A : Matrix ι ι K) (D : Matrix σ ι K) (t : FiniteRootedTree) :
    normTree (attach A D) t ∘ Sum.inl = normTree A t := by
  funext i
  have eq : Φ t (attach A D) (Sum.inl i) = Φ t A i := congrFun (Φ_attach_inl A D t) i
  simp only [Function.comp_apply, normTree, Pi.smul_apply, eq]

/-- Row primitive law paid against actual original-tree columns. -/
def RowLaw (A : Matrix ι ι K) (D : Matrix σ ι K) (c : σ → K) (p : ℕ) : Prop :=
  ∀ x t, ord t < p → (ord t : K) * row (D x) (normTree A t) = c x ^ ord t

/-- A pure appended bank from an actual certified primitive row law. -/
theorem normTree_attach_inr_pure {A : Matrix ι ι K} {D : Matrix σ ι K}
    {c : σ → K} {p : ℕ} (law : RowLaw A D c p) (x : σ)
    (t : FiniteRootedTree) (pay : ord t ≤ p) :
    normTree (attach A D) t (Sum.inr x) = c x ^ (ord t - 1) := by
  revert pay
  induction t with
  | leaf =>
    intro _
    simp [ord]
  | butcherProduct u v ihu _ =>
    intro pay
    have hu : 0 < ord u := u.order.pos
    have hv : 0 < ord v := v.order.pos
    have hp := ord_graft u v
    have pu : ord u ≤ p := by omega
    have pv : ord v < p := by omega
    have hs : (ord u - 1) + ord v = ord (u ◂ v) - 1 := by omega
    rw [normTree_graft, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, ihu pu,
      mat_apply, attach_mulVec_inr, normTree_attach_inl]
    change c x ^ (ord u - 1) * ((ord v : K) * row (D x) (normTree A v)) = _
    rw [law x v pv, ← pow_add, hs]

/-- All terminal copies use the same baseline clock row and one signed contrast. -/
def terminalMatrix (A : Matrix ι ι K) (D : Matrix σ ι K)
    (η : ι → K) (lam : τ → K) : Matrix (ι ⊕ (σ × τ)) (ι ⊕ (σ × τ)) K :=
  attach A (fun j i => D j.1 i + lam j.2 * η i)

def terminalWeight (w : σ → τ → K) : ι ⊕ (σ × τ) → K :=
  Sum.elim (fun _ => 0) (fun j => w j.1 j.2)

def Quiet (A : Matrix ι ι K) (η : ι → K) (h : ℕ) : Prop :=
  ∀ t, ord t ≤ h → row η (normTree A t) = 0

def branchContrast (A : Matrix ι ι K) (η : ι → K) (t : FiniteRootedTree) : K :=
  (ord t : K) * row η (normTree A t)

theorem normTree_terminal_inl (A : Matrix ι ι K) (D : Matrix σ ι K)
    (η : ι → K) (lam : τ → K) (t : FiniteRootedTree) :
    normTree (terminalMatrix A D η lam) t ∘ Sum.inl = normTree A t :=
  normTree_attach_inl A _ t

theorem terminal_mat_inr (A : Matrix ι ι K) (D : Matrix σ ι K) (η : ι → K)
    (lam : τ → K) (v : ι ⊕ (σ × τ) → K) (x : σ) (l : τ) :
    mat (terminalMatrix A D η lam) v (Sum.inr (x,l)) =
      row (D x) (v ∘ Sum.inl) + lam l * row η (v ∘ Sum.inl) := by
  let B : Matrix (σ × τ) ι K := fun j i => D j.1 i + lam j.2 * η i
  have act : mat (terminalMatrix A D η lam) v (Sum.inr (x,l)) =
      (B *ᵥ (v ∘ Sum.inl)) (x,l) := by
    change (attach A B *ᵥ v) (Sum.inr (x,l)) = _
    exact attach_mulVec_inr A B v (x,l)
  rw [act]
  change B (x,l) ⬝ᵥ (v ∘ Sum.inl) = _
  have hrow : B (x,l) = D x + lam l • η := by
    funext i
    change D x i + lam l * η i = (D x + lam l • η) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hrow, add_dotProduct, smul_dotProduct, smul_eq_mul, row_apply]

theorem terminal_graft {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K} {p : ℕ}
    (law : RowLaw A D c p) (η : ι → K) (lam : τ → K) (u v : FiniteRootedTree)
    (pv : ord v < p) (x : σ) (l : τ) :
    normTree (terminalMatrix A D η lam) (u ◂ v) (Sum.inr (x,l)) =
      normTree (terminalMatrix A D η lam) u (Sum.inr (x,l)) *
        (c x ^ ord v + lam l * branchContrast A η v) := by
  have act : (ord v : K) *
      mat (terminalMatrix A D η lam) (normTree (terminalMatrix A D η lam) v)
        (Sum.inr (x,l)) = c x ^ ord v + lam l * branchContrast A η v := by
    rw [terminal_mat_inr, normTree_terminal_inl, mul_add, law x v pv]
    unfold branchContrast
    ring
  rw [normTree_graft, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, act]

theorem nodes_terminal_inr {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K}
    {p h : ℕ} (law : RowLaw A D c p) {η : ι → K} (quiet : Quiet A η h)
    (p1 : 1 < p) (h1 : 1 ≤ h) (lam : τ → K) (x : σ) (l : τ) :
    nodes (terminalMatrix A D η lam) (Sum.inr (x,l)) = c x := by
  have base : row (D x) (1 : ι → K) = c x := by
    simpa [ord] using law x .leaf (by simpa [ord] using p1)
  have z : row η (1 : ι → K) = 0 := by
    simpa using quiet .leaf (by simpa [ord] using h1)
  change mat (terminalMatrix A D η lam) 1 (Sum.inr (x,l)) = c x
  rw [terminal_mat_inr]
  change row (D x) (1 : ι → K) + lam l * row η (1 : ι → K) = c x
  rw [base, z, mul_zero, add_zero]

def powerMass (c a : σ → K) (k : ℕ) : K := ∑ x, a x * c x ^ k

def sampledMoment (β a : σ → K) (x : σ) (j : ℕ) : K :=
  if j = 0 then β x else if j = 1 then a x else 0

def CopyMoments (lam : τ → K) (w : σ → τ → K) (β a : σ → K) (p : ℕ) : Prop :=
  ∀ x j, j < p → (∑ l, w x l * lam l ^ j) = sampledMoment β a x j

def expectedMoment (c β a : σ → K) (k j : ℕ) : K :=
  if j = 0 then powerMass c β k else if j = 1 then powerMass c a k else 0

def momentTerm (M : Matrix (ι ⊕ (σ × τ)) (ι ⊕ (σ × τ)) K)
    (c : σ → K) (lam : τ → K) (w : σ → τ → K) (k j : ℕ)
    (t : FiniteRootedTree) (x : σ) (l : τ) : K :=
  w x l * lam l ^ j * c x ^ k * normTree M t (Sum.inr (x,l))

def mixedMoment (M : Matrix (ι ⊕ (σ × τ)) (ι ⊕ (σ × τ)) K)
    (c : σ → K) (lam : τ → K) (w : σ → τ → K) (k j : ℕ) (t : FiniteRootedTree) : K :=
  ∑ x, ∑ l, momentTerm M c lam w k j t x l

private theorem sum_add_scaled (f g : σ → τ → K) (a : K) :
    (∑ x, ∑ l, (f x l + a * g x l)) = (∑ x, ∑ l, f x l) + a * (∑ x, ∑ l, g x l) := by
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem mixed_graft {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K} {p : ℕ}
    (law : RowLaw A D c p) (η : ι → K) (lam : τ → K) (w : σ → τ → K)
    (u v : FiniteRootedTree) (pv : ord v < p) (k j : ℕ) :
    mixedMoment (terminalMatrix A D η lam) c lam w k j (u ◂ v) =
      mixedMoment (terminalMatrix A D η lam) c lam w (k + ord v) j u +
        branchContrast A η v * mixedMoment (terminalMatrix A D η lam) c lam w k (j + 1) u := by
  let M := terminalMatrix A D η lam
  change mixedMoment M c lam w k j (u ◂ v) =
    mixedMoment M c lam w (k + ord v) j u +
      branchContrast A η v * mixedMoment M c lam w k (j + 1) u
  have term (x : σ) (l : τ) :
      momentTerm M c lam w k j (u ◂ v) x l =
      momentTerm M c lam w (k + ord v) j u x l +
        branchContrast A η v * momentTerm M c lam w k (j + 1) u x l := by
    unfold momentTerm M
    rw [terminal_graft law η lam u v pv x l]
    simp only [pow_add, pow_one]
    ring
  unfold mixedMoment
  simp_rw [term]
  exact sum_add_scaled _ _ _

private theorem mixed_leaf {lam : τ → K} {w : σ → τ → K} {β a : σ → K} {p : ℕ}
    (M : Matrix (ι ⊕ (σ × τ)) (ι ⊕ (σ × τ)) K) (c : σ → K) (k j : ℕ)
    (copy : CopyMoments lam w β a p) (pay : j < p) :
    mixedMoment M c lam w k j .leaf = expectedMoment c β a k j := by
  unfold mixedMoment momentTerm
  simp only [normTree_leaf, Pi.one_apply, mul_one]
  have h (x : σ) : (∑ l, w x l * lam l ^ j * c x ^ k) =
      sampledMoment β a x j * c x ^ k := by
    rw [← Finset.sum_mul, copy x j pay]
  simp_rw [h]
  by_cases e0 : j = 0 <;> by_cases e1 : j = 1 <;> simp [e0, e1, sampledMoment, expectedMoment, powerMass]

/-- Literal mixed tree moments are preserved at the additive budget. -/
theorem mixed_paid {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K}
    {p h : ℕ} (law : RowLaw A D c p) {η : ι → K} (quiet : Quiet A η h)
    {lam : τ → K} {w : σ → τ → K} {β a : σ → K} (copy : CopyMoments lam w β a p)
    (ann : ∀ k, k + h + 2 ≤ p → powerMass c a k = 0)
    (t : FiniteRootedTree) (k j : ℕ) (pay : k + j + ord t ≤ p) :
    mixedMoment (terminalMatrix A D η lam) c lam w k j t =
      expectedMoment c β a (k + (ord t - 1)) j := by
  revert k j
  induction t with
  | leaf =>
    intro k j pay
    have jp : j < p := by
      change k + j + 1 ≤ p at pay
      omega
    simpa [ord] using mixed_leaf (terminalMatrix A D η lam) c k j copy jp
  | butcherProduct u v ihu _ =>
    intro k j pay
    have hu : 0 < ord u := u.order.pos
    have hv : 0 < ord v := v.order.pos
    have size := ord_graft u v
    have pv : ord v < p := by omega
    have p1 : k + ord v + j + ord u ≤ p := by omega
    have p2 : k + (j + 1) + ord u ≤ p := by omega
    have shift : k + ord v + (ord u - 1) = k + (ord (u ◂ v) - 1) := by omega
    have kill : branchContrast A η v * expectedMoment c β a (k + (ord u - 1)) (j + 1) = 0 := by
      by_cases e : j = 0
      · subst j
        by_cases q : ord v ≤ h
        · simp [branchContrast, quiet v q]
        · have pk : (k + (ord u - 1)) + h + 2 ≤ p := by omega
          simp [expectedMoment, ann _ pk]
      · simp [expectedMoment, e]
    rw [mixed_graft law η lam w u v pv k j,
      ihu (k + ord v) j p1, ihu k (j + 1) p2, shift, kill, add_zero]

theorem terminal_normalizedOutput {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K}
    {p h : ℕ} (law : RowLaw A D c p) {η : ι → K} (quiet : Quiet A η h)
    {lam : τ → K} {w : σ → τ → K} {β a : σ → K} (copy : CopyMoments lam w β a p)
    (ann : ∀ k, k + h + 2 ≤ p → powerMass c a k = 0)
    (t : FiniteRootedTree) (pay : ord t ≤ p) :
    row (terminalWeight (ι := ι) w) (normTree (terminalMatrix A D η lam) t) =
      powerMass c β (ord t - 1) := by
  simpa [row_apply, dotProduct, terminalWeight, Fintype.sum_sum_type, Fintype.sum_prod_type,
    mixedMoment, momentTerm, expectedMoment] using
      mixed_paid law quiet copy ann t 0 0 (by simpa using pay)

theorem terminal_hasOrder {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K}
    {p h : ℕ} (law : RowLaw A D c p) {η : ι → K} (quiet : Quiet A η h)
    {lam : τ → K} {w : σ → τ → K} {β a : σ → K} (copy : CopyMoments lam w β a p)
    (ann : ∀ k, k + h + 2 ≤ p → powerMass c a k = 0)
    (quad : ∀ k, k + 1 ≤ p → ((k + 1 : ℕ) : K) * powerMass c β k = 1) :
    HasOrder p (terminalMatrix A D η lam) (terminalWeight (ι := ι) w) := by
  intro t pay
  have pos : 0 < ord t := t.order.pos
  have shape : ord t - 1 + 1 = ord t := by omega
  have hc := quad (ord t - 1) (by rw [shape]; exact pay)
  rw [shape] at hc
  have normalized : (ord t : K) *
      row (terminalWeight (ι := ι) w) (normTree (terminalMatrix A D η lam) t) = 1 := by
    rw [terminal_normalizedOutput law quiet copy ann t pay]
    exact hc
  simpa only [row_apply, normTree, dotProduct_smul, smul_eq_mul, ← mul_assoc,
    FiniteRootedTree.factorial, PNat.mul_coe, Nat.cast_mul] using normalized

theorem terminal_outgoingMass (A : Matrix ι ι K) (D : Matrix σ ι K) (η : ι → K)
    {lam : τ → K} {w : σ → τ → K} {β a : σ → K} {p : ℕ}
    (copy : CopyMoments lam w β a p) (p1 : 1 < p) (q : ι ⊕ (σ × τ) → K) (x : σ) :
    (∑ l, w x l * mat (terminalMatrix A D η lam) q (Sum.inr (x,l))) =
      β x * row (D x) (q ∘ Sum.inl) + a x * row η (q ∘ Sum.inl) := by
  have c0 : (∑ l, w x l) = β x := by
    simpa [sampledMoment] using copy x 0 (by omega)
  have c1 : (∑ l, w x l * lam l) = a x := by
    simpa [sampledMoment] using copy x 1 p1
  calc
    _ = (∑ l, w x l) * row (D x) (q ∘ Sum.inl) +
        (∑ l, w x l * lam l) * row η (q ∘ Sum.inl) := by
      simp_rw [terminal_mat_inr, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    _ = _ := by rw [c0, c1]


theorem nodes_attach_inl (A : Matrix ι ι K) (D : Matrix σ ι K) :
    nodes (attach A D) ∘ Sum.inl = nodes A := by
  funext i
  exact attach_mulVec_inl A D (1 : ι ⊕ σ → K) i

theorem monomialStageDefect_attach_inl (A : Matrix ι ι K) (D : Matrix σ ι K) (d : ℕ) :
    monomialStageDefect (attach A D) d ∘ Sum.inl = monomialStageDefect A d := by
  funext i
  have nc := nodes_attach_inl A D
  have np : (nodes (attach A D) ^ d) ∘ Sum.inl = nodes A ^ d := by
    funext j
    simpa only [Function.comp_apply, Pi.pow_apply] using
      congrArg (fun x : K => x ^ d) (congrFun nc j)
  have ni : nodes (attach A D) (Sum.inl i) = nodes A i := congrFun nc i
  change ((d + 1 : ℕ) : K) * (attach A D *ᵥ nodes (attach A D) ^ d) (Sum.inl i) -
      nodes (attach A D) (Sum.inl i) ^ (d + 1) =
    ((d + 1 : ℕ) : K) * (A *ᵥ nodes A ^ d) i - nodes A i ^ (d + 1)
  rw [attach_mulVec_inl, np, ni]

noncomputable def clockMass {α : Type*} [Fintype α]
    (A : Matrix α α K) (b v : α → K) (z : K) : K := by
  classical
  exact ∑ i, if nodes A i = z then b i * v i else 0

open scoped Classical in
theorem terminal_clockMass {A : Matrix ι ι K} {D : Matrix σ ι K} {c : σ → K}
    {p h : ℕ} (law : RowLaw A D c p) {η : ι → K} (quiet : Quiet A η h)
    {lam : τ → K} {w : σ → τ → K} {β a : σ → K} (copy : CopyMoments lam w β a p)
    (p1 : 1 < p) (h1 : 1 ≤ h) (q : ι ⊕ (σ × τ) → K) (z : K) :
    clockMass (terminalMatrix A D η lam) (terminalWeight (ι := ι) w)
        (mat (terminalMatrix A D η lam) q) z =
      ∑ x, if c x = z then
        β x * row (D x) (q ∘ Sum.inl) + a x * row η (q ∘ Sum.inl) else 0 := by
  classical
  let M := terminalMatrix A D η lam
  unfold clockMass
  change (∑ i, if nodes M i = z then terminalWeight w i * mat M q i else 0) = _
  rw [Fintype.sum_sum_type]
  have zero : (∑ i : ι, if nodes M (Sum.inl i) = z then
      terminalWeight w (Sum.inl i) * mat M q (Sum.inl i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [terminalWeight]
  rw [zero, zero_add, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases eq : c x = z
  · simpa [M, terminalWeight, nodes_terminal_inr law quiet p1 h1 lam, eq] using
      terminal_outgoingMass A D η copy p1 q x
  · simp [M, nodes_terminal_inr law quiet p1 h1 lam, eq]

end RKResearch.Certified.Graded.TerminalDeformation
