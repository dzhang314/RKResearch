module

public import RKCert.ReviewedNative.NativeIntegerSpanClearing
public import RKCert.ReviewedNative.RootedTreeAugmentedSpan

@[expose] public section

/-! Exact Boolean checks on integer coordinates. Candidate generation,
rational Gaussian elimination and any concrete tableau are absent. -/
namespace RKResearch.Certified.NativeIntegerAugmentedChecker

open RKResearch RKResearch.FiniteRootedTree
open NativeIntegerSpanClearing RootedTreeAugmentedSpan
open scoped Matrix

/-- Typed rows, actions and proof receipts. A bounded checker enumerates
all live grades and all actual ordered products, not a supplied key list. -/
structure Candidate (s : ℕ) where
  rank : ℕ → ℕ
  rows : (n : ℕ) → Fin (rank n) → ZFeature s
  leaf : Clearing (rank 1)
  actions : (l : ℕ) → Fin (rank l) → ZVec s
  products : (k l : ℕ) → Fin (rank k) → Fin (rank l) → Clearing (rank (k+l))

def checkDegrees (p : ℕ) (f : ℕ → Bool) : Bool :=
  (List.range p).all (fun n => f (n+1))

theorem checkDegrees_get {p n : ℕ} {f : ℕ → Bool}
    (h : checkDegrees p f = true) (hn : 0 < n) (hp : n ≤ p) :
    f n = true := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change (List.range p).all (fun m => f (m+1)) = true at h
  exact List.all_eq_true.mp h m (List.mem_range.mpr (Nat.lt_of_succ_le hp))

def checkScales (d e : ℤ) : Bool :=
  decide (d ≠ 0) && decide (e ≠ 0)

theorem checkScales_sound {d e : ℤ} (h : checkScales d e = true) :
    d ≠ 0 ∧ e ≠ 0 := by
  change (decide (d ≠ 0) && decide (e ≠ 0)) = true at h
  obtain ⟨hd, he⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hd, of_decide_eq_true he⟩

def leafZ (s : ℕ) : ZFeature s :=
  (fun _ => 1, 1)

def checkLeaf {s : ℕ} (C : Candidate s) : Bool :=
  checkClearing (C.rows 1) (leafZ s) C.leaf

def childInput {s : ℕ} (C : Candidate s) (l : ℕ) (j : Fin (C.rank l)) : ZVec s :=
  fun i => (l : ℤ) * (C.rows l j).1 i

def checkAction {s : ℕ} (act : ZVec s → ZVec s) (C : Candidate s)
    (l : ℕ) (j : Fin (C.rank l)) : Bool :=
  checkVec (C.actions l j) (act (childInput C l j))

def checkActions {s : ℕ} (act : ZVec s → ZVec s) (p : ℕ) (C : Candidate s) : Bool :=
  checkDegrees (p-1) fun l => checkIndices (checkAction act C l)

def joinedZ {s : ℕ} (d : ℤ) (C : Candidate s) (k l : ℕ)
    (i : Fin (C.rank k)) (j : Fin (C.rank l)) : ZFeature s :=
  (fun a => (C.rows k i).1 a * C.actions l j a, (d * (C.rows k i).2) * (C.rows l j).2)

def checkProduct {s : ℕ} (d : ℤ) (C : Candidate s) (k l : ℕ)
    (i : Fin (C.rank k)) (j : Fin (C.rank l)) : Bool :=
  checkClearing (C.rows (k+l)) (joinedZ d C k l i j) (C.products k l i j)

def checkProducts {s : ℕ} (d : ℤ) (p : ℕ) (C : Candidate s) : Bool :=
  checkDegrees p fun k =>
    checkDegrees (p-k) fun l =>
      checkIndices fun i => checkIndices (checkProduct d C k l i)

def checkPayment {s : ℕ} (out : ZVec s → ℤ) (e : ℤ) (n : ℕ)
    (x : ZFeature s) : Bool :=
  decide ((n : ℤ) * out x.1 = e*x.2)

def checkPayments {s : ℕ} (out : ZVec s → ℤ) (e : ℤ) (p : ℕ)
    (C : Candidate s) : Bool :=
  checkDegrees p fun n => checkIndices (fun i => checkPayment out e n (C.rows n i))

def check {s : ℕ} (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (d e : ℤ) (p : ℕ) (C : Candidate s) : Bool :=
  checkScales d e &&
    (checkLeaf C &&
     (checkActions act p C &&
      (checkProducts d p C && checkPayments out e p C)))

/-- Proof-only join seam for independently checked chunks/parts.
Do not require one monolithic reduction of the final check. -/
theorem check_iff {s : ℕ} (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (d e : ℤ) (p : ℕ) (C : Candidate s) :
    check act out d e p C = true ↔
      checkScales d e = true ∧ checkLeaf C = true ∧ checkActions act p C = true ∧
      checkProducts d p C = true ∧ checkPayments out e p C = true := by
  simp only [check, Bool.and_eq_true_iff]

def ratMatrix {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) : Matrix (Fin s) (Fin s) ℚ :=
  A.map (Int.castRingHom ℚ)

def generators {s : ℕ} (C : Candidate s) (n : ℕ) : Set (QFeature s) :=
  Set.range (fun i => ratFeature (C.rows n i))

theorem checkLeaf_sound {s : ℕ} {C : Candidate s} (h : checkLeaf C = true) :
    ((1 : Fin s → ℚ), (1 : ℚ)) ∈ Submodule.span ℚ (generators C 1) := by
  change checkClearing (C.rows 1) (leafZ s) C.leaf = true at h
  have hs := checkClearing_sound h
  have eq : ratFeature (leafZ s) = ((1 : Fin s → ℚ), (1 : ℚ)) := by
    apply Prod.ext
    · funext i
      change ((1 : ℤ) : ℚ) = 1
      exact Int.cast_one
    · change ((1 : ℤ) : ℚ) = 1
      exact Int.cast_one
  rw [eq] at hs
  exact hs

theorem checkActions_get {s p : ℕ} {act : ZVec s → ZVec s} {C : Candidate s}
    (h : checkActions act p C = true) {l : ℕ} (hl : 0 < l) (hp : l < p)
    (j : Fin (C.rank l)) : checkAction act C l j = true := by
  change checkDegrees (p-1) (fun l => checkIndices (checkAction act C l)) = true at h
  have bound : l ≤ p-1 := by omega
  exact checkIndices_get (checkDegrees_get h hl bound) j

theorem checkProducts_get {s p : ℕ} {d : ℤ} {C : Candidate s}
    (h : checkProducts d p C = true) {k l : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hp : k+l ≤ p)
    (i : Fin (C.rank k)) (j : Fin (C.rank l)) :
    checkProduct d C k l i j = true := by
  change checkDegrees p (fun k => checkDegrees (p-k) (fun l =>
    checkIndices (fun i => checkIndices (checkProduct d C k l i)))) = true at h
  have kb : k ≤ p := by omega
  have lb : l ≤ p-k := by omega
  have hk' := checkDegrees_get h hk kb
  have hl' := checkDegrees_get hk' hl lb
  exact checkIndices_get (checkIndices_get hl' i) j

theorem checkPayments_get {s p : ℕ} {out : ZVec s → ℤ} {e : ℤ} {C : Candidate s}
    (h : checkPayments out e p C = true) {n : ℕ}
    (hn : 0 < n) (hp : n ≤ p) (i : Fin (C.rank n)) :
    checkPayment out e n (C.rows n i) = true := by
  change checkDegrees p (fun n => checkIndices (fun i =>
    checkPayment out e n (C.rows n i))) = true at h
  exact checkIndices_get (checkDegrees_get h hn hp) i

private theorem rat_childInput {s : ℕ} (C : Candidate s) (l : ℕ) (j : Fin (C.rank l)) :
    ratVec (childInput C l j) = (l : ℚ) • ratVec (C.rows l j).1 := by
  funext a
  change (((l : ℤ) * (C.rows l j).1 a : ℤ) : ℚ) =
    (l : ℚ) * ((C.rows l j).1 a : ℚ)
  simp only [Int.cast_mul, Int.cast_natCast]

/-- Cast the actual cached action proof before relating the exact joined
integer row to the original bilinear map, including its homogeneous tail. -/
theorem joinedZ_sound {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ)
    (act : ZVec s → ZVec s) (hact : ∀ v, act v = A *ᵥ v)
    (d : ℤ) (C : Candidate s) (k l : ℕ) (i : Fin (C.rank k)) (j : Fin (C.rank l))
    (ha : checkAction act C l j = true) :
    ratFeature (joinedZ d C k l i j) =
      attachBilin (ratMatrix A) (d : ℚ) l (ratFeature (C.rows k i))
        (ratFeature (C.rows l j)) := by
  change checkVec (C.actions l j) (act (childInput C l j)) = true at ha
  have eqZ : C.actions l j = A *ᵥ childInput C l j :=
    (checkVec_sound ha).trans (hact _)
  have actionQ : ratVec (C.actions l j) =
      ratMatrix A *ᵥ ((l : ℚ) • ratVec (C.rows l j).1) := by
    rw [eqZ]
    have mapped : ratVec (A *ᵥ childInput C l j) =
        ratMatrix A *ᵥ ratVec (childInput C l j) := by
      funext a
      exact (Int.castRingHom ℚ).map_mulVec A (childInput C l j) a
    exact mapped.trans (congrArg (fun v => ratMatrix A *ᵥ v) (rat_childInput C l j))
  rw [attachBilin_apply]
  apply Prod.ext
  · funext a
    change ((((C.rows k i).1 a * C.actions l j a) : ℤ) : ℚ) =
      ((C.rows k i).1 a : ℚ) * (ratMatrix A *ᵥ ((l : ℚ) • ratVec (C.rows l j).1)) a
    rw [Int.cast_mul]
    exact congrArg (fun v : Fin s → ℚ => ((C.rows k i).1 a : ℚ) * v a) actionQ
  · change ((((d * (C.rows k i).2) * (C.rows l j).2) : ℤ) : ℚ) =
      ((d : ℚ) * ((C.rows k i).2 : ℚ)) * ((C.rows l j).2 : ℚ)
    simp only [Int.cast_mul]

theorem checkPayment_sound {s : ℕ} (b : ZVec s) (out : ZVec s → ℤ)
    (hout : ∀ v, out v = b ⬝ᵥ v) (e : ℤ) (n : ℕ) (x : ZFeature s)
    (h : checkPayment out e n x = true) :
    residual (ratVec b) (e : ℚ) n (ratFeature x) = 0 := by
  change decide ((n : ℤ) * out x.1 = e*x.2) = true at h
  have eqZ : (n : ℤ) * out x.1 = e*x.2 := of_decide_eq_true h
  rw [hout] at eqZ
  have eqQ := congrArg (Int.castRingHom ℚ) eqZ
  change (Int.castRingHom ℚ) ((n : ℤ)*(b ⬝ᵥ x.1)) =
    (Int.castRingHom ℚ) (e*x.2) at eqQ
  simp only [map_mul, RingHom.map_dotProduct] at eqQ
  change (((n : ℤ) : ℚ) * (ratVec b ⬝ᵥ ratVec x.1)) =
    (e : ℚ) * (x.2 : ℚ) at eqQ
  rw [Int.cast_natCast] at eqQ
  change (n : ℚ) * (ratVec b ⬝ᵥ ratVec x.1) - (e : ℚ)*(x.2 : ℚ) = 0
  exact sub_eq_zero.mpr eqQ

theorem checkProducts_sound {s p bound : ℕ} (A : Matrix (Fin s) (Fin s) ℤ)
    (act : ZVec s → ZVec s) (hact : ∀ v, act v = A *ᵥ v) (d : ℤ)
    (C : Candidate s) (hbound : p ≤ bound)
    (ha : checkActions act bound C = true) (hj : checkProducts d p C = true) :
    BasisCloses (ratMatrix A) (d : ℚ) p (generators C) := by
  intro k l hk hl hp x hx y hy
  change x ∈ Set.range (fun i => ratFeature (C.rows k i)) at hx
  change y ∈ Set.range (fun j => ratFeature (C.rows l j)) at hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hlt : l < bound := by omega
  have hr := checkActions_get ha hl hlt j
  have hc := checkProducts_get hj hk hl hp i j
  change checkClearing (C.rows (k+l)) (joinedZ d C k l i j) (C.products k l i j) =
    true at hc
  have hs := checkClearing_sound hc
  rw [joinedZ_sound A act hact d C k l i j hr] at hs
  exact hs

theorem checkPayments_sound {s p : ℕ} (b : ZVec s) (out : ZVec s → ℤ)
    (hout : ∀ v, out v = b ⬝ᵥ v) (e : ℤ) (C : Candidate s)
    (h : checkPayments out e p C = true) :
    ∀ n : ℕ, 0 < n → n ≤ p → ∀ x ∈ generators C n, residual (ratVec b) (e : ℚ) n x = 0 := by
  intro n hn hp x hx
  change x ∈ Set.range (fun j => ratFeature (C.rows n j)) at hx
  obtain ⟨i, rfl⟩ := hx
  exact checkPayment_sound b out hout e n _ (checkPayments_get h hn hp i)

theorem original_order_from_rational_scaled_moments {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℤ) (b : ZVec s) (d e : ℤ) (p : ℕ)
    {U : Matrix (Fin s) (Fin s) ℚ} {w : Fin s → ℚ}
    (hA : ratMatrix A = (d : ℚ) • U) (hb : ratVec b = (e : ℚ) • w)
    (hd : d ≠ 0) (he : e ≠ 0)
    (mom : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
      (t.factorial : ℚ) * (ratVec b ⬝ᵥ Φ t (ratMatrix A)) =
        (e : ℚ) * (d : ℚ)^((t.order : ℕ)-1)) : RKResearch.HasOrder p U w := by
  have h₁ : (ratMatrix A).map (RingHom.id ℚ) = (RingHom.id ℚ) (d : ℚ) • U := by
    funext i j
    change ratMatrix A i j = ((d : ℚ) • U) i j
    exact congrArg (fun M : Matrix (Fin s) (Fin s) ℚ => M i j) hA
  have h₂ : (RingHom.id ℚ) ∘ ratVec b = (RingHom.id ℚ) (e : ℚ) • w := by
    change ratVec b = (e : ℚ) • w
    exact hb
  have hdu : IsUnit (d : ℚ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hd)
  have heu : IsUnit (e : ℚ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr he)
  exact hasOrder_of_scaled_moments (RingHom.id ℚ) h₁ h₂ hdu heu mom

/-- The reviewed HasOrder at the same explicitly normalized tableau.
The supplied efficient actions/output are checked semantic substitutions. -/
theorem hasOrder_of_check {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) (b : ZVec s)
    (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (hact : ∀ v, act v = A *ᵥ v) (hout : ∀ v, out v = b ⬝ᵥ v)
    (d e : ℤ) (p : ℕ) (C : Candidate s)
    {U : Matrix (Fin s) (Fin s) ℚ} {w : Fin s → ℚ}
    (hA : ratMatrix A = (d : ℚ) • U) (hb : ratVec b = (e : ℚ) • w)
    (h : check act out d e p C = true) : RKResearch.HasOrder p U w := by
  obtain ⟨hSc, hL, ha, hj, hp⟩ := (check_iff act out d e p C).mp h
  obtain ⟨hd, he⟩ := checkScales_sound hSc
  have moments := all_scaled_moments_of_basis_closure (ratMatrix A) (ratVec b)
    (d : ℚ) (e : ℚ) p (generators C) (checkLeaf_sound hL)
    (checkProducts_sound A act hact d C le_rfl ha hj)
    (checkPayments_sound b out hout e C hp)
  exact original_order_from_rational_scaled_moments A b d e p hA hb hd he moments

def normalizedA {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) (d : ℤ) :
    Matrix (Fin s) (Fin s) ℚ :=
  Matrix.of fun i j => (A i j : ℚ) / (d : ℚ)

def normalizedb {s : ℕ} (b : ZVec s) (e : ℤ) : Fin s → ℚ :=
  fun i => (b i : ℚ) / (e : ℚ)

/-- Self-contained dense reference entry. It has no action or scale
assumptions supplied by a generator; the checked integer data suffice. -/
theorem hasOrder_of_dense_check {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) (b : ZVec s)
    (d e : ℤ) (p : ℕ) (C : Candidate s)
    (h : check (fun v => A *ᵥ v) (fun v => b ⬝ᵥ v) d e p C = true) :
    RKResearch.HasOrder p (normalizedA A d) (normalizedb b e) := by
  have sc := ((check_iff _ _ d e p C).mp h).1
  obtain ⟨hd, he⟩ := checkScales_sound sc
  have hA : ratMatrix A = (d : ℚ) • normalizedA A d := by
    funext i j
    change (A i j : ℚ) = (d : ℚ) * ((A i j : ℚ)/(d : ℚ))
    exact (mul_div_cancel₀ (A i j : ℚ) (Int.cast_ne_zero.mpr hd)).symm
  have hb : ratVec b = (e : ℚ) • normalizedb b e := by
    funext i
    change (b i : ℚ) = (e : ℚ) * ((b i : ℚ)/(e : ℚ))
    exact (mul_div_cancel₀ (b i : ℚ) (Int.cast_ne_zero.mpr he)).symm
  exact hasOrder_of_check A b _ _ (fun _ => rfl) (fun _ => rfl) d e p C hA hb h

end RKResearch.Certified.NativeIntegerAugmentedChecker
