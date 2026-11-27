module

public import RKCert.ReviewedNative.RootedTreeGram
public import RKCert.ReviewedNative.TwoDonorDense

@[expose] public section

/-! Recover pointwise local purity from an already certified covariance trace. -/

namespace RKResearch.Certified.RootedTreeGram

open FiniteRootedTree TwoDonorDense
open scoped Matrix

private theorem every_sq_eq_zero {α : Type*} (l : List α) (f : α → ℤ)
    (h : (l.map fun x => (f x)^2).sum = 0) :
    ∀ x ∈ l, f x = 0 := by
  induction l with
  | nil => simp
  | cons y l ih =>
    intro x hx
    have hsum : 0 ≤ (l.map fun x => (f x)^2).sum := by
      apply List.sum_nonneg
      intro a ha
      obtain ⟨z,-,rfl⟩ := List.mem_map.mp ha
      exact sq_nonneg _
    have hsq := sq_nonneg (f y)
    simp only [List.map_cons, List.sum_cons] at h
    rcases List.mem_cons.mp hx with hxy | hx
    · rw [hxy]
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp (by omega)
    · exact ih (by omega) x hx

/-- A localized readout forces the numerator monomial at row `i`
for an arbitrary rational target clock `a/k`. -/
def localForm {s : ℕ} (i : Fin s) (a k : ℤ) (g : ℕ) : Fin (s+1) → ℤ :=
  Fin.snoc (Pi.single i (k^g)) (-(a^g))

theorem FactoredTrace.localNumerator {s p : ℕ}
    {M : Matrix (Fin s) (Fin s) ℤ} {d : ℤ} (F : FactoredTrace M d p)
    (i : Fin s) (a k : ℤ) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ p)
    (h : energy (F.cov ((t.order : ℕ)-1)) (localForm i a k ((t.order : ℕ)-1)) = 0) :
    k^((t.order : ℕ)-1) * normalized M t i = a^((t.order : ℕ)-1) * d^((t.order : ℕ)-1) := by
  let g := ((t.order : ℕ)-1)
  let v := localForm i a k g
  have hpos := t.order.pos
  have hgrade : g < p := by dsimp [g]; omega
  have hmem : t ∈ treesOfOrderSucc g := (mem_treesOfOrderSucc g t).mpr (by dsimp [g]; omega)
  have hz : energy (F.toTrace.cov g) v = 0 := by
    change energy (F.covScale g • F.cov g) v = 0
    unfold energy
    rw [Matrix.smul_mulVec, dotProduct_smul]
    change F.covScale g * energy (F.cov g) v = 0
    rw [h, mul_zero]
  rw [F.toTrace.correct g hgrade, covTrees, energy_covList] at hz
  have hh := every_sq_eq_zero _ _ hz t hmem
  simp only [v, localForm, feature, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, neg_mul, ← sub_eq_add_neg] at hh
  change (Pi.single i (k^g) ⬝ᵥ normalized M t) - a^g*d^g = 0 at hh
  rw [single_dotProduct] at hh
  exact sub_eq_zero.mp hh

/-- The same checked covariance yields an actual physical pure stage,
without re-running any construction or any normalized tree recursion. -/
theorem FactoredTrace.pureAt_of_local {s p q : ℕ}
    {M : Matrix (Fin s) (Fin s) ℤ} {d : ℤ} (F : FactoredTrace M d p)
    {A : Matrix (Fin s) (Fin s) ℚ}
    (hA : M.map (Int.castRingHom ℚ) = (d : ℚ) • A) (hd : (d : ℚ) ≠ 0)
    (i : Fin s) (a k : ℤ) (hk : (k : ℚ) ≠ 0)
    (hc : clocks A i = (a : ℚ)/(k : ℚ)) (hqp : q ≤ p)
    (h : ∀ g < q, energy (F.cov g) (localForm i a k g) = 0) :
    PureAt A i q := by
  intro t ht
  have hpos := t.order.pos
  let g := ((t.order : ℕ)-1)
  have hg : g < q := by dsimp [g]; omega
  have hn := F.localNumerator i a k t (le_trans ht hqp) (h _ hg)
  have hp := congrFun (map_Φ (Int.castRingHom ℚ) t M) i
  rw [hA, Φ_matrix_smul] at hp
  change ((Φ t M i : ℤ) : ℚ) = (d : ℚ)^g * Φ t A i at hp
  have hnQ := congrArg (fun z : ℤ => (z : ℚ)) hn
  simp only [Int.cast_mul, Int.cast_pow, normalized, Pi.smul_apply, smul_eq_mul,
    Int.cast_natCast, hp] at hnQ
  rw [hc, div_pow, eq_div_iff (pow_ne_zero g hk)]
  have hnew : (k : ℚ)^g * ((t.forestFactorial : ℚ) * ((d : ℚ)^g * Φ t A i)) =
      (a : ℚ)^g * (d : ℚ)^g := hnQ
  apply mul_right_cancel₀ (pow_ne_zero g hd)
  rw [← hnew]
  simp only [normalized, Pi.smul_apply, smul_eq_mul]
  change ((t.forestFactorial : ℚ) * Φ t A i) * (k : ℚ)^g * (d : ℚ)^g =
    (k : ℚ)^g * ((t.forestFactorial : ℚ) * ((d : ℚ)^g * Φ t A i))
  ring

#print axioms FactoredTrace.pureAt_of_local
end RKResearch.Certified.RootedTreeGram
