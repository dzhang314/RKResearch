module

public import RKCert.ReviewedNative.NativeTerminalTailMoments
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-! # The paid branch-moment width lower bound

A nodal square vanishes on the proposed replacement support regardless of
its signs. Positivity is required only on the original distinct responses.
-/
namespace RKResearch.Certified.TerminalSplit

open RKResearch FiniteRootedTree Polynomial
open scoped Matrix FiniteRootedTree BigOperators Polynomial

variable {K ι σ τ : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Fintype ι] [Fintype σ] [Fintype τ]

/-- Any finite cover of the nonzero replacement weights must contain enough
response sites. No assumption on the signs of the replacement weights. -/
theorem min_card_le_of_even_power_moments (x w : σ → K) (y v : τ → K)
    (S : Finset K) (cover : ∀ j, v j ≠ 0 → y j ∈ S)
    (positive : ∀ i, 0 < w i) (distinct : Function.Injective x) {d : ℕ}
    (mom : ∀ k ≤ 2*d, (∑ i : σ, w i * (x i)^k) = ∑ j : τ, v j * (y j)^k) :
    min (Fintype.card σ) (d+1) ≤ S.card := by
  classical
  by_contra h
  have hsmall : S.card < min (Fintype.card σ) (d+1) := Nat.lt_of_not_ge h
  have hcard : S.card < Fintype.card σ := hsmall.trans_le (min_le_left _ _)
  have hd : S.card ≤ d := Nat.le_of_lt_succ (hsmall.trans_le (min_le_right _ _))
  let U : Finset K := Finset.univ.image x
  have hU : U.card = Fintype.card σ := by
    simp only [U, Finset.card_image_of_injective _ distinct, Finset.card_univ]
  obtain ⟨z,hz,hzout⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show S.card < U.card by simpa only [hU] using hcard)
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (show z ∈ Finset.univ.image x from hz)
  have hxi : x i ∉ S := by simpa only [hi] using hzout
  let P : K[X] := Lagrange.nodal S id
  have hP : P.natDegree ≤ d := by
    simpa only [P, Lagrange.natDegree_nodal] using hd
  have hPe : P.eval (x i) ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro a ha he
    change x i = a at he
    exact hxi (he.symm ▸ ha)
  have e := sum_weighted_eval_eq_of_power_moments x w y v mom (P^2)
    (natDegree_pow_le_of_le 2 hP)
  simp only [eval_pow] at e
  have hy : (∑ j : τ, v j * (P.eval (y j))^2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hV : v j = 0
    · rw [hV, zero_mul]
    · have hzero : P.eval (y j) = 0 := Lagrange.eval_nodal_at_node (v := id) (cover j hV)
      simp [hzero]
  have hx : 0 < (∑ j : σ, w j * (P.eval (x j))^2) := Finset.sum_pos'
    (fun j _ => mul_nonneg (positive j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos (positive i) (sq_pos_of_ne_zero hPe)⟩
  exact hx.ne' (e.trans hy)

/-- The physical replacement may have an arbitrary internal matrix, arbitrary
self-diagonals, and signed output. Only its old prefix is frozen. -/
theorem min_card_le_terminalTail_of_hasOrder
    (A : Matrix ι ι K) (b : ι → K) (C₀ : Matrix σ ι K) (D₀ : Matrix σ σ K) (w : σ → K)
    (C₁ : Matrix τ ι K) (D₁ : Matrix τ τ K) (v : τ → K) {p : ℕ}
    (h₀ : HasOrder p (terminalTailMatrix A C₀ D₀) (Sum.elim b w))
    (h₁ : HasOrder p (terminalTailMatrix A C₁ D₁) (Sum.elim b v))
    (u : FiniteRootedTree) (positive : ∀ i, 0 < w i)
    (distinct : Function.Injective (tailBranchResponse A C₀ D₀ u))
    (d : ℕ) (pay : 1+(2*d)*(u.order : ℕ) ≤ p) :
    min (Fintype.card σ) (d+1) ≤ Fintype.card τ := by
  classical
  let x := tailBranchResponse A C₀ D₀ u
  let y := tailBranchResponse A C₁ D₁ u
  let S : Finset K := (Finset.univ : Finset τ).image y
  have cover (j : τ) (_ : v j ≠ 0) : y j ∈ S :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have mom (k : ℕ) (hk : k ≤ 2*d) :
      (∑ i : σ, w i * (x i)^k) = ∑ j : τ, v j * (y j)^k :=
    tailBranchResponse_moment_eq_of_hasOrder A b C₀ D₀ w C₁ D₁ v h₀ h₁ u k
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) 1).trans pay)
  exact (min_card_le_of_even_power_moments x w y v S cover positive distinct mom).trans
    (show S.card ≤ Fintype.card τ by
      simpa only [S, Finset.card_univ] using
        (Finset.card_image_le (s := (Finset.univ : Finset τ)) (f := y)))

/-- Singleton positive rigidity needs no early probe agreement and no
assumption on the replacement's internal matrix. -/
theorem tailBranchResponse_eq_singleton_of_hasOrder
    (A : Matrix ι ι K) (b : ι → K) (C₀ : Matrix Unit ι K) (D₀ : Matrix Unit Unit K) (β : K)
    (C₁ : Matrix τ ι K) (D₁ : Matrix τ τ K) (v : τ → K) {p : ℕ}
    (h₀ : HasOrder p (terminalTailMatrix A C₀ D₀) (Sum.elim b (fun _ => β)))
    (h₁ : HasOrder p (terminalTailMatrix A C₁ D₁) (Sum.elim b v))
    (u : FiniteRootedTree) (positive : ∀ j, 0 ≤ v j)
    (pay : 1+2*(u.order : ℕ) ≤ p) (i : τ) (live : 0 < v i) :
    tailBranchResponse A C₁ D₁ u i = tailBranchResponse A C₀ D₀ u () := by
  let y := tailBranchResponse A C₁ D₁ u
  let x := tailBranchResponse A C₀ D₀ u
  let P : K[X] := X - C (x ())
  have hP : P.natDegree ≤ 1 := natDegree_X_sub_C_le _
  have mom (k : ℕ) (hk : k ≤ 2) :
      (∑ j : τ, v j * (y j)^k) = ∑ j : Unit, β * (x j)^k :=
    tailBranchResponse_moment_eq_of_hasOrder A b C₁ D₁ v C₀ D₀ (fun _ => β) h₁ h₀ u k
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) 1).trans pay)
  have hQ : (P^2).natDegree ≤ 2 := by
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le 2 hP
  have h := sum_weighted_eval_eq_of_power_moments y v x (fun _ : Unit => β) mom (P^2) hQ
  have hx : P.eval (x ()) = 0 := by simp [P]
  have hz : (∑ j : τ, v j * (P.eval (y j))^2) = 0 := by
    simpa [eval_pow, Fintype.sum_unique, hx] using h
  change y i = x ()
  by_contra hne
  have hPy : P.eval (y i) ≠ 0 := by
    simpa [P, sub_ne_zero] using hne
  have hp : 0 < (∑ j : τ, v j * (P.eval (y j))^2) := Finset.sum_pos'
    (fun j _ => mul_nonneg (positive j) (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos live (sq_pos_of_ne_zero hPy)⟩
  exact hp.ne' hz

end RKResearch.Certified.TerminalSplit
