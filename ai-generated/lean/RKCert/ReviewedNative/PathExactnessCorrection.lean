module
public import RKResearch.OrderConditions

@[expose] public section

/-! # Additive next-tall correction on the reviewed trees -/
namespace RKResearch.Certified.PathExactness

open FiniteRootedTree
open scoped Matrix FiniteRootedTree

section Path
variable {R : Type*} [CommSemiring R]

/-- A common diagonal with one unit backward step, on the original path coordinates. -/
def adjacentPath (γ : R) (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i => Fin.cases (Pi.single 0 γ)
    (fun j : Fin n => Pi.single j.succ γ + Pi.single j.castSucc 1) i

theorem adjacentPath_first (γ : R) (n : ℕ) :
    adjacentPath γ n 0 = Pi.single (0 : Fin (n+1)) γ := rfl

theorem adjacentPath_diag (γ : R) (n : ℕ) (i : Fin (n+1)) :
    adjacentPath γ n i i = γ := by
  cases i using Fin.cases with
  | zero =>
    change (Pi.single (0 : Fin (n+1)) γ : Fin (n+1) → R) 0 = γ
    simp
  | succ j =>
    have ne : j.succ ≠ j.castSucc := by
      intro eq
      have e := congrArg Fin.val eq
      simp only [Fin.val_succ, Fin.val_castSucc] at e
      omega
    change ((Pi.single j.succ γ : Fin (n+1) → R) + (Pi.single j.castSucc 1 : Fin (n+1) → R)) j.succ = γ
    simp [Pi.single_apply, ne, Ne.symm ne]

theorem adjacentPath_above (γ : R) (n : ℕ) {i j : Fin (n+1)} (h : i < j) :
    adjacentPath γ n i j = 0 := by
  cases i using Fin.cases with
  | zero =>
    have ne : j ≠ (0 : Fin (n+1)) := ne_of_gt h
    change (Pi.single (0 : Fin (n+1)) γ : Fin (n+1) → R) j = 0
    simp [Pi.single_apply, ne, Ne.symm ne]
  | succ i =>
    have ne₁ : j ≠ i.succ := ne_of_gt h
    have ne₂ : j ≠ i.castSucc := by
      intro eq
      have lv : i.succ.val < j.val := h
      simp only [eq, Fin.val_succ, Fin.val_castSucc] at lv
      omega
    change ((Pi.single i.succ γ : Fin (n+1) → R) + (Pi.single i.castSucc 1 : Fin (n+1) → R)) j = 0
    simp [Pi.single_apply, ne₁, Ne.symm ne₁, ne₂, Ne.symm ne₂]

private theorem path_mulVec_zero (γ : R) (n : ℕ) (v : Fin (n+1) → R) :
    (adjacentPath γ n *ᵥ v) 0 = γ * v 0 := by
  change Pi.single (0 : Fin (n+1)) γ ⬝ᵥ v = _
  simp only [single_dotProduct]

private theorem path_mulVec_succ (γ : R) (n : ℕ) (v : Fin (n+1) → R) (i : Fin n) :
    (adjacentPath γ n *ᵥ v) i.succ = γ * v i.succ + v i.castSucc := by
  change (Pi.single i.succ γ + Pi.single i.castSucc (1 : R)) ⬝ᵥ v = _
  simp only [add_dotProduct, single_dotProduct, one_mul]

/-- Past the largest possible depth, the zero-endpoint truncation disappears. -/
theorem phi_adjacentPath_stable (γ : R) (n : ℕ) (t : FiniteRootedTree)
    (i : Fin (n+1)) (bound : (t.order : ℕ)-1 ≤ i.val) :
    Φ t (adjacentPath γ n) i = (γ+1)^((t.order : ℕ)-1) := by
  induction t generalizing i with
  | leaf => simp [Φ, order]
  | butcherProduct t u ihT ihU =>
    have tpos := t.order.pos
    have upos := u.order.pos
    have total : (t.order : ℕ) + (u.order : ℕ) - 1 ≤ i.val := by
      simpa only [order, PNat.add_coe] using bound
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero] at total
      omega
    | succ j =>
      have hT : (t.order : ℕ)-1 ≤ j.succ.val := by omega
      have hU : (u.order : ℕ)-1 ≤ j.succ.val := by omega
      have hPrev : (u.order : ℕ)-1 ≤ j.castSucc.val := by
        simp only [Fin.val_succ] at total
        simp only [Fin.val_castSucc]
        omega
      simp only [Φ, Pi.mul_apply, path_mulVec_succ, ihT j.succ hT,
        ihU j.succ hU, ihU j.castSucc hPrev]
      calc
        _ = (γ+1)^((t.order : ℕ)-1) * ((γ+1) * (γ+1)^((u.order : ℕ)-1)) := by
          rw [add_mul, one_mul]
        _ = (γ+1)^(((t.order : ℕ)-1) + (((u.order : ℕ)-1)+1)) := by
          rw [pow_add, pow_succ']
        _ = _ := by
          have exp : ((t.order : ℕ)-1) + (((u.order : ℕ)-1)+1) =
              (((t ◂ u).order : ℕ)-1) := by
            simp only [order, PNat.add_coe]
            omega
          rw [exp]

private theorem adjacentPower_stable (γ : R) (n r : ℕ) (i : Fin (n+1))
    (bound : r ≤ i.val) :
    ((adjacentPath γ n)^r *ᵥ (1 : Fin (n+1) → R)) i = (γ+1)^r := by
  have htree : (((tallTree r.succPNat).order : ℕ)-1) ≤ i.val := by
    simpa only [order_tallTree, Nat.succPNat_coe, Nat.succ_sub_one] using bound
  simpa only [Φ_tallTree, order_tallTree, Nat.succPNat_coe, Nat.succ_sub_one] using
    phi_adjacentPath_stable γ n (tallTree r.succPNat) i htree

/-- At the first admissible coordinate only the all-step term is new. -/
private theorem adjacentPower_boundary (γ : R) (n r : ℕ)
    (i : Fin n) (pos : i.val = r) :
    ((adjacentPath γ n)^(r+1) *ᵥ (1 : Fin (n+1) → R)) i.succ =
      ((adjacentPath γ n)^(r+1) *ᵥ (1 : Fin (n+1) → R)) i.castSucc + 1 := by
  induction r generalizing i with
  | zero =>
    have hi : i.castSucc = (0 : Fin (n+1)) := by
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_zero] using pos
    simp only [Nat.zero_add, pow_one, path_mulVec_succ, hi, path_mulVec_zero, Pi.one_apply, mul_one]
  | succ r ih =>
    let j : Fin n := ⟨r, by have hn := i.isLt; omega⟩
    have mid : i.castSucc = j.succ := by
      apply Fin.ext
      change i.val = r+1
      exact pos
    let v : Fin (n+1) → R := (adjacentPath γ n)^(r+1) *ᵥ 1
    have op : (adjacentPath γ n)^((r+1)+1) *ᵥ (1 : Fin (n+1) → R) =
        adjacentPath γ n *ᵥ v := by
      change (adjacentPath γ n)^((r+1)+1) *ᵥ (1 : Fin (n+1) → R) =
        adjacentPath γ n *ᵥ ((adjacentPath γ n)^(r+1) *ᵥ (1 : Fin (n+1) → R))
      rw [pow_succ', Matrix.mulVec_mulVec]
    have same : v i.succ = v i.castSucc := by
      have h₁ : r+1 ≤ i.succ.val := by
        simp only [Fin.val_succ]
        omega
      have h₂ : r+1 ≤ i.castSucc.val := by
        simp only [Fin.val_castSucc]
        omega
      exact (adjacentPower_stable γ n (r+1) i.succ h₁).trans
        (adjacentPower_stable γ n (r+1) i.castSucc h₂).symm
    have boundary : v i.castSucc = v j.castSucc + 1 := by
      rw [mid]
      exact ih j rfl
    change ((adjacentPath γ n)^((r+1)+1) *ᵥ (1 : Fin (n+1) → R)) i.succ =
      ((adjacentPath γ n)^((r+1)+1) *ᵥ (1 : Fin (n+1) → R)) i.castSucc + 1
    rw [op]
    calc
      _ = γ * v i.succ + v i.castSucc := path_mulVec_succ γ n v i
      _ = γ * v i.castSucc + (v j.castSucc + 1) :=
        congrArg₂ (fun x y : R => γ*x+y) same boundary
      _ = (γ * v i.castSucc + v j.castSucc) + 1 := (add_assoc _ _ _).symm
      _ = _ := by rw [mid, path_mulVec_succ]

end Path

section Correction
variable {R : Type*} [CommRing R]

/-- The two-coordinate row for preserving orders through n+1. The path has n+2 stages. -/
def pathCorrection (n : ℕ) : Fin (n+2) → R :=
  Pi.single (Fin.last n).succ 1 - Pi.single (Fin.last n).castSucc 1

theorem pathCorrection_pair (n : ℕ) (v : Fin (n+2) → R) :
    pathCorrection n ⬝ᵥ v = v (Fin.last n).succ - v (Fin.last n).castSucc := by
  simp only [pathCorrection, sub_dotProduct, single_dotProduct, one_mul]

theorem pathCorrection_paid (γ : R) (n : ℕ) (t : FiniteRootedTree)
    (pay : (t.order : ℕ) ≤ n+1) :
    pathCorrection n ⬝ᵥ Φ t (adjacentPath γ (n+1)) = 0 := by
  have top : (t.order : ℕ)-1 ≤ (Fin.last n).succ.val := by
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have below : (t.order : ℕ)-1 ≤ (Fin.last n).castSucc.val := by
    simp only [Fin.val_castSucc, Fin.val_last]
    omega
  rw [pathCorrection_pair, phi_adjacentPath_stable γ _ t _ top,
    phi_adjacentPath_stable γ _ t _ below, sub_self]

theorem pathCorrection_next_tall (γ : R) (n : ℕ) :
    pathCorrection n ⬝ᵥ Φ (tallTree (n+1).succPNat) (adjacentPath γ (n+1)) = 1 := by
  rw [pathCorrection_pair, Φ_tallTree]
  simp only [Nat.succPNat_coe, Nat.succ_sub_one]
  rw [adjacentPower_boundary γ (n+1) n (Fin.last n) rfl]
  simp

variable {ι : Type*} [Fintype ι]

/-- An additive correction of the output row only. The direction can be the
physical path row after an existing stage extension. -/
def nextTallCorrectedWeights (n : ℕ) (A : Matrix ι ι R) (b d : ι → R) : ι → R :=
  b - (b ⬝ᵥ Φ (tallTree (n+1).succPNat) A) • d

/-- The two raw read properties certify literal exact order with no
inverse of the next tall factorial. Neither the stage matrix nor clocks change. -/
theorem exact_order_of_next_tall_correction [Nontrivial R]
    {n : ℕ} {A : Matrix ι ι R} {b d : ι → R} (h : HasOrder (n+1) A b)
    (vanish : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ n+1 → d ⬝ᵥ Φ t A = 0)
    (one : d ⬝ᵥ Φ (tallTree (n+1).succPNat) A = 1) :
    HasOrder (n+1) A (nextTallCorrectedWeights n A b d) ∧
      ¬ HasOrder (n+2) A (nextTallCorrectedWeights n A b d) := by
  constructor
  · intro t pay
    simpa only [nextTallCorrectedWeights, sub_dotProduct, smul_dotProduct,
      vanish t pay, smul_zero, sub_zero] using h t pay
  · intro next
    let t := tallTree (n+1).succPNat
    have pay : (t.order : ℕ) ≤ n+2 := by
      simp [t, order_tallTree, Nat.succPNat_coe, Nat.succ_eq_add_one]
    have raw : nextTallCorrectedWeights n A b d ⬝ᵥ Φ t A = 0 := by
      simp only [t, nextTallCorrectedWeights, sub_dotProduct, smul_dotProduct,
        one, smul_eq_mul, mul_one, sub_self]
    have fail := next t pay
    rw [raw, mul_zero] at fail
    exact zero_ne_one fail

end Correction
end RKResearch.Certified.PathExactness
