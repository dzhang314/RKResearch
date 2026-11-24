module

public import RKCert.TreeMoments
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.Paired.SDIRK
open RKCert.Paired
variable {K : Type*} [Field K] {s : ℕ}

def lower (A : Fin s → Fin s → K) : Prop :=
  ∀ i j, i < j → A i j = 0

/-- The actual price-two Volterra commutator on ordinary stage columns. -/
def R (A : Fin s → Fin s → K) : Vec K s →ₗ[K] Vec K s :=
  (diag (nodes A)).comp (mat A) - (mat A).comp (diag (nodes A)) - (mat A).comp (mat A)

private theorem lower_lead {A : Fin s → Fin s → K} (ha : lower A) (i : Fin s) (v : Vec K s)
    (hv : ∀ j, j < i → v j = 0) : mat A v i = A i i * v i := by
  rw [mat_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_cases hj : j < i
    · rw [hv j hj, mul_zero]
    · rw [ha i j (lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hji)), zero_mul]
  · simp

theorem commutator_lead {A : Fin s → Fin s → K} (ha : lower A) (i : Fin s) (v : Vec K s)
    (hv : ∀ j, j < i → v j = 0) : R A v i = -(A i i)^2 * v i := by
  have hd (j) (hj : j < i) : diag (nodes A) v j = 0 := by simp [hv j hj]
  have hm (j) (hj : j < i) : mat A v j = 0 := by
    rw [lower_lead ha j v (fun k hk => hv k (lt_trans hk hj)), hv j hj, mul_zero]
  change nodes A i * mat A v i - mat A (diag (nodes A) v) i - mat A (mat A v) i = _
  rw [lower_lead ha i _ hd, lower_lead ha i _ hm, lower_lead ha i v hv, diag_apply]
  ring

/-- No common diagonal is required. -/
theorem commutator_injective {A : Fin s → Fin s → K} (ha : lower A) (hn : ∀ i, A i i ≠ 0) :
    Function.Injective (R A) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  ext i
  have hi : ∀ n : ℕ, ∀ j : Fin s, j.val = n → x j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hj
      have he := congrFun hx j
      rw [commutator_lead ha j _ (fun k hk => ih k.val (by change k.val < j.val at hk; omega) k rfl)] at he
      simpa [(hn j)] using he
  exact hi i.val i rfl

theorem commutator_mem {A : Fin s → Fin s → K} {j : ℕ} {x : Vec K s} (hx : x ∈ treeSpace A j) :
    R A x ∈ treeSpace A (j+2) :=
  (treeSpace A (j+2)).sub_mem ((treeSpace A (j+2)).sub_mem
    (diag_treeSpace A (j+1) (mat_treeSpace A j hx))
    (mat_treeSpace A (j+1) (diag_treeSpace A j hx)))
    (mat_treeSpace A (j+1) (mat_treeSpace A j hx))

private theorem mat_tree (A : Fin s → Fin s → K) (t : Tree) :
    mat A (stageWeight A t) = stageWeight A (.attach t .leaf) := by
  ext i; simp [stageWeight]
private theorem clock_tree (A : Fin s → Fin s → K) (t : Tree) :
    diag (nodes A) (stageWeight A t) = stageWeight A (.attach .leaf t) := by
  ext i; simp [stageWeight, nodes]

theorem probe_commutator_tree {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (k : ℕ) (h : k+t.order+2 ≤ p) :
    probe A b k (R A (stageWeight A t)) = 0 := by
  let t₁ := Tree.attach .leaf (.attach t .leaf)
  let t₂ := Tree.attach (.attach .leaf t) .leaf
  let t₃ := Tree.attach (.attach t .leaf) .leaf
  have hp₁ : k+t₁.order ≤ p := by dsimp [t₁,Tree.order]; omega
  have hp₂ : k+t₂.order ≤ p := by dsimp [t₂,Tree.order]; omega
  have hp₃ : k+t₃.order ≤ p := by dsimp [t₃,Tree.order]; omega
  have h₁ := probe_normTree ho t₁ k hp₁
  have h₂ := probe_normTree ho t₂ k hp₂
  have h₃ := probe_normTree ho t₃ k hp₃
  simp only [normTree, map_smul, smul_eq_mul, t₁, t₂, t₃, Tree.order, Tree.childDensityProduct,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, one_mul, mul_one] at h₁ h₂ h₃
  let n := (t.order : K); let v := (t.childDensityProduct : K)
  let W := ((k:K)+n+2) * ((n+1)*(n*v))
  have nz : W ≠ 0 := by
    intro hz
    have : W * probe A b k (stageWeight A t₃) = 1 := by
      convert h₃ using 1; dsimp [W,n,v,t₃]; ring
    rw [hz, zero_mul] at this; exact zero_ne_one this
  apply (mul_eq_zero.mp (show W * probe A b k (R A (stageWeight A t)) = 0 from ?_)).resolve_left nz
  change W * probe A b k
    (diag (nodes A) (mat A (stageWeight A t)) - mat A (diag (nodes A) (stageWeight A t)) -
     mat A (mat A (stageWeight A t))) = 0
  simp only [mat_tree, clock_tree, map_sub]
  dsimp [W,n,v]
  linear_combination ((t.order:K)+1) * h₁ - (t.order:K) * h₂ - h₃

theorem probe_commutator {A : Fin s → Fin s → K} {b : Vec K s} {p j k : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hk : k+j+3 ≤ p) {x} (hx : x ∈ treeSpace A j) :
    probe A b k (R A x) = 0 := by
  have hle : treeSpace A j ≤ LinearMap.ker ((probe A b k).comp (R A)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    exact probe_commutator_tree ho t k (by omega)
  exact hle hx

end RKCert.Paired.SDIRK

