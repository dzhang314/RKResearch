module

public import RKCert.ReviewedNative.DIRKOrderSix
public import RKCert.ReviewedNative.DIRKReverseGrowth

public section

/-! # Uniform lower bound for lower triangular Runge–Kutta tableaux

The full-rank argument uses only the reviewed tree spaces, their paid
annihilators and the actual physical first and last live coordinates. In
particular it does not replace the tableau by a trimmed one, or require
distinct nodes, nonzero diagonal entries, positive weights or characteristic
zero. The result gives the existing uniform DIRK lower bound directly for the
human tree-order predicate; it does not assert existence at the bound.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K]

/-- One physical zero row, not strict triangularity, suffices to distinguish
a live node at one from the entire paid midpoint space. -/
theorem endpoint_coordinate_out_of_zero_row {ι : Type*} [Fintype ι] {A : Matrix ι ι K}
    {b : ι → K} {p q : ℕ} (ho : HasOrder A b p) (pay : 2*q+1 ≤ p) {o t : ι}
    (hr : ∀ j, A o j = 0) (live : b t ≠ 0) (one : nodes A t = 1) :
    coordinate (K:=K) t ∉ treeSpace A q := by
  classical
  intro ht
  have c0 : nodes A o = 0 := by simp [nodes,Matrix.mulVec,dotProduct,hr]
  have nt : o ≠ t := by
    rintro rfl
    exact zero_ne_one (c0.symm.trans one)
  have e0 : coordinate (K:=K) t o = 0 := by simp [coordinate,nt]
  rw [treeSpace_coeff_sup ho (by omega)] at ht
  obtain ⟨v,hv,f,hf,e⟩ := Submodule.mem_sup.mp ht
  obtain ⟨a,rfl⟩ := hv
  have a0 : a 0 = 0 := by
    have h := congrFun e o
    have f0 : f o = 0 := zeroSpace_at_zero_row hr q hf
    rwa [Pi.add_apply,coeffEval_at_zero_row hr,f0,add_zero,e0] at h
  have test (i : Fin (q+1)) :
      (∑ j : Fin q, a j.succ/((i.val+j.val+2:ℕ):K)) = b t := by
    have h := congrArg (probe A b i.val) e
    have f0 : probe A b i.val f = 0 := probe_zeroSpace ho (by have := i.isLt; omega) hf
    have ct : probe A b i.val (coordinate t) = b t := by
      change row _ (coordinate t) = b t
      rw [row_coordinate,one,one_pow,mul_one]
    rw [map_add,f0,add_zero,probe_coeffEval ho (by have := i.isLt; omega),
      Fin.sum_univ_succ,a0,zero_div,zero_add,ct] at h
    simpa only [Fin.val_succ,Nat.add_assoc] using h
  exact live (paid_constant_cauchy ho pay (fun j : Fin q => a j.succ) _ test).2

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The exact unmarked reverse room at any paid cutoff, from level one.
This keeps the *actual* initial reverse rank rather than counting it twice. -/
theorem dirk_reverse_rank_budget (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q n : ℕ} (hn : 1 ≤ n) (pay : q+n+2 ≤ p) :
    finrank K (treeSpace A q) + (n-1) + finrank K (primitiveBack A b 1) ≤ s := by
  have grow := dirk_primitiveBack_rank_gain ha ho (r:=1) (by decide) hn (by omega)
  have inc := Submodule.finrank_mono (primitiveBack_annih ho q n pay)
  have cap := finrank_annih (treeSpace A q)
  rw [Fintype.card_fin] at cap
  omega

/-- Once the physical origin and the first two backward seeds vanish,
the last live coordinate cannot be spent on any of the counted dimensions. -/
theorem dirk_terminal_rank_budget (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q n : ℕ} {o : Fin s} (hn : 1 ≤ n) (pay : q+n+2 ≤ p) (mid : 2*q+1 ≤ p)
    (hr : ∀ j, A o j = 0) (h₁ : reflectedStageRow A b 0 = 0)
    (h₂ : reflectedStageRow A b 1 = 0) :
    finrank K (treeSpace A q) + n ≤ s := by
  obtain ⟨t,L⟩ := exists_lastActive ho (by omega)
  have node : nodes A t = 1 := (sub_eq_zero.mp (L.dirk_reflected_zero ha h₁ h₂)).symm
  have outside := endpoint_coordinate_out_of_zero_row ho mid hr L.live node
  have cut : primitiveBack A b n ≤ zeroAt (annih (treeSpace A q)) t := by
    intro v hv
    exact mem_zeroAt.mpr ⟨primitiveBack_annih ho q n pay hv,
      mem_tailZero.mp (L.dirk_primitiveBack_tail ha h₁ h₂ n hv) t le_rfl⟩
  have inc := Submodule.finrank_mono cut
  have codim := finrank_zeroAt_annih (treeSpace A q) t outside
  have cap := finrank_annih (treeSpace A q)
  rw [Fintype.card_fin] at cap
  have grow := dirk_primitiveBack_rank_gain ha ho (r:=1) (by decide) hn (by omega)
  omega

/-- Two-ended physical count, with the one boundary refund paid by C(2),
one of the first two backward rows, or the last live coordinate itself. -/
theorem dirk_two_ended_stage_count (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) (pay : q+n+2 ≤ p) (mid : 2*q+1 ≤ p) :
    2*q+n-1 ≤ s := by
  have fr := dirk_forward_zeroSpace_rank_floor ha ho hq (by omega)
  have tr := treeSpace_rank_eq_of_separation ho (q:=q) (by omega) (coeff_separated ho mid)
  have raw := dirk_reverse_rank_budget ha ho hn pay
  by_cases fc : monomialStageDefect A 1 = 0
  · by_cases rb : finrank K (primitiveBack A b 1) = 0
    · obtain ⟨h₁,h₂⟩ := dirk_primitiveBack_one_zero rb
      cases s with
      | zero =>
        obtain ⟨t,_⟩ := exists_lastActive ho (by omega)
        exact Fin.elim0 t
      | succ s =>
        have hr := dirk_first_row_of_zero_quadratic ha
          (show monomialStageDefect A 1 0 = 0 from congrFun fc 0)
        have terminal := dirk_terminal_rank_budget ha ho hn pay mid hr h₁ h₂
        omega
    · omega
  · have extra := fr.2 fc
    omega

end RKResearch.Certified.Graded.Reverse

namespace RKResearch

/-- Native uniform DIRK floor over every field. -/
theorem HasOrder.dirk_uniform_stages_field {K : Type*} [Field K] {p s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b p) (ha : A.IsLowerTriangular) (hp : 6 ≤ p) :
    p+(p-1)/2-3 ≤ s := by
  have count := Certified.Graded.Reverse.dirk_two_ended_stage_count ha h
    (q:=(p-1)/2) (n:=p-(p-1)/2-2) (by omega) (by omega) (by omega) (by omega)
  omega

/-- Over every nontrivial commutative ring, a lower triangular tableau
satisfying the human rooted-tree conditions needs at least
p + ⌊(p−1)/2⌋ − 3 original stages at order p ≥ 6. -/
theorem HasOrder.dirk_uniform_stages {R : Type*} [CommRing R] [Nontrivial R] {p s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b p) (ha : A.IsLowerTriangular) (hp : 6 ≤ p) :
    p+(p-1)/2-3 ≤ s :=
  h.lower_triangular_of_all_fields ha
    (fun _ _ _ _ ht h' => h'.dirk_uniform_stages_field ht hp)

theorem HasOrder.dirk_order_seven_stages {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b 7) (ha : A.IsLowerTriangular) : 7 ≤ s :=
  h.dirk_uniform_stages ha (by decide)

theorem HasOrder.dirk_order_eight_stages {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b 8) (ha : A.IsLowerTriangular) : 8 ≤ s :=
  h.dirk_uniform_stages ha (by decide)

/-- The uniform lower-bound ledger, including small orders before the
two-ended argument starts. Its values are necessary stages, not constructions. -/
def dirkUniformFloor : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | k+6 => (k+6)+(k+5)/2-3

/-- All orders, including the complete arbitrary-ring DIRK column from
orders one through twenty, using only the native tableau predicate. -/
theorem HasOrder.dirk_uniform_floor_le_stages {R : Type*} [CommRing R] [Nontrivial R]
    {p s : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b p) (ha : A.IsLowerTriangular) : dirkUniformFloor p ≤ s := by
  have positive {k : ℕ} (hk : 1 ≤ k) (g : HasOrder A b k) : 1 ≤ s :=
    g.lower_triangular_of_all_fields ha (fun _ _ _ _ _ g' => by
      obtain ⟨t,_⟩ := Certified.Graded.Reverse.exists_lastActive g' hk
      have := t.isLt
      omega)
  rcases p with _|p
  · exact Nat.zero_le _
  rcases p with _|p
  · exact positive (by decide) h
  rcases p with _|p
  · exact positive (by decide) h
  rcases p with _|p
  · exact h.lower_triangular_of_all_fields ha (fun _ _ _ _ _ h' => h'.order_three_stages_field)
  rcases p with _|p
  · exact h.dirk_order_four_stages ha
  rcases p with _|p
  · exact h.dirk_order_five_stages ha
  exact h.dirk_uniform_stages ha (by omega)

/-- Regression on the published arbitrary-ring DIRK column, with order
zero prepended. Larger characteristic-zero refinements are separate. -/
theorem dirkUniformFloor_through_twenty : (List.range 21).map dirkUniformFloor =
    [0,1,1,2,3,4,5,7,8,10,11,13,14,16,17,19,20,22,23,25,26] := by decide

end RKResearch
