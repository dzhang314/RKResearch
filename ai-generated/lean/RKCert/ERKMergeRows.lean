module

public import RKCert.ERKLowBase

@[expose] public section

/-! # A genuine merge of two identical explicit incoming rows

An equality of a few stage features is not sufficient here: the entire
physical rows must be identical. All rooted-tree order conditions survive
the canonical retained-stage construction, including the output terms.
-/
namespace RKCert.Paired

variable {K : Type*} [Field K] {n p : ℕ}

def mergeCoefficient (j : Fin (n+1)) (r : Fin n) (w : Vec K (n+1)) : Vec K n :=
  fun k => w (j.succAbove k) + if k=r then w j else 0

theorem sum_merge_coefficient (j : Fin (n+1)) (r : Fin n)
    (w v : Vec K (n+1)) (hv : v j=v (j.succAbove r)) :
    (∑ k : Fin n, mergeCoefficient j r w k * v (j.succAbove k)) = ∑ k, w k * v k := by
  simp only [mergeCoefficient,add_mul,Finset.sum_add_distrib]
  rw [Fin.sum_univ_succAbove _ j,add_comm]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp [hv]
  · intro k _ hk; simp [hk]
  · simp

theorem stageWeight_equal_rows {A : Fin n → Fin n → K} {i j : Fin n}
    (he : ∀ k, A i k=A j k) (t : Tree) :
    stageWeight A t i=stageWeight A t j := by
  induction t with
  | leaf => rfl
  | attach t u _ ihu => simp only [stageWeight,he,ihu]

/-- Expand a literal identically evaluated pair into one retained coordinate,
replacing all outgoing taps and the output coefficient by their sums. -/
theorem exists_merge_equal_rows {A : Fin (n+1) → Fin (n+1) → K} {b : Vec K (n+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {i j : Fin (n+1)}
    (hij : i < j) (he : ∀ k, A i k=A j k) :
    ∃ (B : Fin n → Fin n → K) (c : Vec K n), StrictLower B ∧ HasTreeOrderAtLeast B c p := by
  obtain ⟨r,hr⟩ := Fin.exists_succAbove_eq (ne_of_lt hij)
  let B (a : Fin n) : Vec K n := mergeCoefficient j r (A (j.succAbove a))
  have hB : StrictLower B := by
    intro x y hxy
    have h := (Fin.succAboveOrderEmb j).monotone hxy
    change j.succAbove x  ≤  j.succAbove y at h
    by_cases hh : y=r
    · subst y
      have hi' : j.succAbove x  ≤  i := hr ▸ h
      simp [B,mergeCoefficient,ha _ _ h,ha _ _ (hi'.trans hij.le)]
    · simp [B,mergeCoefficient,ha _ _ h,hh]
  have hw (t : Tree) (k : Fin n) : stageWeight B t k = stageWeight A t (j.succAbove k) := by
    induction t generalizing k with
    | leaf => rfl
    | attach t u iht ihu =>
      simp only [stageWeight,iht,ihu]
      congr 1
      exact sum_merge_coefficient j r (A (j.succAbove k)) (stageWeight A t)
        (by rw [hr]; exact (stageWeight_equal_rows he t).symm)
  refine ⟨B,mergeCoefficient j r b,hB,?_⟩
  intro t ht
  have hW : weight B (mergeCoefficient j r b) t = weight A b t := by
    simp only [weight,hw]
    exact sum_merge_coefficient j r b (stageWeight A t) (by rw [hr]; exact (stageWeight_equal_rows he t).symm)
  rw [hW]
  exact ho t ht

theorem no_identical_rows_at_uniform_floor {A : Fin (n+1) → Fin (n+1) → K} {b : Vec K (n+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hn : max p ((3*p+1)/2-2)=n+1)
    {i j : Fin (n+1)} (hij : i < j) :
    ¬ ∀ k, A i k=A j k := by
  intro he
  obtain ⟨B,c,hB,hc⟩ := exists_merge_equal_rows ha ho hij he
  have h := uniform_erk_field hB hc
  omega

end RKCert.Paired
