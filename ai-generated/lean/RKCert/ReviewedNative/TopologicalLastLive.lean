module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

/-! # Reachability and possible last live vertices

For a finite directed relation with an existing increasing edge rank, an
exact suffix can be arranged around any marked vertex. Its strict
descendants, and only those descendants, follow the vertex in the new
topological rank. The consequence for a live subset uses reachability in
the whole relation, not in the restriction to the live vertices.
-/
namespace RKResearch.Certified.Topological

/-- An edge is directed from its earlier endpoint to its later endpoint. -/
def RespectsEdges {V B : Type*} [LT B] (R : V → V → Prop) (f : V → B) : Prop :=
  ∀ ⦃u v⦄, R u v → f u < f v

private theorem strict_of_path {V B : Type*} [Preorder B] {R : V → V → Prop}
    {f : V → B} (h : RespectsEdges R f) {u v : V} (p : Relation.TransGen R u v) :
    f u < f v := by
  let : IsTrans V (fun a b => f a < f b) :=
    ⟨fun _ _ _ hab hbc => lt_trans hab hbc⟩
  exact Relation.transGen_minimal (r := R) (r' := fun a b => f a < f b)
    (fun _ _ e => h e) u v p

private theorem exists_rank_of_injective_key {V B : Type*} [Fintype V] [LinearOrder B]
    {n : ℕ} (hcard : Fintype.card V = n) (key : V → B) (hkey : Function.Injective key) :
    ∃ σ : V ≃ Fin n, ∀ u v, σ u < σ v ↔ key u < key v := by
  classical
  let e : V ≃ Set.range key := Equiv.ofInjective key hkey
  let : Fintype (Set.range key) := Fintype.ofEquiv V e
  let sorted : Fin n ≃o Set.range key :=
    Fintype.orderIsoFinOfCardEq (Set.range key) ((Fintype.card_congr e.symm).trans hcard)
  refine ⟨e.trans sorted.symm.toEquiv, ?_⟩
  intro u v
  change sorted.symm (e u) < sorted.symm (e v) ↔ e u < e v
  exact sorted.symm.lt_iff_lt

/-- There is a topological rank in which the strict suffix of the marked
vertex is exactly its nonempty-path descendants. The sorting key is the
old rank within each of three tiers: ordinary nondescendants, the marked
vertex, and strict descendants. -/
theorem exists_rank_exact_strict_suffix {V B : Type*} [Fintype V] [LinearOrder B]
    {n : ℕ} (hcard : Fintype.card V = n) (R : V → V → Prop)
    (old : V ↪ B) (hold : RespectsEdges R old) (t : V) :
    ∃ σ : V ≃ Fin n, RespectsEdges R σ ∧
      ∀ u, σ t < σ u ↔ Relation.TransGen R t u := by
  classical
  have no_self : ¬ Relation.TransGen R t t :=
    fun h => (lt_irrefl (old t)) (strict_of_path hold h)
  let tier : V → ℕ :=
    fun u => if Relation.TransGen R t u then 2 else if u = t then 1 else 0
  have tier_marked : tier t = 1 := by simp [tier, no_self]
  have tier_high {u : V} (hu : Relation.TransGen R t u) : tier u = 2 := by
    simp only [tier, ite_eq_left hu]
  have tier_low {u : V} (hu : ¬ Relation.TransGen R t u) (hne : u ≠ t) : tier u = 0 := by
    simp only [tier, ite_eq_right hu, ite_eq_right hne]
  have tier_mono {u v : V} (h : R u v) : tier u ≤ tier v := by
    by_cases hu : Relation.TransGen R t u
    · rw [tier_high hu, tier_high (hu.tail h)]
    · by_cases he : u = t
      · subst u
        rw [tier_marked, tier_high (Relation.TransGen.single h)]
        decide
      · rw [tier_low hu he]
        exact Nat.zero_le _
  let key : V → Lex (ℕ × B) := fun u => toLex (tier u, old u)
  have key_inj : Function.Injective key := by
    intro u v h
    have h' := congrArg (fun z : Lex (ℕ × B) => (ofLex z).2) h
    change old u = old v at h'
    exact old.injective h'
  have key_edge : RespectsEdges R key := by
    intro u v h
    change toLex (tier u, old u) < toLex (tier v, old v)
    exact Prod.Lex.toLex_lt_toLex'.mpr ⟨tier_mono h, fun _ => hold h⟩
  have key_of_tier_lt {u v : V} (h : tier u < tier v) : key u < key v := by
    change toLex (tier u, old u) < toLex (tier v, old v)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  obtain ⟨σ, hσ⟩ := exists_rank_of_injective_key hcard key key_inj
  refine ⟨σ, ?_, ?_⟩
  · intro u v h
    exact (hσ u v).mpr (key_edge h)
  · intro u
    constructor
    · intro hu
      by_contra hn
      have hne : u ≠ t := by
        intro he
        subst u
        exact (lt_irrefl (σ t)) hu
      have hb : tier u < tier t := by
        rw [tier_low hn hne, tier_marked]
        decide
      exact (lt_asymm ((hσ t u).mp hu)) (key_of_tier_lt hb)
    · intro hu
      have hb : tier t < tier u := by
        rw [tier_marked, tier_high hu]
        decide
      exact (hσ t u).mpr (key_of_tier_lt hb)

/-- Given that topological ranks exist, precisely the live vertices with
no strict live descendant can be last live. The existence conjunct on
the right also makes the statement valid for relations without a
topological rank of the indicated size. -/
theorem exists_last_live_rank_iff {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (live : V → Prop) (t : V) :
    (∃ σ : V ≃ Fin n, RespectsEdges R σ ∧ live t ∧
      ∀ u, σ t < σ u → ¬ live u) ↔
    (∃ σ : V ≃ Fin n, RespectsEdges R σ) ∧ live t ∧
      ∀ u, Relation.TransGen R t u → ¬ live u := by
  constructor
  · intro h
    rcases h with ⟨σ, hσ, ht, hafter⟩
    exact ⟨⟨σ, hσ⟩, ht, fun u hu => hafter u (strict_of_path hσ hu)⟩
  · intro h
    rcases h with ⟨⟨old, hold⟩, ht, hdesc⟩
    have hcard : Fintype.card V = n :=
      (Fintype.card_congr old).trans (Fintype.card_fin n)
    obtain ⟨σ, hσ, hsuffix⟩ :=
      exists_rank_exact_strict_suffix hcard R old.toEmbedding hold t
    exact ⟨σ, hσ, ht, fun u hu => hdesc u ((hsuffix u).mp hu)⟩

end RKResearch.Certified.Topological
