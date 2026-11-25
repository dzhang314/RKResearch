module

public import RKCert.ReviewedNative.TopologicalLastLive

@[expose] public section

/-! # The minimum attainable last-live index

With a starting topological rank, a set is an exact strict prefix of a
marked vertex precisely when it is a predecessor-closed cut that
excludes the mark and contains its immediate predecessors. For a
nonempty live set, the minimum last-live index is one less than the
size of its reflexive predecessor closure. No tableau data are used.
-/
namespace RKResearch.Certified.Topological

/-- The exact strict prefixes at a marked vertex are the predecessor
ideals omitting it and containing all its immediate predecessors. -/
theorem exists_rank_exact_prefix_iff {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (old : V ≃ Fin n) (hold : RespectsEdges R old)
    (t : V) (E : Finset V) :
    (∃ σ : V ≃ Fin n, RespectsEdges R σ ∧ ∀ u, σ u < σ t ↔ u ∈ E) ↔
      t ∉ E ∧ (∀ ⦃a b⦄, R a b → b ∈ E → a ∈ E) ∧
        ∀ ⦃a⦄, R a t → a ∈ E := by
  classical
  constructor
  · intro h
    rcases h with ⟨σ, hσ, hcut⟩
    refine ⟨fun ht => (lt_irrefl (σ t)) ((hcut t).mpr ht), ?_, ?_⟩
    · intro a b e hb
      exact (hcut a).mp (lt_trans (hσ e) ((hcut b).mpr hb))
    · intro a e
      exact (hcut a).mp (hσ e)
  · intro h
    rcases h with ⟨outside, back, before⟩
    let S : V → V → Prop := fun a b => R b a ∨ (a = t ∧ b ∈ E)
    let tier : V → ℕ := fun u => if u ∈ E then 1 else 0
    let keyFn : V → Lex (ℕ × Fin n) := fun u => toLex (tier u, (old u).rev)
    have key_inj : Function.Injective keyFn := by
      intro u v e
      have hs := congrArg (fun z : Lex (ℕ × Fin n) => (ofLex z).2) e
      change (old u).rev = (old v).rev at hs
      exact old.injective (Fin.rev_injective hs)
    let key : V ↪ Lex (ℕ × Fin n) := ⟨keyFn, key_inj⟩
    have hkey : RespectsEdges S key := by
      intro a b e
      change R b a ∨ (a = t ∧ b ∈ E) at e
      change toLex (tier a, (old a).rev) < toLex (tier b, (old b).rev)
      rcases e with e | ⟨hat, hb⟩
      · apply Prod.Lex.toLex_lt_toLex'.mpr
        refine ⟨?_, fun _ => Fin.rev_lt_rev.mpr (hold e)⟩
        by_cases ha : a ∈ E
        · have hb : b ∈ E := back e ha
          simp only [tier, ite_eq_left ha, ite_eq_left hb, le_refl]
        · simp only [tier, ite_eq_right ha, Nat.zero_le]
      · subst a
        apply Prod.Lex.toLex_lt_toLex.mpr
        left
        calc
          tier t = 0 := ite_eq_right outside
          _ < 1 := Nat.zero_lt_succ 0
          _ = tier b := (ite_eq_left hb).symm
    have start {u : V} (h : S t u) : u ∈ E := by
      change R u t ∨ (t = t ∧ u ∈ E) at h
      exact h.elim (fun e => before e) (fun e => e.2)
    have stay {a b : V} (ha : a ∈ E) (h : S a b) : b ∈ E := by
      change R b a ∨ (a = t ∧ b ∈ E) at h
      exact h.elim (fun e => back e ha) (fun e => e.2)
    have reach (u : V) : Relation.TransGen S t u ↔ u ∈ E := by
      constructor
      · intro p
        induction p with
        | single e => exact start e
        | tail _ e ih => exact stay ih e
      · intro hu
        have e : S t u := Or.inr ⟨rfl, hu⟩
        exact Relation.TransGen.single e
    have hcard : Fintype.card V = n := (Fintype.card_congr old).trans (Fintype.card_fin n)
    obtain ⟨ρ, hρ, hs⟩ := exists_rank_exact_strict_suffix hcard S key hkey t
    let σ : V ≃ Fin n := ρ.trans Fin.revPerm
    refine ⟨σ, ?_, ?_⟩
    · intro a b e
      change (ρ a).rev < (ρ b).rev
      exact Fin.rev_lt_rev.mpr (hρ (Or.inl e : S b a))
    · intro u
      change (ρ u).rev < (ρ t).rev ↔ u ∈ E
      exact Fin.rev_lt_rev.trans ((hs u).trans (reach u))

/-- A stage is in the live predecessor closure if some possibly empty
path connects it to a live stage. -/
noncomputable def liveAncestors {V : Type*} [Fintype V]
    (R : V → V → Prop) (live : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => ∃ v, live v ∧ Relation.ReflTransGen R u v)

private theorem mem_liveAncestors {V : Type*} [Fintype V]
    (R : V → V → Prop) (live : V → Prop) (u : V) :
    u ∈ liveAncestors R live ↔ ∃ v, live v ∧ Relation.ReflTransGen R u v := by
  classical
  simp only [liveAncestors, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem live_mem_ancestors {V : Type*} [Fintype V]
    (R : V → V → Prop) (live : V → Prop) {u : V} (hu : live u) :
    u ∈ liveAncestors R live :=
  (mem_liveAncestors R live u).mpr ⟨u, hu, Relation.ReflTransGen.refl⟩

private theorem liveAncestors_back {V : Type*} [Fintype V]
    (R : V → V → Prop) (live : V → Prop) {a b : V} (e : R a b)
    (hb : b ∈ liveAncestors R live) : a ∈ liveAncestors R live := by
  rcases (mem_liveAncestors R live b).mp hb with ⟨v, hv, hp⟩
  exact (mem_liveAncestors R live a).mpr ⟨v, hv, Relation.ReflTransGen.head e hp⟩

private theorem rank_le_of_path {V : Type*} {n : ℕ} {R : V → V → Prop}
    {σ : V ≃ Fin n} (hσ : RespectsEdges R σ) {a b : V}
    (p : Relation.ReflTransGen R a b) : σ a ≤ σ b := by
  induction p with
  | refl => exact le_rfl
  | tail _ e ih => exact le_trans ih (hσ e).le

private theorem ancestors_rank_le_last {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (live : V → Prop) {σ : V ≃ Fin n}
    (hσ : RespectsEdges R σ) {t : V} (after : ∀ u, σ t < σ u → ¬ live u)
    {a : V} (ha : a ∈ liveAncestors R live) : σ a ≤ σ t := by
  rcases (mem_liveAncestors R live a).mp ha with ⟨u, hu, p⟩
  exact le_trans (rank_le_of_path (σ := σ) hσ p) (le_of_not_gt (fun h => after u h hu))

private def rankPrefix {V : Type*} {n m : ℕ} (σ : V ≃ Fin n) (hm : m ≤ n) : Finset V :=
  (Finset.univ : Finset (Fin m)).map ((Fin.castLEEmb hm).trans σ.symm.toEmbedding)

private theorem mem_rankPrefix {V : Type*} {n m : ℕ} (σ : V ≃ Fin n)
    (hm : m ≤ n) (u : V) : u ∈ rankPrefix σ hm ↔ (σ u).val < m := by
  rw [rankPrefix, Finset.mem_map]
  constructor
  · intro h
    rcases h with ⟨i, _, hi⟩
    change σ.symm (Fin.castLE hm i) = u at hi
    have e : Fin.castLE hm i = σ u :=
      (σ.apply_symm_apply (Fin.castLE hm i)).symm.trans (congrArg σ hi)
    calc
      (σ u).val = (Fin.castLE hm i).val := congrArg Fin.val e.symm
      _ < m := i.isLt
  · intro h
    let i : Fin m := ⟨(σ u).val, h⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change σ.symm (Fin.castLE hm i) = u
    exact σ.injective ((σ.apply_symm_apply _).trans (Fin.ext rfl))

private theorem card_rankPrefix {V : Type*} {n m : ℕ} (σ : V ≃ Fin n)
    (hm : m ≤ n) : (rankPrefix σ hm).card = m := by
  simp only [rankPrefix, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem card_eq_rank_of_exact_prefix {V : Type*} {n : ℕ}
    (σ : V ≃ Fin n) (t : V) (E : Finset V) (hcut : ∀ u, σ u < σ t ↔ u ∈ E) :
    E.card = (σ t).val := by
  have cap : (σ t).val ≤ n := (σ t).isLt.le
  have hset : E = rankPrefix σ cap := by
    ext u
    exact (hcut u).symm.trans (mem_rankPrefix σ cap u).symm
  exact (congrArg Finset.card hset).trans (card_rankPrefix σ cap)

private theorem last_live_index_lower {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (live : V → Prop) (σ : V ≃ Fin n)
    (hσ : RespectsEdges R σ) (t : V) (ht : live t)
    (after : ∀ u, σ t < σ u → ¬ live u) :
    (liveAncestors R live).card - 1 ≤ (σ t).val := by
  classical
  let D := liveAncestors R live
  have htD : t ∈ D := live_mem_ancestors R live ht
  have cap : (σ t).val ≤ n := (σ t).isLt.le
  have hsub : D.erase t ⊆ rankPrefix σ cap := by
    intro u hu
    rcases Finset.mem_erase.mp hu with ⟨hne, hD⟩
    have hle := ancestors_rank_le_last R live (σ := σ) hσ (t := t) after hD
    have hlt : σ u < σ t := lt_of_le_of_ne hle (fun e => hne (σ.injective e))
    exact (mem_rankPrefix σ cap u).mpr hlt
  calc
    (liveAncestors R live).card - 1 = (D.erase t).card :=
      (Finset.card_erase_of_mem htD).symm
    _ ≤ (rankPrefix σ cap).card := Finset.card_le_card hsub
    _ = (σ t).val := card_rankPrefix σ cap

/-- For nonempty support the least possible zero-based last-live index
is the size of its full predecessor closure minus one. -/
theorem isLeast_last_live_index {V : Type*} [Fintype V] {n : ℕ}
    (R : V → V → Prop) (live : V → Prop) (old : V ≃ Fin n)
    (hold : RespectsEdges R old) (hne : ∃ t, live t) :
    IsLeast {k : ℕ | ∃ (σ : V ≃ Fin n) (t : V), RespectsEdges R σ ∧ live t ∧
      (∀ u, σ t < σ u → ¬ live u) ∧ (σ t).val = k}
      ((liveAncestors R live).card - 1) := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter (fun i => live (old.symm i))
  have memP (i : Fin n) : i ∈ P ↔ live (old.symm i) := by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
  have hP : P.Nonempty := by
    rcases hne with ⟨v, hv⟩
    exact ⟨old v, (memP (old v)).mpr (by simpa only [Equiv.symm_apply_apply] using hv)⟩
  let p : Fin n := P.max' hP
  let t : V := old.symm p
  have ht : live t := (memP p).mp (P.max'_mem hP)
  have old_last : ∀ u, old t < old u → ¬ live u := by
    intro u hlt hu
    have hm : old u ∈ P :=
      (memP (old u)).mpr (by simpa only [Equiv.symm_apply_apply] using hu)
    have hl : old u ≤ p := P.le_max' (old u) hm
    have hr : p < old u := by simpa only [t, Equiv.apply_symm_apply] using hlt
    exact not_lt_of_ge hl hr
  let D := liveAncestors R live
  let E := D.erase t
  have htD : t ∈ D := live_mem_ancestors R live ht
  have memE (u : V) : u ∈ E ↔ u ≠ t ∧ u ∈ D := Finset.mem_erase
  have outside : t ∉ E := fun h => ((memE t).mp h).1 rfl
  have back : ∀ ⦃a b⦄, R a b → b ∈ E → a ∈ E := by
    intro a b e hb
    have hbD : b ∈ D := ((memE b).mp hb).2
    have haD : a ∈ D := liveAncestors_back R live e hbD
    have hlt : old a < old t :=
      lt_of_lt_of_le (hold e) (ancestors_rank_le_last R live (σ := old) hold (t := t) old_last hbD)
    exact (memE a).mpr ⟨fun z => (ne_of_lt hlt) (congrArg old z), haD⟩
  have before : ∀ ⦃a⦄, R a t → a ∈ E := by
    intro a e
    exact (memE a).mpr
      ⟨fun z => (ne_of_lt (hold e)) (congrArg old z), liveAncestors_back R live e htD⟩
  obtain ⟨σ, hσ, hcut⟩ :=
    (exists_rank_exact_prefix_iff R old hold t E).mpr ⟨outside, back, before⟩
  have after : ∀ u, σ t < σ u → ¬ live u := by
    intro u hlt hu
    have hne : u ≠ t := fun z => (ne_of_lt hlt) (congrArg σ z.symm)
    have huD : u ∈ D := live_mem_ancestors R live hu
    exact lt_asymm hlt ((hcut u).mpr ((memE u).mpr ⟨hne, huD⟩))
  have hindex : (σ t).val = D.card - 1 :=
    (card_eq_rank_of_exact_prefix σ t E hcut).symm.trans (Finset.card_erase_of_mem htD)
  refine ⟨⟨σ, t, hσ, ht, after, hindex⟩, ?_⟩
  intro k hk
  rcases hk with ⟨ρ, u, hρ, hu, hafter, hval⟩
  calc
    (liveAncestors R live).card - 1 ≤ (ρ u).val :=
      last_live_index_lower R live ρ hρ u hu hafter
    _ = k := hval

end RKResearch.Certified.Topological
